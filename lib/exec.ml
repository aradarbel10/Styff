open Lexer
open Typecheck.Typer
open Typecheck.Pretty
open Typecheck.Eval
open Typecheck.Scene
open Typecheck.Errors
module Pattern = Typecheck.Pattern
module Unif = Typecheck.Unif

open Syntax.Common
module R = Syntax.Raw
module C = Syntax.Core
module Z = Syntax.Zonked

open Backend.Zonk
open Backend.Js

type options = {
  elab_diagnostics : bool;
  dump_output : bool;
}

(*
elaborate given stmt under given scene, with [scp] to accumulate the qualified scope.
returns:
- scene bound with new unqualified names
- scope accumulator (not entire scene) updated with qualified names,
  could later be plugged into above scene to get qualified context.
- elaborated version of the statement (might produce a list of statements in result)
*)
let rec elab_stmt (opts : options) (scn : scene) (stmt : R.stmt) : scene * C.prog =
  match stmt with
  | Def (rc, x, ps, t, e) ->
    (* elaborate the definition itself *)
    let full_scn, _, bod, typ = infer_let scn rc x ps t e in
    let x = qualify full_scn x in

    let bod_scn = if rc then full_scn else scn in
    let bod = norm_expr bod_scn.env bod in

    (* print those *)
    if opts.elab_diagnostics then
      print_endline ("let " ^ string_of_name x ^ "\n\t : " ^
        string_of_vtype bod_scn.scope typ ^ "\n\t = " ^
        string_of_expr bod_scn.scope bod);

    (* zonk everything
    let ztyp = zonk_type bod_scn.scope (quote bod_scn.height typ) in
    let zbod = zonk_expr bod_scn.scope bod in *)
    let typ = quote bod_scn.height typ in

    let stmt = C.Def (rc, x, typ, bod) in
                (* todo: consider refactoring with something like [scn.scope.head] *)
    full_scn, [stmt]

  | TDef (x, k, t) ->
    let scn', t, _, k = infer_let_type scn x k t in
    let x = qualify scn' x in

    if opts.elab_diagnostics then
      print_endline ("type " ^ string_of_name x ^ "\n\t : " ^
        string_of_kind k ^ "\n\t = " ^
        string_of_type scn.scope t);

    scn', [TDef (x, k, t)]

  | Infer (x, e) ->
    let (_, te) = infer scn e in
    if opts.elab_diagnostics then
      print_endline ("infer " ^ x ^ "\n\t : " ^
        string_of_vtype scn.scope te);
    scn, []

  | TInfer (x, t) ->
    let (_, kt) = kind_of scn t in
    if opts.elab_diagnostics then
      print_endline ("infer type " ^ x ^ "\n\t : " ^
        string_of_kind kt);
    scn, []

  | Print e ->
    let (e, _) = infer scn e in
    let e = norm_expr scn.env e in
    scn, [C.Print e]

  | Postulate (x, t) ->
    let (t, _) = kind_of scn t in
    let vt = eval scn.env t in
    assume x vt scn, [Postulate (qualify scn x, t)]

  | PostulateType (x, k) ->
    let k = lower_kind k in
    assume_typ x k `ESolved scn, [PostulateType (qualify scn x, k)]

  | DataDecl (x, k, ctors) ->
    let scn, k, ctors = declare_data scn x k ctors in
    if opts.elab_diagnostics then
      print_endline ("declared data " ^ x);

    scn, [DataDecl (qualify scn x, k, List.map (qualify scn) ctors)]

  | Section (sect, stmts) ->
    (* enter section *)
    let scn = {scn with scope = Scope.enter scn.scope sect} in

    (* elaborate contents *)
    let go_stmt (acc_scn, acc_prog : scene * C.prog) (stmt : R.stmt) =
      let acc_scn', acc_prog' = elab_stmt opts acc_scn stmt in
      acc_scn', acc_prog @ acc_prog'
    in
    let scn, stmts' = List.fold_left go_stmt (scn, []) stmts in

    (* re-qualify scn *)
    let scn = {scn with scope = Scope.exit scn.scope} in

    scn, stmts'

  | OpenSection sect ->
    {scn with scope = Scope.open_section scn.scope sect}, []

  | Alias (new_nm, old_nm) ->
    {scn with scope = {scn.scope with nms = Sectioned.alias scn.scope.nms new_nm old_nm}}, []

let builtins_prog : R.prog = [
  Section ("builtin", [
    PostulateType ("int", RStar);
    Postulate ("int-add", RArrow (RBase `Int, RArrow (RBase `Int, RBase `Int)));
    Postulate ("int-mul", RArrow (RBase `Int, RArrow (RBase `Int, RBase `Int)));
    
    PostulateType ("bool", RStar);
    Postulate ("bool-true", RBase `Bool);
    Postulate ("bool-false", RBase `Bool);
  ])
]

let elab_prog (opts : options) (prog : R.prog) : C.prog =
  let go_stmt (acc_scn, acc_prog : scene * C.prog) (stmt : R.stmt) =
    let acc_scn', acc_prog' = elab_stmt opts acc_scn stmt in
    acc_scn', acc_prog @ acc_prog'
  in
  let preambled = builtins_prog @ prog in
  let _, stmts' = List.fold_left go_stmt (empty_scene, []) preambled in
  stmts'

let zonk_name (nm : name) : string = String.concat "_" (sanitize nm)
let zonk_ctor (scp : zonk_scope) (ctor : name) : zonk_scope
  = {scp with nms = string_of_name ctor :: scp.nms}
let zonk_stmt (scp : zonk_scope) : C.stmt -> zonk_scope * Z.prog = function
| Def (rc, x, t, e) ->
  let x = zonk_name x in
  let full_scp = {scp with nms = x :: scp.nms} in
  let bod_scp = if rc then full_scp else scp in
  full_scp, [Def (x, zonk_type bod_scp t, zonk_expr bod_scp e)]
| TDef (x, _, _) -> {scp with tps = zonk_name x :: scp.tps}, []
| Print e -> scp, [Print (zonk_expr scp e)]
| Postulate (x, _) -> {scp with nms = zonk_name x :: scp.nms}, []
| PostulateType (x, _) -> {scp with tps = zonk_name x :: scp.tps}, []
| DataDecl (x, _, ctors) ->
  let scp = {scp with tps = zonk_name x :: scp.tps} in
  let scp = List.fold_left zonk_ctor scp ctors in
  scp, []
let zonk_prog (prog : C.prog) : Z.prog = snd @@ List.fold_left (fun (scp, p) stmt ->
  let (scp', p') = zonk_stmt scp stmt in scp', p @ p') ({nms=[]; tps=[]}, []) prog

exception CompileFailure of string
let compile_prog (mode : [`file | `str]) (opts : options) (input : string) : string =
  let throw err = raise (CompileFailure err) in
  try
    let js = input
      |> (match mode with | `file -> parse_file | `str -> parse_str)
      |> elab_prog opts
      |> zonk_prog
      |> beta_fold_prog
      |> js_of_zonked
      |> string_of_js
    in if opts.dump_output then begin
      print_string "\n\n\nOUTPUT JS:\n==========\n";
      print_endline js;
    end;
    js
  with
  | ParseFailure err -> throw (show_parse_err err)
  | EvalFailure err -> throw (show_eval_err err)
  | ElabFailure err -> throw (show_elab_err err)

  | UnsolvedKVar -> throw "ambiguous kind variable"
  | UnsolvedTVar x -> throw ("ambiguous type variable " ^ x)

  | BadCtorReturn -> throw "constructor's type must return the type it's defined in"

  | Unif.NonVarInSpine -> throw "unification problem too hard (spine contains non-variables)"
  | Unif.NonLinearSpine -> throw "unification problem too hard (spine is non-linear)"
  | Unif.OccursError -> throw "recursive types not supported"
  | Unif.IllScopedSpine -> throw "(internal) ill-scoped spine"
  | Unif.Ununifiable -> throw "unequal types"
  | Unif.UnunifiableLocals -> throw "unequal GADT indices"
  | Unif.DifferentSpineLength -> throw "rigid types cannot be equal when applied to a different amount of arguments"
  | Unif.UnunifiableKinds -> throw "unequal kinds"

  | err -> print_endline "unidentified compilation error"; raise err
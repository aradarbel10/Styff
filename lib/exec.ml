open Typecheck.Typer
open Syntax.Raw
open Lexer
open Typecheck.Pretty
open Typecheck.Eval
open Typecheck.Scene

module Z = Syntax.Zonked
open Backend.Zonk
open Backend.Js

(*
elaborate given stmt under given scene, with [scp] to accumulate the qualified scope.
returns:
- scene bound with new unqualified names
- scope accumulator (not entire scene) updated with qualified names,
  could later be plugged into above scene to get qualified context.
- elaborated version of the statement (might produce a list of statements in result)
*)
let rec elab_stmt (scn : scene) (stmt : stmt) : scene * Z.prog =
  match stmt with
  | Def (rc, x, ps, t, e) ->
    (* elaborate the definition itself *)
    let scn', bod, typ = infer_let scn rc x ps t e in
    let bod = norm_expr scn'.env bod in

    (* print those *)
    print_endline ("let " ^ x ^ "\n\t : " ^
      string_of_vtype scn.scope typ ^ "\n\t = " ^
      string_of_expr scn.scope bod);

    (* zonk everything *)
    let ztyp = zonk_type scn.scope (quote scn'.height typ) in
    let zbod = zonk_expr scn.scope bod in

    let stmt' = Z.Def (rc, List.rev scn.scope.prefix @ [x], ztyp, zbod) in
    scn', [stmt']

  | TDef (x, k, t) ->
    let scn', _, vt, k = infer_let_type scn x k t in

    print_endline ("type " ^ x ^ "\n\t : " ^
      string_of_kind k ^ "\n\t = " ^
      string_of_vtype scn.scope vt);

    scn', []

  | Infer (x, e) ->
    let (_, te) = infer scn e in
    print_endline ("infer " ^ x ^ "\n\t : " ^
      string_of_vtype scn.scope te);
    scn, []

  | TInfer (x, t) ->
    let (_, kt) = kind_of scn t in
    print_endline ("infer type " ^ x ^ "\n\t : " ^
      string_of_kind kt);
    scn, []

  | Postulate (x, t) ->
    let (t, _) = kind_of scn t in
    let vt = eval scn.env t in
    assume x vt scn, []

  | PostulateType (x, k) ->
    let k = lower_kind k in
    assume_typ x k `ESolved scn, []

  | DataDecl (x, k, ctors) ->
    let scn = declare_data scn x k ctors in
    print_endline ("declared data " ^ x);
    scn, []

  | Section (sect, stmts) ->
    (* enter section *)
    let scn = {scn with scope = Scope.enter scn.scope sect} in

    (* elaborate contents *)
    let go_stmt (acc_scn, acc_prog : scene * Z.prog) (stmt : stmt) =
      let acc_scn', acc_prog' = elab_stmt acc_scn stmt in
      acc_scn', acc_prog @ acc_prog'
    in
    let scn, stmts' = List.fold_left go_stmt (scn, []) stmts in

    (* re-qualify scn *)
    let scn = {scn with scope = Scope.exit scn.scope} in

    scn, stmts'

let builtins_prog : prog = [
  Section ("builtin", [
    PostulateType ("int", RStar);
    Postulate ("int-add", RArrow (RBase `Int, RArrow (RBase `Int, RBase `Int)));
    Postulate ("int-mul", RArrow (RBase `Int, RArrow (RBase `Int, RBase `Int)));

    PostulateType ("bool", RStar);
    Postulate ("bool-true", RBase `Bool);
    Postulate ("bool-false", RBase `Bool);
  ])
]

let elab_prog (prog : prog) : Z.prog =
  let go_stmt (acc_scn, acc_prog : scene * Z.prog) (stmt : stmt) =
    let acc_scn', acc_prog' = elab_stmt acc_scn stmt in
    acc_scn', acc_prog @ acc_prog'
  in
  let preambled = builtins_prog @ prog in
  let _, stmts' = List.fold_left go_stmt (empty_scene, []) preambled in
  stmts'

let compile_prog (prog : prog) : string =
  prog
    |> elab_prog
    |> beta_fold_prog
    |> js_of_zonked
    |> string_of_js
let compile_prog_file (fil : string) : unit =
  parse_file fil
    |> Result.get_ok
    |> compile_prog
    |> (print_string "\n\n\nOUTPUT JS:\n==========\n"; print_endline)
let compile_prog_str (str : string) : unit =
  parse_str str
    |> Result.get_ok
    |> compile_prog
    |> (print_string "\n\n\nOUTPUT JS:\n==========\n"; print_endline)
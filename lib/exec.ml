open Typecheck.Typer
open Syntax.Raw
open Lexer
open! Typecheck.Pretty
open Typecheck.Eval
open Typecheck.Scene

module Z = Syntax.Zonked
open Backend.Zonk
open Backend.Js

(*
let rec exec_stmt (scn : scene) (s : stmt) : scene * scope * Z.prog =
  match s with
  | Def (rc, x, ps, t, e) ->
    let (scn, e, t) = infer_let scn rc x ps t e in
    let e = norm_expr scn.env e in
    let nms' = if rc then scn.scope.nms else List.tl (scn.scope.nms) in
    print_endline ("let " ^ x ^ "\n\t : " ^
      string_of_vtype scn.scope.tps t ^ "\n\t = " ^
      string_of_expr nms' scn.scope.tps e);
    scn, _, [Def (rc, x :: scn.scope.prefix, zonk_type scn.scope.tps (quote scn.height t), zonk_expr nms' scn.scope.tps e)]
  | TDef (x, k, t) ->
    let (scn', _, vt, k) = infer_let_type scn x k t in
    print_endline ("type " ^ x ^ "\n\t : " ^
      string_of_kind k ^ "\n\t = " ^
      string_of_vtype scn.scope.tps vt);
    scn', _, []
  | Infer (x, e) ->
    let (_, te) = infer scn e in
    print_endline ("infer " ^ x ^ "\n\t : " ^
      string_of_vtype scn.scope.tps te);
    scn, _, []
  | TInfer (x, t) ->
    let (_, kt) = kind_of scn t in
    print_endline ("infer type " ^ x ^ "\n\t : " ^
      string_of_kind kt);
    scn, _, []
  | Postulate (x, t) ->
    let (t, _) = kind_of scn t in
    let vt = eval scn.env t in
    assume scn x vt, _, []
  | BuiltIn _ -> failwith "unimplemented"
  | DataDecl (x, k, ctors) ->
    let scn = declare_data scn x k ctors in
    print_endline ("declared data " ^ x);
    scn, _, []
  | Section (sect, prog) ->
    let scn, prog = List.fold_left (fun (scn', prg') stmt ->
      let scn', stmt' = exec_stmt scn' stmt in scn', prg' @ stmt') (scn, []) prog
    in
    _

let exec_prog_str (str : string) : unit =
  let p = Result.get_ok @@ parse_str str in
  ignore @@ List.fold_left (fun scn p -> fst (exec_stmt scn p)) empty_scene p

let exec_prog_file (fil : string) : unit =
  let p = Result.get_ok @@ parse_file fil in
  ignore @@ List.fold_left (fun scn p -> fst (exec_stmt scn p)) empty_scene p
  

let check_prog (prog : prog) : Z.prog =
  try
    let (_, prog) = List.fold_left (
      fun (scn, p) s -> let (scn, p') = exec_stmt scn s in (scn, p @ p')
      ) (empty_scene, []) prog
    in prog
  with
  | Failure msg -> print_endline msg; failwith "error"
*)

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
  | _ -> failwith "unimplemented"

let check_prog (prog : prog) : Z.prog =
  let go_stmt (acc_scn, acc_prog : scene * Z.prog) (stmt : stmt) =
    let acc_scn', acc_prog' = elab_stmt acc_scn stmt in
    acc_scn', acc_prog @ acc_prog'
  in
  let _, stmts' = List.fold_left go_stmt (empty_scene, []) prog in
  stmts'

let compile_prog_file (fil : string) : unit =
  parse_file fil
    |> Result.get_ok
    |> check_prog
    |> beta_fold_prog
    |> js_of_zonked
    |> string_of_js
    |> (print_string "\n\n\nOUTPUT JS:\n==========\n"; print_endline)
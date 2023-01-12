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
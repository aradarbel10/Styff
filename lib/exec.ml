open Typer
open Expr
open Lexer
open Pretty
open Eval

let exec_stmt (scn : scene) (s : stmt) : scene =
  match s with
  | Def (x, t, e) ->
    let (scn', e, t) = infer_let scn x t e in
    let e = norm_expr scn.env e in
    print_endline ("let " ^ x ^ "\n\t : " ^
      string_of_vtype (tps scn) t ^ "\n\t = " ^
      string_of_expr (names scn) (tps scn) e);
    scn'
  | TDef (x, k, t) ->
    let (scn', _, vt, k) = infer_let_type scn x k t in
    print_endline ("type " ^ x ^ "\n\t : " ^
      string_of_kind k ^ "\n\t = " ^
      string_of_vtype (tps scn) vt);
    scn'
  | Infer (x, e) ->
    let (_, te) = type_of scn e in
    print_endline ("infer " ^ x ^ "\n\t : " ^
      string_of_vtype (tps scn) te);
    scn
  | TInfer (x, t) ->
    let (_, kt) = kind_of scn t in
    print_endline ("infer type " ^ x ^ "\n\t : " ^
      string_of_kind kt);
    scn
  | Postulate (x, t) ->
    let (t, _) = kind_of scn t in
    let vt = eval scn.env t in
    assume scn x vt

let exec_prog_str (str : string) : unit =
  let p = Result.get_ok @@ parse_str str in
  ignore @@ List.fold_left exec_stmt empty_scene p

let exec_prog_file (fil : string) : unit =
  let p = Result.get_ok @@ parse_file fil in
  ignore @@ List.fold_left exec_stmt empty_scene p
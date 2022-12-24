open Typecheck.Typer
open Syntax.Raw
open Lexer
open Typecheck.Pretty
open Typecheck.Eval
open Typecheck.Scene

module Z = Syntax.Zonked
open Backend.Js
open Backend.Zonk

let exec_stmt (scn : scene) (s : stmt) : scene * Z.prog =
  match s with
  | Def (rc, x, ps, t, e) ->
    let (scn, e, t) = infer_let scn rc x ps t e in
    let e = norm_expr scn.env e in
    let nms' = if rc then names scn else List.tl (names scn) in
    print_endline ("let " ^ x ^ "\n\t : " ^
      string_of_vtype (tps scn) t ^ "\n\t = " ^
      string_of_expr nms' (tps scn) e);
    scn, [Def (rc, x, zonk_type (tps scn) (quote scn.height t), zonk_expr nms' (tps scn) e)]
  | TDef (x, k, t) ->
    let (scn', _, vt, k) = infer_let_type scn x k t in
    print_endline ("type " ^ x ^ "\n\t : " ^
      string_of_kind k ^ "\n\t = " ^
      string_of_vtype (tps scn) vt);
    scn', []
  | Infer (x, e) ->
    let (_, te) = infer scn e in
    print_endline ("infer " ^ x ^ "\n\t : " ^
      string_of_vtype (tps scn) te);
    scn, []
  | TInfer (x, t) ->
    let (_, kt) = kind_of scn t in
    print_endline ("infer type " ^ x ^ "\n\t : " ^
      string_of_kind kt);
    scn, []
  | Postulate (x, t) ->
    let (t, _) = kind_of scn t in
    let vt = eval scn.env t in
    assume scn x vt, []
  | BuiltIn _ -> failwith "unimplemented"
  | DataDecl (x, k, ctors) ->
    let scn = declare_data scn x k ctors in
    print_endline ("declared data " ^ x);
    scn, []

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

let compile_prog_file (fil : string) : unit =
  let js = parse_file fil
    |> Result.get_ok
    |> check_prog
    |> beta_fold_prog
    |> js_of_zonked
    |> string_of_js
  in print_string "\n\n\nOUTPUT JS:\n==========\n"; print_endline js
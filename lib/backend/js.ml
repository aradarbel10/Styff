open Syntax.Common
module Z = Syntax.Zonked

module JS = struct
  type block = stmt list
  and stmt =
  | DeclVar of string
  | AssgnVar of string * expr
  | Assgn of string * expr
  | IfTagElse of expr * (string * block) list
  | Destruct of string list * expr
  | Ret of expr
  | Print of expr
  and expr =
  | Var of string
  | Lam of string * block
  | App of expr * expr
  | Block of block
  | Tup of expr list
  | ProjAt of expr * int
  | TagWith of string * expr list
  | Lit of lit
  | Null
  | BinOp of expr * binop * expr
end

let ret e = [JS.Ret e]

let js_of_zonked (prog : Z.prog) : JS.block =
  let erase_pat (args) : string list =
    List.map (function | PVar x -> x | PTvar _ -> freshen_str "_") args
  in
  let rec go_stmt : Z.stmt -> JS.block = function
  | Def (x, _, e) ->
    go_expr e (fun r -> [JS.Assgn (x, r)])
  | Print e ->
    go_expr e (fun r -> [JS.Print r])

  and go_expr (e : Z.expr) (k : JS.expr -> JS.block) : JS.block =
    let ( let* ) = go_expr in
    match e with
    | Var x -> k @@ Var x
    | Lam (x, _, e) -> k @@ Lam (x, go_expr e ret)
    | Tlam (_, _, e) -> k @@ Lam ("_", go_expr e ret)
    | App (e1, e2) ->
      let* v1 = e1 in
      let* v2 = e2 in
      k @@ App (v1, v2)
    | Inst (e, _) ->
      let* v = e in
      k @@ App (v, Null)
    | Let (x, e, rest) ->
      let* v = e in
      Assgn (x, v)
      :: go_expr rest k
    | Match (e, bs) ->
      let res = freshen_str "r" in
      let scrut = freshen_str "v" in
      let go_branch (Z.PCtor (ctor, vars), branch) : string * JS.block =
        ctor,
        Destruct (erase_pat vars, Var scrut)
        :: go_expr branch (fun e -> [AssgnVar (res, e)])
      in

      let* v = e in
      Assgn (scrut, v)
      :: DeclVar res
      :: IfTagElse (Var scrut, List.map go_branch bs)
      :: go_expr (Var res) k
    | Tup es ->
      let rec go_tup vs es : JS.block =
        match es with
        | [] ->
          k @@ Tup (List.rev vs)
        | e :: es ->
          let* v = e in
          go_tup (v :: vs) es
      in go_tup [] es
    | Ctor (c, es) ->
      let rec go_ctor vs es : JS.block =
        match es with
        | [] -> k @@ TagWith (c, List.rev vs)
        | `TmArg e :: es ->
          let* v = e in
          go_ctor (v :: vs) es
        | `TpArg _ :: es ->
          go_ctor (Null :: vs) es
      in go_ctor [] es
    | ProjAt (e, i) ->
      let* v = e in
      k @@ ProjAt (v, i)
    | BinOp (e1, op, e2) ->
      let* v1 = e1 in
      let* v2 = e2 in
      k @@ BinOp (v1, op, v2)
    | Lit l -> k @@ Lit l
  in
  List.fold_left (@) [] (List.map go_stmt prog)

let string_of_js =
  let rec go_block (indent : int) (block : JS.block) : string =
    String.concat "" (List.map (go_stmt indent) block)
  and go_stmt (indent : int) (block : JS.stmt) : string =
    match block with
    | Assgn (x, e) ->
      String.make indent '\t' ^ "let " ^ x ^ " = " ^ go_expr indent e ^ ";\n"
    | AssgnVar (x, e) ->
      String.make indent '\t' ^ x ^ " = " ^ go_expr indent e ^ ";\n"
    | DeclVar x ->
      String.make indent '\t' ^ "var " ^ x ^ ";\n"
    | IfTagElse (e, opts) ->
      let opts = List.map (fun (lbl, bod) ->
        "(" ^ go_expr indent e ^ "[0] == \"" ^ lbl ^ "\")" ^ "{\n"
        ^ go_block (indent + 1) bod
        ^ String.make indent '\t' ^ "}"
        ) opts
      in
      String.make indent '\t' ^ "if " ^ String.concat " else if " opts ^ "\n"
    | Destruct (xs, e) ->
      String.make indent '\t' ^ "let [_" ^ String.concat "" (List.map (fun x -> ", " ^ x) xs) ^ "] = " ^ go_expr indent e ^ ";\n"
    | Ret e ->
      String.make indent '\t' ^ "return " ^ go_expr indent e ^ ";\n"
    | Print e ->
      String.make indent '\t' ^ "outputPrint(" ^ go_expr indent e ^ ");\n"
  and go_expr (indent : int) : JS.expr -> string = function
  | Var x -> x
  | Lam (x, e) -> "(" ^ x ^ " => " ^ go_expr indent (Block e) ^ ")"
  | App (e1, e2) -> go_expr indent e1 ^ "(" ^ go_expr indent e2 ^ ")"
  | Block b ->
    "{\n" ^
      go_block (indent + 1) b ^
      String.make indent '\t' ^ "}"
  | Tup es -> "[" ^ String.concat ", " (List.map (go_expr indent) es) ^ "]"
  | ProjAt (e, i) -> go_expr indent e ^ "[" ^ string_of_int i ^ "]"
  | TagWith (x, es) -> "[\"" ^ x ^ "\"" ^ String.concat "" (List.map (fun e -> ", " ^ go_expr indent e) es) ^ "]"
  | Lit l -> go_lit l
  | Null -> "null"
  | BinOp (e1, op, e2) -> "(" ^ go_expr indent e1 ^ " " ^ string_of_binop op ^ " " ^ go_expr indent e2 ^ ")"
  and go_lit : lit -> string = function
  | `Int i -> string_of_int i
  | `Bool b -> string_of_bool b
  in go_block 0
open Syntax.Core
open Eval
open Scene

let string_of_base : base -> string = function
| `Int -> "int"
| `Bool -> "bool"
let string_of_lit : lit -> string = function
| `Int n -> string_of_int n
| `Bool true -> "true"
| `Bool false -> "false"

let rec string_of_type (scp : Scope.t) (t : typ) : string =
  let rec go (p : int) (scp : Scope.t) = function (* [p]recedence printing *)
  | Tvar (tv, _) ->
    begin match !tv with
    | Solved t -> "(" ^ string_of_vtype Scope.empty t ^ ")"
    | Unsolved x -> "?" ^ x
    end
  | Qvar i -> string_of_name (Scope.ith_type scp i)
  | Inserted _ -> "?inserted"
  | Arrow (lt, rt) -> parens (p > 1) @@ go 2 scp lt ^ " → " ^ go 1 scp rt
  | Tapp (t1, t2) ->
    (* sketchy way to hide parameters applied on flexible meta *)
    let rec tapp_head : typ -> typ = function
    | Tapp (tapp, _) -> tapp_head tapp
    | t -> t
    in
    begin match tapp_head t1 with
    | Tvar _ as tv -> go p scp tv
    | _ -> parens (p > 2) @@ go 2 scp t1 ^ " " ^ go 3 scp t2
    end
  | TLet (x, k, t, rest) -> parens (p > 0) @@ "let type " ^ x ^ " : " ^ string_of_kind k
    ^ " = " ^ go 0 scp t ^ " in " ^ go 0 (fst @@ Scope.push_type scp x) rest
  | TAbs (x, k, B t) -> parens (p > 0) @@ "λ(" ^ x ^ " : " ^ string_of_kind k ^ "). " ^ go 0 (fst @@ Scope.push_type scp x) t
  | Forall (x, k, B t) -> parens (p > 0) @@ "{" ^ x ^ " : " ^ string_of_kind k ^ "} → " ^ go 0 (fst @@ Scope.push_type scp x) t
  | Base b -> string_of_base b
  in go 0 scp t
and string_of_vtype (scp : Scope.t) (t : vtyp) : string =
  let t = quote (Lvl scp.type_height) t in
  string_of_type scp t

and string_of_pattern (scp : Scope.t) (PCtor (ctor, args)) : string =
  let strs = List.map (function | PVar v -> v | PTvar v -> "{" ^ v ^ "}") args in
  let str = String.concat " " strs in
  string_of_name (Scope.ith_term scp ctor) ^ " " ^ str
and string_of_expr (scp : Scope.t) (expr : expr) : string =
  let rec go_lam (scp : Scope.t) = function
  | Lam (x, t, e) -> "(" ^ x ^ " : " ^ string_of_type scp t ^ ") " ^ go_lam (fst @@ Scope.push_term scp x) e
  | Tlam (x, k, e, _) -> "{" ^ x ^ " : " ^ string_of_kind k ^ "} " ^ go_lam (fst @@ Scope.push_type scp x) e
  | e -> ". " ^ go 0 scp e
  and go_branch (scp : Scope.t) (((PCtor (_, args) as pat), bod) : pattern * expr) : string =
    let scp' = List.fold_left (fun scp -> function
      | PVar  v -> fst @@ Scope.push_term scp v
      | PTvar v -> fst @@ Scope.push_type scp v) scp args in
    string_of_pattern scp pat ^ " . " ^ go 0 scp' bod
  and go_arg (scp : Scope.t) : arg -> string = function
  | `TmArg e -> go 0 scp e
  | `TpArg t -> "{" ^ string_of_type scp t ^ "}"
  and go (p : int) (scp : Scope.t) = function
  | Var i -> string_of_name (Scope.ith_term scp i)
  | Ctor (i, es) -> string_of_name (Scope.ith_term scp i)
    ^ "(" ^ String.concat ", " (List.map (go_arg scp) es) ^ ")"
  | Lam _ | Tlam _ as e -> parens (p > 0) @@ "λ" ^ go_lam scp e
  | App (e1, e2) -> parens (p > 2) @@ go 2 scp e1 ^ " " ^ go 3 scp e2
  | Inst (e, t) -> parens (p > 2) @@ go 2 scp e ^ " {" ^ string_of_type scp t ^ "}"
  | Let (rc, x, t, e, rest) ->
    parens (p > 0) @@ "let " ^ x ^ " : " ^ string_of_type scp t
    ^ " = " ^ go 0 (if rc then fst @@ Scope.push_term scp x else scp) e ^ " in " ^ go 0 (fst @@ Scope.push_term scp x) rest
  | Match (s, bs) ->
    parens (p > 0) @@ "match " ^ go 0 scp s ^ " with { " ^
    String.concat " | " (List.map (go_branch scp) bs)
    ^ " }"
  | Lit l -> string_of_lit l
  | BinOp (e1, op, e2) -> "(" ^ go p scp e1 ^ " " ^ string_of_binop op ^ " " ^ go p scp e2 ^ ")"
  in go 0 scp expr


and string_of_kind (k : kind) : string =
  let rec go (p : int) (k : kind) : string =
    match forcek k with
    | Star -> "∗"
    | KArrow (lk, rk) -> parens (p > 1) @@ go 2 lk ^ " → " ^ go 1 rk
    | KVar kv ->
      match !kv with
      | KSolved k -> go p k
      | KUnsolved x -> "?" ^ x
  in go 0 k
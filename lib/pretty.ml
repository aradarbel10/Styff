open Batteries.Uref
open Expr
open Eval

let string_of_base : base -> string = function
| `Int -> "int"
| `Bool -> "bool"
let string_of_lit : lit -> string = function
| `Int n -> string_of_int n
| `Bool true -> "true"
| `Bool false -> "false"

let parens (b : bool) (s : string) : string =
  if b then "(" ^ s ^ ")" else s

let symbols = ['!'; '@'; '#'; '$'; '%'; '^'; '&'; '*'; '-'; '+'; ';'; '?'; '/'; '<'; '>'; ','; '~'; '='; '.'; ':'; '|']
let print_name (x : name) : string =
  if List.mem x.[0] symbols
    then parens true x
    else x

let rec string_of_type (nms : name list) (t : typ) : string =
  let rec go (p : int) (nms : name list) = function (* [p]recedence printing *)
  | Tvar tv ->
    begin match uget tv with
    | Solved t -> "(" ^ string_of_vtype [] t ^ ")"
    | Unsolved x -> "?" ^ x
    end
  | Qvar (Idx i) -> print_name (List.nth nms i)
  | Inserted (tv, msk) -> go_inserted p nms tv msk
  | Arrow (lt, rt) -> parens (p > 1) @@ go 2 nms lt ^ " → " ^ go 1 nms rt
  | Tapp (t1, t2) -> parens (p > 2) @@ go 2 nms t1 ^ " " ^ go 3 nms t2
  | TLet (x, t, rest) -> parens (p > 0) @@ "let type " ^ print_name x ^ " = " ^ go 0 nms t ^ " in " ^ go 0 (x :: nms) rest
  | TAbs (x, B t) -> parens (p > 0) @@ "λ" ^ print_name x ^ ". " ^ go 0 (x :: nms) t
  | Forall (x, B t) -> parens (p > 0) @@ "[" ^ print_name x ^ "] → " ^ go 0 (x :: nms) t
  | Base b -> string_of_base b
  and go_inserted (p : int) (nms : name list) (tv : tvar uref) (msk : mask) =
    match nms, msk with
    | [], [] -> go p nms (Tvar tv)
    | x :: nms, true  :: msk -> parens (p > 2) @@ go_inserted 2 nms tv msk ^ " " ^ print_name x
    | _ :: nms, false :: msk -> go_inserted 2 nms tv msk
    | _ -> raise (Failure "impossible - can't print ill-lengthed inserted meta")
  in go 0 nms t
and string_of_vtype (nms : name list) (t : vtyp) : string =
  let hi = Lvl (List.length nms) in
  let t = quote hi t in
  string_of_type nms t

and string_of_expr (nms : name list) (tps : name list) (expr : expr) : string =
  let rec go_lam (nms : name list) (tps : name list) = function
  | Lam (x, t, e) -> "(" ^ print_name x ^ " : " ^ string_of_type tps t ^ ") " ^ go_lam (x :: nms) tps e
  | Tlam (x, e) -> "[" ^ print_name x ^ "] " ^ go_lam nms (x :: tps) e
  | e -> ". " ^ go 0 nms tps e
  and go (p : int) (nms : name list) (tps : name list) = function
  | Var (Idx i) -> print_name (List.nth nms i)
  | Lam _ | Tlam _ as e -> "λ" ^ go_lam nms tps e
  | App (e1, e2) -> parens (p > 2) @@ go 2 nms tps e1 ^ " " ^ go 3 nms tps e2
  | Inst (e, t) -> parens (p > 2) @@ go 2 nms tps e ^ " [" ^ string_of_type tps t ^ "]"
  | Let (rc, x, t, e, rest) ->
    parens (p > 0) @@ "let " ^ print_name x ^ " : " ^ string_of_type tps t
    ^ " = " ^ go 0 (if rc then x :: nms else nms) tps e ^ " in " ^ go 0 (x :: nms) tps rest
  | Lit l -> string_of_lit l
  in go 0 nms tps expr

and string_of_kind (k : kind) : string =
  let rec go (p : int) (k : kind) : string =
    match forcek k with
    | Star -> "*"
    | KArrow (lk, rk) -> parens (p > 1) @@ go 2 lk ^ " → " ^ go 1 rk
    | KVar kv ->
      match uget kv with
      | KSolved k -> go p k
      | KUnsolved x -> "?" ^ x
  in go 0 k
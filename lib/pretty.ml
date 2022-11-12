open Batteries.Uref
open Expr
open Eval

let string_of_base : base -> string = function
| `Nat -> "nat"
| `Bool -> "bool"
let string_of_lit : lit -> string = function
| `Nat n -> string_of_int n
| `Bool true -> "true"
| `Bool false -> "false"

let parens (b : bool) (s : string) : string =
  if b then "(" ^ s ^ ")" else s
let rec string_of_type (nms : name list) (t : typ) : string =
  let rec go (p : int) (nms : name list) = function (* [p]recedence printing *)
  | Tvar tv ->
    begin match uget tv with
    | Solved t -> "(" ^ string_of_vtype [] t ^ ")"
    | Unsolved x -> "?" ^ x
    end
  | Qvar (Idx i) -> List.nth nms i
  | Inserted (tv, _msk) -> go p nms (Tvar tv)
  | Arrow (lt, rt) -> parens (p > 1) @@ go 2 nms lt ^ " → " ^ go 1 nms rt
  | Tapp (t1, t2) -> parens (p > 2) @@ go 2 nms t1 ^ " " ^ go 3 nms t2
  | TAbs (x, B t) -> parens (p > 0) @@ "λ" ^ x ^ ". " ^ go 0 (x :: nms) t
  | Forall (x, B t) -> parens (p > 0) @@ "∀" ^ x ^ ". " ^ go 0 (x :: nms) t
  | Base b -> string_of_base b
  in go 0 nms t
and string_of_vtype (nms : name list) (t : vtyp) : string =
  let hi = Lvl (List.length nms) in
  let t = quote hi t in
  string_of_type nms t

and string_of_expr (nms : name list) (tps : name list) (expr : expr) : string =
  let rec go (p : int) (nms : name list) (tps : name list) = function
  | Var (Idx i) -> List.nth nms i
  | Lam (x, t, e) -> parens (p > 0) @@ "λ" ^ x ^ ":" ^ string_of_type tps t ^ ". " ^ go 0 (x :: nms) tps e
  | Tlam (x, e) -> parens (p > 0) @@ "Λ" ^ x ^ ". " ^ go 0 nms (x :: tps) e
  | App (e1, e2) -> parens (p > 2) @@ go 2 nms tps e1 ^ " " ^ go 3 nms tps e2
  | Inst (e, t) -> parens (p > 2) @@ go 2 nms tps e ^ " [" ^ string_of_type tps t ^ "]"
  | Let (x, t, e, rest) ->
    parens (p > 0) @@ "let " ^ x ^ " : " ^ string_of_type tps t
    ^ " = " ^ go 0 nms (* TODO remember to change this when adding recursive binds *) tps e ^ " in " ^ go 0 (x :: nms) tps rest
  | Lit l -> string_of_lit l
  in go 0 nms tps expr
include Common

(* the zonked representation is a finalized version of [Core],
  after type checking all type variables are "zonked" and all bound
  variables become explicitly named *)
type kind =
| Star
| KArrow of kind * kind

type typ =
| Qvar of name
| Arrow of typ * typ
| TApp of typ * typ
| TAbs of name * kind * typ
| Forall of name * kind * typ
| Prod of typ list
| Base of base

type pattern = PCtor of name * pat_arg list
and expr =
| Var of name
| Ctor of name * arg list
| Lam of name * typ * expr
| Tlam of name * kind * expr
| App of expr * expr
| Inst of expr * typ
| Let of name * expr * expr
| Match of expr * (pattern * expr) list
| Tup of expr list
| ProjAt of expr * int
| Lit of lit
| BinOp of expr * binop * expr
and arg = [`TmArg of expr | `TpArg of typ]


and stmt =
| Def of bool * name * typ * expr
| TDef of name * kind * typ
and prog = stmt list
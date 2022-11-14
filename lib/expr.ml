open Batteries.Uref

type name = string

type base = [`Int | `Bool]
type lit = [`Int of int | `Bool of bool]

type idx = Idx of int
type lvl = Lvl of int

type rkind =
| RStar
| RKArrow of rkind * rkind

type rtyp =
| RQvar of name
| RArrow of rtyp * rtyp
| RTapp of rtyp * rtyp
| RTAbs of name * rkind option * rtyp
| RTLet of name * rkind option * rtyp * rtyp
| RForall of name * rtyp
| RBase of base
| RHole
  
type rexpr =
| RVar of name
| RAnn of rexpr * rtyp
| RLam of name * rtyp option * rexpr
| RTlam of name * rkind option * rexpr
| RApp of rexpr * rexpr
| RInst of rexpr * rtyp
| RLet of name * rtyp option * rexpr * rexpr
| RLit of lit

type stmt =
| Def of name * rtyp option * rexpr
| TDef of name * rkind option * rtyp
| Infer of name * rexpr
| TInfer of name * rtyp
| Postulate of name * rtyp
type prog = stmt list


type expr =
| Var of idx
| Lam of name * typ * expr
| Tlam of name * expr
| App of expr * expr
| Inst of expr * typ
| Let of name * typ * expr * expr
| Lit of lit

and typ =
| Tvar of tvar uref
| Inserted of tvar uref * mask
| Qvar of idx
| Arrow of typ * typ
| Tapp of typ * typ
| TAbs of name * bdr
| TLet of name * typ * typ
| Forall of name * bdr
| Base of base
and bdr = B of typ
and mask = bool list (* true -- bound ;; false -- unbound *)

and vtyp =
| VArrow of vtyp * vtyp
| VAbs of name * clos
| VForall of name * clos
| VBase of base
| VNeut of head * spine
and tvar =
| Solved of vtyp
| Unsolved of name
and head =
| VQvar of lvl
| VTvar of tvar uref
and spine = vtyp list
and clos = {env : env; bdr : bdr}
and env = (name * vtyp) list

and kind =
| Star
| KArrow of kind * kind
| KVar of kvar uref
and kvar =
| KSolved of kind
| KUnsolved of name


let unLvl (Lvl i) = i
let inc (Lvl i) = Lvl (i + 1)
let lvl2idx (Lvl hi : lvl) (Lvl i) = Idx (hi - i - 1)
let lookup (Idx i) (env : env) = List.nth_opt env i

let vqvar (i : lvl) : vtyp = VNeut (VQvar i, [])

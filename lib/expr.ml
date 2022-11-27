open Batteries.Uref

type name = string

type base = [`Int | `Bool]
type lit = [`Int of int | `Bool of bool]

type idx = Idx of int
type lvl = Lvl of int

(* raw language, parser's output *)
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
  
type pat_arg =
| PVar of name
| PTvar of name
type pattern = PCtor of name * pat_arg list

type rexpr =
| RVar of name
| RAnn of rexpr * rtyp
| RLam of name * rtyp option * rexpr
| RTlam of name * rkind option * rexpr
| RApp of rexpr * rexpr
| RInst of rexpr * rtyp
| RLet of bool * name * rtyp option * rexpr * rexpr
| RMatch of rexpr * (pattern * rexpr) list
| RLit of lit

type rctor = Ctor of {nam : name; t : rtyp}

type stmt =
| Def of bool * name * rtyp option * rexpr
| TDef of name * rkind option * rtyp
| Infer of name * rexpr
| TInfer of name * rtyp
| Postulate of name * rtyp
| DataDecl of name * rkind option * rctor list
type prog = stmt list

(* core language, typechecker's output

   uses debruijn indices to trivialize α-equivalence
*)
type expr =
| Var of idx
| Lam of name * typ * expr
| Tlam of name * expr
| App of expr * expr
| Inst of expr * typ
| Let of bool * name * typ * expr * expr
| Match of expr * (pattern * expr) list
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

and ebound = [`EBound | `EDefed]
and esolved = [`ESolved | `EUnsolved]
and mask = ebound list

(* semantic domain (values), used for normalization

   uses debruijn levels to trivialize weakening,
   has no β-redexes so β-equality is easy (during unification)

   subdomain: "neutrals" - values where computation is stuck on a variable
                           represented in spine form.
*)
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
and clos = {env : env; bdr : bdr} (* [bdr] lives in a scene of height |env|+1, the extra value is the closure's parameter *)

and env = (name * esolved * ebound * vtyp) list
(*
types in the environment are stored as values, signifies "these are already normalized! just unpack them with [quote]"
we also keep track of two boolean flags
- solved? whether the variable is a solved one, ragarding the env as a metacontext.
  an unsolved var at level [i] should have the value [VNeut (VQvar i, [])]
  a solved var might have any other value, which should be well-scoped and -typed in the
  tail of the context before itself (or including itself, if trivially recursive)
- bound? whether the variable is a bound one, and can be used in inserted metas' spines.
  bound values have the form [VNeut (VQvar i, [])], hence all unsolved vars are bound but not vise versa.

example:
   when defining ADTs, the type being defined becomes bound, but not unsolved.
   that way, it can be used in metavar solutions, but it can't be assigned a solution in unification.
*)

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
let lookup_lvl (i : lvl) (env : env) = lookup (lvl2idx (Lvl (List.length env)) i) env

let vqvar (i : lvl) : vtyp = VNeut (VQvar i, [])
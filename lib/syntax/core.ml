include Common

(* core language, typechecker's output

   uses debruijn indices to trivialize α-equivalence
*)
type pattern = PCtor of idx * pat_arg list
type expr =
| Var of idx
| Ctor of idx * arg list
| Lam of string * typ * expr
| Tlam of string * kind * expr
| App of expr * expr
| Inst of expr * typ
| Let of bool * string * typ * expr * expr
| Match of expr * (pattern * expr) list
| Lit of lit
| BinOp of expr * binop * expr
and arg = [`TmArg of expr | `TpArg of typ]

and typ =
| Tvar of tvar ref * kind
| Inserted of tvar ref * kind * mask
| Qvar of idx
| Arrow of typ * typ
| Tapp of typ * typ
| TAbs of string * kind * bdr
| TLet of string * kind * typ * typ
| Forall of string * kind * bdr
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
| VAbs of string * clos
| VForall of string * clos
| VBase of base
| VNeut of head * spine
and tvar =
| Solved of vtyp
| Unsolved of string
and head =
| VQvar of lvl
| VTvar of tvar ref * kind
and spine = vtyp list
and clos = {knd : kind; env : env; bdr : bdr} (* [bdr] lives in a scene of height |env|+1, the extra value is the closure's parameter *)

and vparam = [`TpParam of kind | `TmParam of vtyp]

and env = (esolved * ebound * vtyp) list
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
| KVar of kvar ref
and kvar =
| KSolved of kind
| KUnsolved of string


let lookup (Idx i) (env : env) = List.nth_opt env i
let height env : lvl = Lvl (List.length env)
let lookup_lvl (i : lvl) (env : env) = lookup (lvl2idx (height env) i) env

let vqvar (i : lvl) : vtyp = VNeut (VQvar i, [])
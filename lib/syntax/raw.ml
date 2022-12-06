include Common

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
| RForall of name * rkind option * rtyp
| RBase of base
| RHole

type rparam =
| RParam of name * rtyp option
| RTParam of name * rkind option

type rexpr =
| RVar of name
| RAnn of rexpr * rtyp
| RLam of name * rtyp option * rexpr
| RTlam of name * rkind option * rexpr
| RApp of rexpr * rexpr
| RInst of rexpr * rtyp
| RLet of bool * name * rparam list * rtyp option * rexpr * rexpr
| RMatch of rexpr * (pattern * rexpr) list
| RLit of lit

type rctor = Ctor of {nam : name; t : rtyp}

type stmt =
| Def of bool * name * rparam list * rtyp option * rexpr
| TDef of name * rkind option * rtyp
| Infer of name * rexpr
| TInfer of name * rtyp
| Postulate of name * rtyp
| DataDecl of name * rkind option * rctor list
type prog = stmt list
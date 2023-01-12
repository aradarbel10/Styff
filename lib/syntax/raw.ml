include Common

(* raw language, parser's output *)
type rkind =
| RStar
| RKArrow of rkind * rkind

type rtyp =
| RQvar of name
| RArrow of rtyp * rtyp
| RTapp of rtyp * rtyp
| RTAbs of string * rkind option * rtyp
| RTLet of string * rkind option * rtyp * rtyp
| RForall of string * rkind option * rtyp
| RBase of base
| RHole

type rparam =
| RParam of string * rtyp option
| RTParam of string * rkind option

type rpattern = RPCtor of name * pat_arg list
type rexpr =
| RVar of name
| RAnn of rexpr * rtyp
| RLam of string * rtyp option * rexpr
| RTlam of string * rkind option * rexpr
| RApp of rexpr * rexpr
| RInst of rexpr * rtyp
| RLet of bool * string * rparam list * rtyp option * rexpr * rexpr
| RMatch of rexpr * (rpattern * rexpr) list
| RLit of lit

type rctor = RCtor of {nam : string; t : rtyp}

type stmt =
| Def of bool * string * rparam list * rtyp option * rexpr
| TDef of string * rkind option * rtyp
| Infer of string * rexpr
| TInfer of string * rtyp
| Postulate of string * rtyp
| DataDecl of string * rkind option * rctor list
| BuiltIn of string * string
| Section of string * prog
and prog = stmt list
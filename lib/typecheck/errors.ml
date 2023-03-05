open Scene
open Syntax.Common

type elab_code =
| UndefinedVar of name
| UndefinedQVar of name
| UnificationFailure of string * string

| TooManyArgsInPattern of name (* todo: add expected vs actual parameter counts *)
| UnexpectedTArgPattern

| DuplicateCase of name
| MissingCases of name list
| UnrelatedCase of name
type elab_err = {
  code : elab_code;
  scp : scope;
  range : src_range;
}
let show_elab_err ({code; scp = _; range = rng} : elab_err) : string =
  string_of_range rng ^ ": " ^ match code with
  | UndefinedVar x -> "undefined variable `" ^ string_of_name x ^ "`"
  | UndefinedQVar x -> "undefined type var " ^ string_of_name x
  | UnificationFailure (t1, t2) -> "unification failure " ^ t1 ^ " ~/~ " ^ t2
  | TooManyArgsInPattern ctor -> "pattern with ctor " ^ string_of_name ctor ^ " has too many arguments"
  | UnexpectedTArgPattern -> "unexpected type argument in pattern"
  | DuplicateCase ctor -> "match clause has duplicate cases for `" ^ string_of_name ctor ^ "`"
  | UnrelatedCase ctor -> "match clause has an unrelated constructor `" ^ string_of_name ctor  ^ "`"
  | MissingCases ctors ->
    let ctors, rest = Util.take_or_less 3 ctors in
    let ctors = List.map (fun ctor -> "`" ^ string_of_name ctor ^ "`") ctors in
    "match clause is missing a case for: " ^ String.concat ", " ctors
    ^ match rest with
    | None -> "."
    | Some rest -> ", and " ^ string_of_int rest ^ " more."

type eval_code =
| IndexOutOfScope
| AppNonAbs
| IllLengthedMask
| UnnormalizedInsertedMeta
type eval_err = {
  code : eval_code;
}
let show_eval_err ({code} : eval_err) : string =
  "(internal) " ^ match code with
  | IndexOutOfScope -> "too big debruijn index"
  | AppNonAbs -> "cannot evaluate application on non-function value"
  | IllLengthedMask -> "environment mask has wrong length"
  | UnnormalizedInsertedMeta -> "normalized types cannot contain inserted metas"

type parse_err = SyntaxErr of src_range
let show_parse_err (SyntaxErr rng : parse_err) : string = "syntax error at " ^ string_of_range rng

exception LexFailure of src_range * string
exception ParseFailure of parse_err
exception ElabFailure of elab_err
exception EvalFailure of eval_err

let elab_complain (scn : scene) (code : elab_code) =
  raise (ElabFailure {code = code; scp = scn.scope; range = scn.range})
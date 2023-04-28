(* a name is a list of strings, representing an access path
   eg `std.io.print` is represneted as `["std"; "io"; "print"]`.
*)
type name = string list

(* source of fresh names, mutable counter is hidden *)
module Fresh : sig
  val uniquei : unit -> int
  val freshen_str : string -> string
  val freshen : name -> name
end = struct
  let freshi = ref (-1)
  let uniquei () = freshi := !freshi + 1; !freshi
  let freshen_str (x : string) = x ^ string_of_int (uniquei ())
  let rec freshen = function
  | [] -> []
  | [s] -> [freshen_str s]
  | s :: ss -> s :: freshen ss
end
include Fresh

type idx = Idx of int
type lvl = Lvl of int

let unLvl (Lvl i) = i
let unIdx (Idx i) = i
let inc (Lvl i) = Lvl (i + 1)
let lvl2idx (Lvl hi : lvl) (Lvl i) = Idx (hi - i - 1)
let at_idx (xs : 'a list) (Idx i : idx) = List.nth xs i

type base = [`Int | `Bool]
type lit = [`Int of int | `Bool of bool]

type pat_arg =
| PVar of string
| PTvar of string

type binop = IntAdd | IntSub | IntMul | BoolAnd | BoolOr
let string_of_binop : binop -> string = function
| IntAdd -> "+"
| IntSub -> "-"
| IntMul -> "*"
| BoolAnd -> "&&"
| BoolOr -> "||"

(* printing names *)
let parens (b : bool) (s : string) : string =
  if b then "(" ^ s ^ ")" else s

let symbols = ['!'; '@'; '#'; '$'; '%'; '^'; '&'; '*'; '-'; '+'; ';'; '?'; '/'; '<'; '>'; ','; '~'; '='; '.'; ':'; '|']
let string_of_name (nm : name) : string =
  String.concat "." (List.map (fun s -> parens (List.mem s.[0] symbols) s) nm)
let string_of_names (nms : name list) : string =
  String.concat ";" (List.map string_of_name (List.rev nms))

(* for error reporting *)
type src_range = Lexing.position * Lexing.position
let dummy_range = Lexing.dummy_pos, Lexing.dummy_pos
let string_of_range (pos_i, _pos_f : src_range) =
  "input:" ^ string_of_int pos_i.pos_lnum ^ ":" ^ string_of_int (pos_i.pos_cnum - pos_i.pos_bol + 1)
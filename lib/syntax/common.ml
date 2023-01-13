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
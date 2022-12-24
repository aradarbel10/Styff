type name = string

(* source of fresh names, mutable counter is hidden *)
module Fresh : sig
  val uniquei : unit -> int
  val freshen : name -> name
end = struct
  let freshi = ref (-1)
  let uniquei () = freshi := !freshi + 1; !freshi
  let freshen (x : name) = x ^ string_of_int (uniquei ())
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
| PVar of name
| PTvar of name

type binop = IntAdd | IntSub | IntMul | BoolAnd | BoolOr
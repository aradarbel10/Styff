open Implifit.Typer
open Implifit.Lexer
open Implifit.Pretty

let run_infer msg input =
  print_endline msg;
  let e = Result.get_ok @@ parse_str input in
  let (e, t) = type_of empty_scene e in
  print_string "\t= "; print_endline (string_of_expr [] [] e);
  print_string "\t: "; print_endline (string_of_vtype [] t)

let ex_bool () =
  print_endline "\n\nBooleans";

  run_infer "true "  "ΛA. λx:A. λy:A. x";
  run_infer "false" "ΛA. λx:A. λy:A. y";

  run_infer "and  " "λx:(∀A. A → A → A). λy:(∀A. A → A → A). x [∀A. A → A → A] y (ΛA. λx:A. λy:A. y)";
  run_infer "and' " "λx:(∀A. A → A → A). λy. x [∀A. A → A → A] y (ΛA. λx. λy. y)";
  ()

  
let ex_nat () =
  print_endline "\n\nNaturals";

  run_infer "zero" "                          ΛA. λs:(A → A). λz:A. z";
  run_infer "succ" "λn:(∀A. (A → A) → A → A). ΛA. λs.         λz.   s (n [A] s z)";
  ()


let ex_pair () =
  print_endline "\n\nPairs";
  run_infer "pair" "ΛA. ΛB. λx. λy. ΛC. λf:A → B → C. f x y";
  run_infer "fst" "ΛA. ΛB. λp:(∀C. (A → B → C) → C). p [A] (λa:A. λb:B. a)";
  run_infer "snd" "ΛA. ΛB. λp:(∀C. (A → B → C) → C). p [B] (λa:A. λb:B. b)";
  ()

let ex_basic () =
  print_endline "\n\nBasics";
  run_infer "identity" "let id = ΛX. λx:X. x in id 42";
  run_infer "self app" "λx:(∀X. X → X). x x";
  run_infer "const" "ΛA. ΛB. λa:A. λb:B. a";
  ()

let () =
  ex_basic ();
  ex_bool ();
  ex_nat ();
  ex_pair ();
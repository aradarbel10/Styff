{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let print_err_pos lexbuf =
  let pos = lexbuf.lex_curr_p in
  "input:" ^ string_of_int pos.pos_lnum ^ ":" ^ string_of_int (pos.pos_cnum - pos.pos_bol + 1)

let classify_op (op : string) =
  match op.[0] with
  | ';' | '?' | ',' -> INFIXL0 op
  | '|' -> INFIXL1 op
  | '&' -> INFIXL2 op
  | '#' | '$' -> INFIX3 op
  | '=' | '<' | '>' | '~' -> INFIX4 op
  | ':' -> INFIXR5 op
  | '+' | '-' -> INFIXL6 op
  | '*' | '/' | '%' -> INFIXL7 op
  | '^' -> INFIX8 op
  | '@' | '.' | '!' -> INFIXL9 op
  | _ -> failwith "impossible; non operator symbol"

}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = (alpha) (alpha|'-'|'_'|digit|'\'')*
let unum = digit+
let symbol = ['!' '@' '#' '$' '%' '^' '&' '*' '-' '+' ';' '?' '/' '<' '>' ',' '~' '=' '.' ':' '|']
let operator = symbol+
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule read = parse
  | whitespace  { read lexbuf }
  | newline     { next_line lexbuf; read lexbuf }
  | "(*"        { read_comment lexbuf }
  | "infer"     { INFER }
  | "postulate" { POSTULATE }
  | "type"      { TYPE }
  | "data"      { DATA }
  | "where"     { WHERE }
  | '|'         { PIPE }
  | "match"     { MATCH }
  | "with"      { WITH }
  | "end"       { END }
  | "bool"      { BOOL }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "int"       { INT }
  | "∗"         { STAR }
  | "lam"       { LAM }
  | "λ"         { LAM }
  | '\\'        { LAM }
  | '.'         { DOT }
  | "let"       { LET }
  | "rec"       { REC }
  | '='         { EQ }
  | "in"        { IN }
  | "->"        { ARROW }
  | "→"         { ARROW }
  | '_'         { HOLE }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '['         { LBRACK }
  | ']'         { RBRACK }
  | ':'         { COLON }
  | ident       { IDENT (Lexing.lexeme lexbuf) }
  | operator    { classify_op (Lexing.lexeme lexbuf) }
  | unum        { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | _           { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof         { EOF }

(* TODO nested comments *)
and read_comment = parse
  | "*)"        { read lexbuf }
  | newline     { next_line lexbuf; read_comment lexbuf }
  | eof         { raise (SyntaxError "file ends before comment") }
  | _           { read_comment lexbuf }

{

let parse_buf lexbuf =
  try Ok (whole read lexbuf) with
    | SyntaxError reason ->
      let msg = print_err_pos lexbuf ^ ": " ^ reason in
      Error msg
    | Error ->
      let msg = print_err_pos lexbuf ^ ": syntax error" in
      Error msg

let parse_str str =
  let lexbuf = Lexing.from_string str in
  parse_buf lexbuf

let parse_file file =
  let handle = open_in file in
  let lexbuf = Lexing.from_channel handle in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file };
  let res = parse_buf lexbuf in
  close_in handle;
  res

}
{
open Lexing
open Parser
open Typecheck.Errors

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

let buf_rng (lexbuf : lexbuf) : Syntax.Common.src_range =
  Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf

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

let sep_ident (nm : string) : string list = String.split_on_char '.' nm

}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let single_ident = (alpha) (alpha|'-'|'_'|digit|'\'')*
let path_ident = single_ident ('.' single_ident)*
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
  | "print"     { PRINT }
  | "data"      { DATA }
  | "section"   { SECTION }
  | "where"     { WHERE }
  | '|'         { PIPE }
  | "match"     { MATCH }
  | "with"      { WITH }
  | "end"       { END }
  | "∗"         { STAR }
  | "Type"      { STAR }
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
  | '{'         { LCURLY }
  | '}'         { RCURLY }
  | ':'         { COLON }
  | single_ident{ SINGLE_IDENT (Lexing.lexeme lexbuf) }
  | path_ident  { IDENT (sep_ident (Lexing.lexeme lexbuf)) }
  | operator    { classify_op (Lexing.lexeme lexbuf) }
  | unum        { NUM (int_of_string (Lexing.lexeme lexbuf)) }
  | _           {
    let rng = buf_rng lexbuf in
    let lex = Lexing.lexeme lexbuf in
    raise (LexFailure (rng, lex))
    }
  | eof         { EOF }

(* TODO nested comments *)
and read_comment = parse
  | "*)"        { read lexbuf }
  | newline     { next_line lexbuf; read_comment lexbuf }
  | _           { read_comment lexbuf }

{

let parse_buf lexbuf =
  try whole read lexbuf with
  | Error -> raise (ParseFailure (SyntaxErr (buf_rng lexbuf)))

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
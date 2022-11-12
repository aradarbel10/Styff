%{
open Expr

type argument =
| InstArg of rtyp
| AppArg of rexpr

let rec unfoldApp (f : rexpr) (es : argument list) : rexpr =
  match es with
  | [] -> f
  | AppArg e :: rest -> unfoldApp (RApp (f, e)) rest
  | InstArg t :: rest -> unfoldApp (RInst (f, t)) rest
%}

%token EOF

%token <string> IDENT
%token <int> NUM
%token LAM ARROW TLAM FORALL LPAREN RPAREN LBRACK RBRACK COLON DOT LET EQ IN HOLE
%token BOOL NAT TRUE FALSE

%nonassoc WEAK
%nonassoc COLON
%right ARROW

%start whole
%type <rexpr> whole

%type <rexpr> expr
%type <rexpr> e_atom
%type <rtyp> typ
%type <rtyp> t_atom

%type <rtyp> bind_annot

%%
whole:
  | e=expr; EOF { e }

expr:
  | f=e_atom; es=list(arg) { unfoldApp f es }
  | e=expr; COLON; t=typ { RAnn (e, t) }
  | LAM; x=IDENT; t=option(bind_annot); DOT; e=expr
  (** [FUN] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)`.
      similar reason for most other "big" constructs. *)
    %prec WEAK { RLam (x, t, e) }
  | TLAM; x=IDENT; DOT; e=expr
    %prec WEAK { RTlam (x, None, e) }
  | LET; x=IDENT; EQ; e=expr; IN; r=expr
    %prec WEAK { RLet (x, e, r) }

arg:
  | LBRACK; t=typ; RBRACK { InstArg t }
  | e=e_atom { AppArg e }

bind_annot:
  | COLON; t=typ { t }

e_atom:
  | x=IDENT { RVar x }
  | LPAREN; e=expr; RPAREN { e }
  | n=NUM { RLit (`Nat n) }
  | TRUE { RLit (`Bool true) }
  | FALSE { RLit (`Bool false) }

typ:
  | t=t_atom { t }
  | a=typ; ARROW; b=typ { RArrow (a, b) }
  | FORALL; x=IDENT; DOT; e=typ
    %prec WEAK { RForall (x, e) }

t_atom:
  | x=IDENT { RQvar x }
  | LPAREN; t=typ; RPAREN { t }
  | BOOL { RBase `Bool }
  | NAT  { RBase `Nat  }
  | HOLE { RHole }
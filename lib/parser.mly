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

let rec unfoldTypApp (t1 : rtyp) (ts : rtyp list) : rtyp =
  match ts with
  | [] -> t1
  | t2 :: rest -> unfoldTypApp (RTapp (t1, t2)) rest
%}

%token EOF

%token <string> IDENT
%token <int> NUM
%token INFER TYPE
%token LAM ARROW TLAM FORALL LPAREN RPAREN LBRACK RBRACK COLON DOT LET EQ IN HOLE
%token BOOL NAT TRUE FALSE STAR

%nonassoc WEAK
%nonassoc COLON
%right ARROW

%start whole
%type <prog> whole

%type <rexpr> expr
%type <rexpr> e_atom
%type <rtyp> typ
%type <rtyp> t_atom

%type <rtyp> bind_annot

%%
whole:
  | stmts=list(stmt); EOF { stmts }

stmt:
  | LET; x=IDENT; t=option(bind_annot); EQ; e=expr { Def (x, t, e) }
  | TYPE; x=IDENT; k=option(bind_annotk); EQ; t=typ { TDef (x, k, t) }
  | INFER; x=IDENT; EQ; e=expr { Infer (x, e) }
  | INFER; TYPE; x=IDENT; EQ; t=typ { TInfer (x, t) }

expr:
  | f=e_atom; es=list(arg) { unfoldApp f es }
  | e=expr; COLON; t=typ { RAnn (e, t) }
  | LAM; x=IDENT; t=option(bind_annot); DOT; e=expr
  (** [FUN] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)`.
      similar reason for most other "big" constructs. *)
    %prec WEAK { RLam (x, t, e) }
  | TLAM; x=IDENT; k=option(bind_annotk); DOT; e=expr
    %prec WEAK { RTlam (x, k, e) }
  | LET; x=IDENT; t=option(bind_annot); EQ; e=expr; IN; r=expr
    %prec WEAK { RLet (x, t, e, r) }
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
  | t=t_atom; ts=list(t_atom) { unfoldTypApp t ts }
  | a=typ; ARROW; b=typ { RArrow (a, b) }
  | FORALL; x=IDENT; DOT; e=typ
    %prec WEAK { RForall (x, e) }
  | LAM; x=IDENT; k=option(bind_annotk); DOT; e=typ
    %prec WEAK { RTAbs (x, k, e) }
t_atom:
  | x=IDENT { RQvar x }
  | LPAREN; t=typ; RPAREN { t }
  | BOOL { RBase `Bool }
  | NAT  { RBase `Nat  }
  | HOLE { RHole }

kind:
  | STAR { RStar }
  | lk=kind; ARROW; rk=kind { RKArrow (lk, rk) }
bind_annotk:
  | COLON; k=kind { k }
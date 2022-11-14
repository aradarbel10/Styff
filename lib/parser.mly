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

type annotation =
| TypeAnnot of rtyp option
| KindAnnot of rkind option

let unfoldLamTele ((xs, ann) : name list * annotation) (e : rexpr) : rexpr =
  match ann with
  | TypeAnnot t -> List.fold_right (fun x e -> RLam  (x, t, e)) xs e
  | KindAnnot k -> List.fold_right (fun x e -> RTlam (x, k, e)) xs e
let rec unfoldLamTeles (teles : (name list * annotation) list) (e : rexpr) : rexpr =
  match teles with
  | [] -> e
  | tele :: teles ->
    let e' = unfoldLamTeles teles e in
    unfoldLamTele tele e'

let applyAnnot (e : rexpr) (t : rtyp option) : rexpr =
  match t with
  | None -> e
  | Some t -> RAnn (e, t)

%}

%token EOF

%token <string> IDENT
%token <int> NUM
%token <string> INFIXL0
%token <string> INFIXL1
%token <string> INFIXL2
%token <string> INFIX3 
%token <string> INFIX4 
%token <string> INFIXR5
%token <string> INFIXL6
%token <string> INFIXL7
%token <string> INFIX8 
%token <string> INFIXL9
%token INFER TYPE
%token LAM ARROW LPAREN RPAREN LBRACK RBRACK COLON DOT LET EQ IN HOLE
%token BOOL NAT TRUE FALSE STAR

%nonassoc WEAK
%nonassoc COLON
%right ARROW

%left INFIXL0
%left INFIXL1
%left INFIXL2
%nonassoc INFIX3 
%nonassoc INFIX4 
%right INFIXR5
%left INFIXL6
%left INFIXL7
%nonassoc INFIX8 
%left INFIXL9


%start whole
%type <prog> whole

%type <rexpr> expr
%type <rexpr> e_atom
%type <rtyp> typ
%type <rtyp> t_atom

%type <name list * annotation> tele

%type <string> infix_op

%type <rtyp> bind_annot
%type <rkind> bind_annotk

%%
whole:
  | stmts=list(stmt); EOF { stmts }

stmt:
  | LET; xtt=let_args; EQ; e=expr {
    let (x,teles,t) = xtt in
    Def (x, None, applyAnnot (unfoldLamTeles teles e) t)
    }
  | TYPE; x=IDENT; k=option(bind_annotk); EQ; t=typ { TDef (x, k, t) }
  | INFER; x=IDENT; EQ; e=expr { Infer (x, e) }
  | INFER; TYPE; x=IDENT; EQ; t=typ { TInfer (x, t) }

expr:
  | f=e_atom; es=list(arg) { unfoldApp f es }
  | e=expr; COLON; t=typ { RAnn (e, t) }
  | LAM; teles=lam_args; DOT; e=expr
  (** [FUN] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)`.
      similar reason for most other "big" constructs. *)
    %prec WEAK { unfoldLamTeles teles e (* RLam (x, t, e) *) }
  | LET; xtt=let_args; EQ; e=expr; IN; r=expr %prec WEAK {
    let (x,teles,t) = xtt in
    RLet (x, None, applyAnnot (unfoldLamTeles teles e) t, r)
    }
  | e1=expr; op=infix_op; e2=expr { RApp (RApp (RVar op, e1), e2) }
arg:
  | LBRACK; t=typ; RBRACK { InstArg t }
  | e=e_atom { AppArg e }

lam_args:
  | teles=nonempty_list(tele) { teles }
  | x=IDENT; COLON; t=typ { [[x], TypeAnnot (Some t)] }
let_args:
  | x=decl_name; teles=list(tele); t=option(bind_annot) { (x, teles, t) }
  | x1=IDENT; op=infix_op; x2=IDENT { (op, [[x1], TypeAnnot None; [x2], TypeAnnot None], None) }
%inline ttele:
  | LBRACK; xs=nonempty_list(IDENT); k=option(bind_annotk); RBRACK
    { (xs, KindAnnot k) }
tele:
  | t=ttele { t }
  | x=IDENT { ([x], TypeAnnot None) }
  | LPAREN; xs=nonempty_list(IDENT); COLON; t=typ; RPAREN { (xs, TypeAnnot (Some t)) }

bind_annot:
  | COLON; t=typ { t }
e_atom:
  | x=IDENT { RVar x }
  | LPAREN; e=expr; RPAREN { e }
  | n=NUM { RLit (`Nat n) }
  | TRUE { RLit (`Bool true) }
  | FALSE { RLit (`Bool false) }

%inline decl_name:
  | x=IDENT { x }
  | LPAREN; op=infix_op; RPAREN { op }
%inline infix_op:
  | op=INFIXL0 { op }
  | op=INFIXL1 { op }
  | op=INFIXL2 { op }
  | op=INFIX3  { op }
  | op=INFIX4  { op }
  | op=INFIXR5 { op }
  | op=INFIXL6 { op }
  | op=INFIXL7 { op }
  | op=INFIX8  { op }
  | op=INFIXL9 { op }

typ:
  | t=t_atom; ts=list(t_atom) { unfoldTypApp t ts }
  | a=typ; ARROW; b=typ { RArrow (a, b) }
  | LBRACK; x=IDENT; option(bind_annotk); RBRACK; ARROW; t=typ
    { RForall (x, t) }
  | LAM; x=IDENT; k=option(bind_annotk); DOT; e=typ
    %prec WEAK { RTAbs (x, k, e) }
  | t1=typ; op=infix_op; t2=typ { RTapp (RTapp (RQvar op, t1), t2) }
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
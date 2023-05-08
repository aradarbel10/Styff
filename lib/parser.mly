%{
open Syntax.Raw

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

let unfoldLamTele ((xs, ann) : string list * annotation) (e : rexpr) : rexpr =
  match ann with
  | TypeAnnot t -> List.fold_right (fun x e -> RLam  (x, t, e)) xs e
  | KindAnnot k -> List.fold_right (fun x e -> RTlam (x, k, e)) xs e
let rec unfoldLamTeles (teles : (string list * annotation) list) (e : rexpr) : rexpr =
  match teles with
  | [] -> e
  | tele :: teles ->
    let e' = unfoldLamTeles teles e in
    unfoldLamTele tele e'

let rec joinTele : string list * annotation -> rparam list = function
| [], _ -> []
| x::xs, TypeAnnot t -> RParam  (x, t) :: joinTele (xs, TypeAnnot t)
| x::xs, KindAnnot k -> RTParam (x, k) :: joinTele (xs, KindAnnot k)

let joinTeles : (string list * annotation) list -> rparam list =
  fun teles -> List.concat @@ List.map joinTele teles

%}

%token EOF

%token <string> SINGLE_IDENT
%token <Syntax.Common.name> IDENT
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
%token INFER TYPE PRINT POSTULATE DATA SECTION OPEN ALIAS WHERE PIPE MATCH WITH END
%token LAM ARROW LPAREN RPAREN LCURLY RCURLY COLON DOT LET REC EQ IN HOLE
%token STAR

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

%type <string list * annotation> tele

%type <string> bnd_name
%type <name> qual_name

%type <string> infix_op

%type <rtyp> bind_annot
%type <rkind> bind_annotk

%%
whole:
  | stmts=list(stmt); EOF { stmts }

stmt:
  | LET; rc=option(REC); xtt=let_args; EQ; e=expr {
    let (x,teles,t) = xtt in
    Def (Option.is_some rc, x, joinTeles teles, t, e)
    }
  | TYPE; x=bnd_name; k=option(bind_annotk); EQ; t=typ { TDef (x, k, t) }
  | INFER; x=bnd_name; EQ; e=expr { Infer (x, e) }
  | INFER; TYPE; x=bnd_name; EQ; t=typ { TInfer (x, t) }
  | PRINT; e=expr { Print e }
  | POSTULATE; x=bnd_name; COLON; t=typ { Postulate (x, t) }
  | POSTULATE; TYPE; x=bnd_name; COLON; k=kind { PostulateType (x, k) }
  | d=data_decl { d }
  | o=option(OPEN); SECTION; x=bnd_name; WHERE; stmts=list(stmt); END
    { Section ((if Option.is_some o then `opened else `closed), x, stmts) }
  | OPEN; x=qual_name { OpenSection x }
  | ALIAS; x=bnd_name; EQ; y=qual_name { Alias (x, y) }

unloc_expr:
  | f=e_atom; es=list(arg) { unfoldApp f es }
  | e=expr; COLON; t=typ { RAnn (e, t) }
  | LAM; teles=lam_args; DOT; e=expr
  (** [FUN] needs weak precedence to ensure `λx . e : t` == `λx . (e : t)`.
      similar reason for most other "big" constructs. *)
    %prec WEAK { unfoldLamTeles teles e (* RLam (x, t, e) *) }
  | LET; rc=option(REC); xtt=let_args; EQ; e=expr; IN; r=expr %prec WEAK {
    let (x,teles,t) = xtt in
    RLet (Option.is_some rc, x, joinTeles teles, t, e, r)
    }
  | e1=expr; op=infix_op; e2=expr { RApp (RApp (RVar [op], e1), e2) }
%inline expr:
  | e=unloc_expr { RSrcRange ($loc, e) }
arg:
  | LCURLY; t=typ; RCURLY { InstArg t }
  | e=e_atom { AppArg e }

lam_args:
  | teles=nonempty_list(tele) { teles }
  | x=bnd_name; COLON; t=typ { [[x], TypeAnnot (Some t)] }
let_args:
  | x=bnd_name; teles=list(tele); t=option(bind_annot) { (x, teles, t) }
  | x1=bnd_name; op=infix_op; x2=bnd_name { (op, [[x1], TypeAnnot None; [x2], TypeAnnot None], None) }
%inline ttele:
  | LCURLY; xs=nonempty_list(bnd_name); k=option(bind_annotk); RCURLY
    { (xs, KindAnnot k) }
tele:
  | t=ttele { t }
  | x=bnd_name { ([x], TypeAnnot None) }
  | LPAREN; xs=nonempty_list(bnd_name); COLON; t=typ; RPAREN { (xs, TypeAnnot (Some t)) }

bind_annot:
  | COLON; t=typ { t }
e_atom:
  | x=qual_name { RVar x }
  | LPAREN; e=expr; RPAREN { e }
  | n=NUM { RLit (`Int n) }
  | MATCH; e=e_atom; WITH; bs=list(branch); END { RMatch (e, bs) }

%inline bnd_name:
  | x=SINGLE_IDENT { x }
  | LPAREN; op=infix_op; RPAREN { op }
%inline qual_name:
  | x=IDENT { x }
  | x=bnd_name { [x] }
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
  | LCURLY; x=bnd_name; k=option(bind_annotk); RCURLY; ARROW; t=typ
    { RForall (x, k, t) }
  | LAM; x=bnd_name; k=option(bind_annotk); DOT; e=typ
    %prec WEAK { RTAbs (x, k, e) }
  | LET; x=bnd_name; k=option(bind_annotk); EQ; t1=typ; IN; t2=typ
    %prec WEAK { RTLet (x, k, t1, t2) }
  | t1=typ; op=infix_op; t2=typ { RTapp (RTapp (RQvar [op], t1), t2) }
t_atom:
  | x=qual_name { RQvar x }
  | LPAREN; t=typ; RPAREN { t }
  | HOLE { RHole }

kind:
  | STAR { RStar }
  | lk=kind; ARROW; rk=kind { RKArrow (lk, rk) }
  | LPAREN; k=kind; RPAREN { k }
bind_annotk:
  | COLON; k=kind { k }


tparam:
  | x=bnd_name { RTParam (x, None) }
  | LPAREN; x=bnd_name; COLON; k=kind; RPAREN { RTParam (x, Some k) }

data_decl:
  | DATA; x=bnd_name; tps=list(tparam); COLON; k=kind; WHERE; cs=list(ctor_decl)
    { DataDecl (x, tps, k, cs) }
ctor_decl:
  | PIPE; x=bnd_name; COLON; t=typ
    { RCtor {nam = x; t = t} }

branch:
  | PIPE; p=pattern; DOT; e=expr { (p, e) }
pattern:
  | ctor=qual_name; args=list(pattern_arg); { RPCtor (ctor, args) }
  | lhs=bnd_name; op=infix_op; rhs=bnd_name { RPCtor ([op], [PVar lhs; PVar rhs]) }
pattern_arg:
  | v=bnd_name { PVar v }
  | LCURLY; v=bnd_name; RCURLY { PTvar v }
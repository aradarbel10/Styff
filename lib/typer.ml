open Batteries.Uref
open Util
open Pretty
open Expr
open Eval
open Unif

module Fresh : sig
  val uniquei : int
  val freshen : name -> name
  val fresh : mask -> name -> typ
  val freshk : name -> kind
end = struct
  let freshi = ref (-1)
  let uniquei = freshi := !freshi + 1; !freshi
  let freshen (x : name) = x ^ string_of_int uniquei
  let fresh (msk : mask) (x : name) = Inserted (uref (Unsolved (freshen x)), msk)
  let freshk (x : name) = KVar (uref (KUnsolved (freshen x)))
end
open Fresh

type ctx = (name * vtyp) list
type tctx = (name * kind) list
type scene = {
  ctx : ctx;

  height : lvl;
  tctx : tctx;
  env : env;
  msk : mask;
}

let empty_scene : scene = {ctx = []; height = Lvl 0; tctx = []; env = []; msk = []}
let names scn = List.map fst scn.ctx
let tps scn = List.map fst scn.tctx

let assume (scn : scene) (x : name) (t : vtyp) : scene =
  {scn with
    ctx = (x, t) :: scn.ctx;
  }

let assume_typ (scn : scene) (x : name) (k : kind) : scene =
  {scn with
    height = inc scn.height;
    tctx = (x, k) :: scn.tctx;
    env = (x, vqvar scn.height) :: scn.env;
    msk = true :: scn.msk;
  }

let define_typ (scn : scene) (x : name) (t : vtyp) (k : kind) : scene =
  {scn with
    height = inc scn.height;
    tctx = (x, k) :: scn.tctx;
    env = (x, t) :: scn.env;
    msk = false :: scn.msk;
  }

exception UndefinedVar of name
exception UndefinedQVar of name
exception Unexpected of typ
exception NoFirstClassTypes of name
exception UnexpectedHigherKind

let unify' (scn : scene) (t : vtyp) (t' : vtyp) =
  try unify scn.height t t' with
  | Ununifiable ->
    let nms = List.map fst scn.env in
    let str  = string_of_vtype nms t  in
    let str' = string_of_vtype nms t' in
    raise (Failure ("unable to unify " ^ str ^ " ~/~ " ^ str'))

let type_of_lit : lit -> base = function
| `Int _ -> `Int
| `Bool _ -> `Bool

let clos_of (scn : scene) (t : vtyp) : clos =
  {env = scn.env; bdr = B (quote (inc scn.height) t)}

let insert (scn : scene) (e, t : expr * vtyp) : expr * vtyp =
  match force t with
  | VForall (x, bod) ->
    let m = fresh scn.msk x in
    let m' = eval scn.env m in
    (Inst (e, m), capp x bod m')
  | t -> (e, t)
let insert_unless (scn : scene) (e, t : expr * vtyp) : expr * vtyp =
  match e with
  | Tlam _ -> (e, t)
  | _ -> insert scn (e, t)

let rec lower_kind : rkind -> kind = function
| RStar -> Star
| RKArrow (lk, rk) -> KArrow (lower_kind lk, lower_kind rk)

let rec kind_of (scn : scene) : rtyp -> typ * kind = function
| RArrow (lt, rt) -> (Arrow (is_type scn lt, is_type scn rt), Star)
| RBase b -> (Base b, Star)
| RTapp (t1, t2) ->
  let (t1, k1) = kind_of scn t1 in
  let (t2, k2) = kind_of scn t2 in
  let kv = freshk "k" in
  unify_kinds k1 (KArrow (k2, kv));
  (Tapp (t1, t2), kv)
| RTLet (x, k, t, rest) ->
  let (scn, t, vt, k) = infer_let_type scn x k t in
  let (rest, krest) = kind_of (define_typ scn x vt k) rest in
  (TLet (x, t, rest), krest)
| RTAbs (x, None, t) ->
  let kv = freshk "k" in
  let (t, k) = kind_of (assume_typ scn x kv) t in
  (t, KArrow (kv, k))
| RTAbs (x, Some k, t) ->
  let (t, k') = kind_of scn (RTAbs (x, None, t)) in
  let k = lower_kind k in
  unify_kinds k k';
  (t, k)
| RForall (x, t) ->
  let xk = freshk x in
  let t = is_type (assume_typ scn x xk) t in
  (Forall (x, B t), Star)
| RHole -> (fresh scn.msk "t", Star)
| RQvar x ->
  match assoc_idx x scn.tctx with
  | Some (i, k) -> (Qvar (Idx i), k)
  | None -> raise (UndefinedQVar x)
and is_type (scn : scene) (t : rtyp) : typ =
  let (t, k) = kind_of scn t in
  match forcek k with
  | Star -> t
  | KVar kv -> unify_kinds (KVar kv) Star; t
  | _ -> raise UnexpectedHigherKind
and infer_let_type (scn : scene) (x : name) (_ : rkind option) (t : rtyp) : scene * typ * vtyp * kind =
  let (t, k) = kind_of scn t in
  let vt = eval scn.env t in
  (define_typ scn x vt k, t, vt, k)


let rec type_of (scn : scene) : rexpr -> expr * vtyp = function
| RAnn (e, t) ->
  let (e, te) = insert_unless scn @@ type_of scn e in
  let t = eval scn.env (is_type scn t) in
  unify' scn t te;
  (e, te)

| RVar x ->
  begin match assoc_idx x scn.ctx with
  | None -> raise (UndefinedVar x)
  | Some (i, t) -> (Var (Idx i), t)
  end

| RLam (x, None, e) ->
  let tx = eval scn.env (fresh scn.msk x) in
  let (e, te) = type_of (assume scn x tx) e in
  (Lam (x, quote scn.height tx, e), VArrow (tx, te))

| RLam (x, Some tx, e) ->
  let tx = eval scn.env (is_type scn tx) in
  let (e, te) = type_of (assume scn x tx) e in
  (Lam (x, quote scn.height tx, e), VArrow (tx, te))

| RTlam (x, None, e) ->
  let k = freshk "k" in
  let (e, te) = insert_unless scn @@ type_of (assume_typ scn x k) e in
  (Tlam (x, e), VForall (x, clos_of scn te))

| RTlam (x, Some k, e) ->
  let k = lower_kind k in
  let (e, te) = insert_unless scn @@ type_of (assume_typ scn x k) e in
  (Tlam (x, e), VForall (x, clos_of scn te))

| RApp (e1, e2) ->
  let (e1, te1) = insert scn @@ type_of scn e1 in
  let (e2, te2) = type_of scn e2 in
  let ret = eval scn.env (fresh scn.msk "r") in
  unify' scn te1 (VArrow (te2, ret));
  (App (e1, e2), ret)

| RInst (e, t) ->
  let (e, te) = type_of scn e in
  let (t, k) = kind_of scn t in

  let x = freshen "x" in
  let ret = fresh (assume_typ scn x k).msk "ret" in
  let clos = {env = scn.env; bdr = B ret} in

  unify' scn te (VForall (x, clos));
  (Inst (e, t), capp x clos (eval scn.env t))

| RLet (rc, x, t, e, rest) ->
  let (scn, e, te) = infer_let scn rc x t e in
  let (rest, trest) = type_of (assume scn x te) rest in
  (Let (rc, x, quote scn.height te, e, rest), trest)

| RLit n ->
  (Lit n, VBase (type_of_lit n))

and infer_let (scn : scene) (rc : bool) (x : name) (t : rtyp option) (e : rexpr) : scene * expr * vtyp =
  (* if the binding is recursive, extend the scene with it *)
  let scn = if rc then
    let t_all = match t with
    | None -> fresh scn.msk x
    | Some t_all -> is_type scn t_all
    in assume scn x (eval scn.env t_all)
  else
    scn
  in
  let (e, te) = type_of scn e in
  begin match t with
  | Some t' ->
    let t' = eval scn.env (is_type scn t') in
    unify' scn te t'
  | None -> ()
  end;
  (assume scn x te, e, te)
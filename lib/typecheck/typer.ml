open Util
open Syntax.Raw
open Syntax.Core
open Pretty
open Eval
open Unif
open Scene
open Pattern

exception UndefinedVar of name
exception UndefinedQVar of name
exception Unexpected of typ
exception NoFirstClassTypes of name
exception UnexpectedHigherKind

(* wrapper for [unify] to catch errors *)
let unify' (scn : scene) (t : vtyp) (t' : vtyp) =
  try unify scn.height Global t t' with
  | Ununifiable ->
    let nms = List.map (fun (x, _, _, _) -> x) scn.env in
    let str  = string_of_vtype nms t  in
    let str' = string_of_vtype nms t' in
    raise (Failure ("unable to unify " ^ str ^ " ~/~ " ^ str'))

let infer_lit : lit -> base = function
| `Int _ -> `Int
| `Bool _ -> `Bool

(* construct a closure around a value *)
let clos_of (scn : scene) (t : vtyp) (k : kind) : clos =
  {knd = k; env = scn.env; bdr = B (quote (inc scn.height) t)}

(* construct lambdas around a ctor to make it fully saturated
   this is a special case of uncurrying, but the backend currently doesn't do that *)
let lams_ctor (hi' : lvl) (Idx ctor : idx) (params : vparam list) =
  let rec args_of_params : vparam list -> arg list * int * int = function
  | [] -> [], 0, 0
  | `TmParam _ :: ps ->
    let ps, tpdepth, tmdepth = args_of_params ps in
    `TmArg (Var (Idx tmdepth)) :: ps, tpdepth, tmdepth+1
  | `TpParam _ :: ps ->
    let ps, tpdepth, tmdepth = args_of_params ps in
    `TpArg (Qvar (Idx tpdepth)) :: ps, tpdepth+1, tmdepth
  in

  let rec go (hi : lvl) : vparam list -> expr = function
  | [] ->
    let args, _, tmdepth = args_of_params params in
    Ctor (Idx (ctor + tmdepth), args)
  | `TmParam t :: ps ->
    let a = freshen "a" in
    Lam (a, quote hi t, go hi ps)
  | `TpParam k :: ps ->
    let b = freshen "b" in
    Tlam (b, k, go (inc hi) ps)
  in go hi' params


(* to allow implicit instantiation, we sometimes insert an application for the user *)
let insert (scn : scene) (e, t : expr * vtyp) : expr * vtyp =
  match force t with
  | VForall (x, bod) ->
    let m = fresh (mask_of scn) x in
    let m' = eval scn.env m in
    (Inst (e, m), capp x bod m')
  | t -> (e, t)
let insert_unless (scn : scene) (e, t : expr * vtyp) : expr * vtyp =
  match e with
  | Tlam _ -> (e, t)
  | _ -> insert scn (e, t)

(* embed raw language kinds ↪ core language kinds *)
let rec lower_kind : rkind -> kind = function
| RStar -> Star
| RKArrow (lk, rk) -> KArrow (lower_kind lk, lower_kind rk)

(* elaboration:
   opposed to plain type checking/inference, we want to translate
   the raw language to a more explicit core language.
*)

(* given a type, return its core representation and infer its kind *)
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
  (TLet (x, k, t, rest), krest)
| RTAbs (x, xk, t) ->
  let xk = maybe_rkind "k" xk in
  let (t, tk) = kind_of (assume_typ scn x xk `EUnsolved) t in
  (TAbs (x, xk, B t), KArrow (xk, tk))
| RForall (x, xk, t) ->
  let xk = maybe_rkind "k" xk in
  let t = is_type (assume_typ scn x xk `EUnsolved) t in
  (Forall (x, xk, B t), Star)
| RHole -> (fresh (mask_of scn) "t", Star)
| RQvar x ->
  match assoc_idx x scn.tctx with
  | Some (i, k) -> (Qvar (Idx i), k)
  | None -> raise (UndefinedQVar x)
and is_type (scn : scene) (t : rtyp) : typ =
  let (t, k) = kind_of scn t in
  unify_kinds k Star;
  t
and maybe_rtyp (scn : scene) (x : name) : rtyp option -> typ = function
| Some t -> is_type scn t
| None -> fresh (mask_of scn) (freshen x)
and maybe_rkind (x : name) : rkind option -> kind = function
| Some k -> lower_kind k
| None -> freshk (freshen x)

and infer_let_type (scn : scene) (x : name) (_ : rkind option) (t : rtyp) : scene * typ * vtyp * kind =
  let (t, k) = kind_of scn t in
  let vt = eval scn.env t in
  (define_typ scn x vt k, t, vt, k)

(* given an expression, return its core representation and infer its type *)
let rec infer (scn : scene) : rexpr -> expr * vtyp = function
| RAnn (e, t) ->
  let t = eval scn.env (is_type scn t) in
  let e = check scn e t in
  (e, t)

| RVar x ->
  begin match assoc_idx x scn.ctx with
  | None -> raise (UndefinedVar x)
  | Some (i, t) ->
    match List.assoc_opt x scn.ctor_params with
    | None -> Var (Idx i), t
    | Some params -> insert scn (lams_ctor scn.height (Idx i) params, t)
  end

| RLam (x, xt, e) ->
  let xt = eval scn.env (maybe_rtyp scn "x" xt) in
  let (e, te) = infer (assume scn x xt) e in
  (Lam (x, quote scn.height xt, e), VArrow (xt, te))

| RTlam (x, xk, e) ->
  let xk = maybe_rkind "k" xk in
  let (e, te) = insert_unless scn @@ infer (assume_typ scn x xk `EUnsolved) e in
  (Tlam (x, xk, e), VForall (x, clos_of scn te xk))

| RApp (e1, e2) ->
  let (e1, te1) = insert scn @@ infer scn e1 in
  let (lt, rt) = begin match force te1 with
  | VArrow (lt, rt) -> (lt, rt)
  | te1 ->
    let lt = eval scn.env (fresh (mask_of scn) "l") in
    let rt = eval scn.env (fresh (mask_of scn) "r") in
    unify' scn te1 (VArrow (lt, rt));
    (lt, rt)
  end in
  let e2 = check scn e2 lt in
  (App (e1, e2), rt)

| RInst (e, t) ->
  let (e, te) = infer scn e in
  let (t, k) = kind_of scn t in

  let x = freshen "x" in
  let ret = fresh (mask_of (assume_typ scn x k `ESolved)) "ret" in
  let clos = {knd = k; env = scn.env; bdr = B ret} in

  unify' scn te (VForall (x, clos));
  (Inst (e, t), capp x clos (eval scn.env t))

| RLet (rc, x, ps, t, e, rest) ->
  let (scn, e, te) = infer_let scn rc x ps t e in
  let (rest, trest) = infer (assume scn x te) rest in
  (Let (rc, x, quote scn.height te, e, rest), trest)

| RMatch (scrut, branches) ->
  check_coverage scn branches;
  let (scrut, scrut_typ) = infer scn scrut in
  let t = eval scn.env (fresh (mask_of scn) "t") in
  let branch_typs = List.map (fun (pat, branch) -> infer_branch scn scrut_typ pat branch) branches in
  ignore @@ List.map (fun (_, _, t') -> unify' scn t t') branch_typs;
  (Match (scrut, List.map (fun (p, e, _) -> (p, e)) branch_typs), t)

| RLit n ->
  (Lit n, VBase (infer_lit n))

and check (scn : scene) (e : rexpr) (t : vtyp) : expr = match e, force t with
| RLam (x, Some xt, e), VArrow (lt, rt) ->
  let xt = eval scn.env (is_type scn xt) in
  unify' scn xt lt;
  check scn (RLam (x, None, e)) (VArrow (lt, rt))
  
| RLam (x, None, e), VArrow (lt, rt) ->
  let e = check (assume scn x lt) e rt in
  Lam (x, quote scn.height lt, e)

| RTlam (x, Some _, e), VForall (x', c) ->
  (*todo unify k with the kind of x'*)
  check scn (RTlam (x, None, e)) (VForall (x', c))

| RTlam (x, None, e), VForall (x', c) ->
  let ret_typ = cinst_at scn.height x' c in
  let e = check (assume_typ scn x c.knd `EUnsolved) e ret_typ in
  Tlam (x, c.knd, e)

| RLet (rc, x, ps, t, e, rest), t_rest ->
  let (scn, e, te) = infer_let scn rc x ps t e in
  let rest = check scn rest t_rest in
  Let (rc, x, quote scn.height te, e, rest)

| RMatch (scrut, branches), ret_typ ->
  check_coverage scn branches;
  let (scrut, scrut_typ) = infer scn scrut in
  let branch_typs = List.map (fun (pat, branch) -> check_branch scn scrut_typ pat branch ret_typ) branches in
  Match (scrut, branch_typs)
  
| e, actual_t ->
  let (e, expected_t) = insert_unless scn @@ infer scn e in
  unify' scn expected_t actual_t;
  e

(* given a scene, a list of parameters, and a return type, return
- a scene transformer, binding the new params into scope
- the whole type of the function being defined
- just the return type of the function being defined (evaluated under the new scene)
- a HOF to wrap the definition's body with lambdas bindings its params
*)
and process_params (scn : scene) (ps : rparam list) (ret_typ : rtyp option) : (scene -> scene) * typ * vtyp * (expr -> expr) =
  match ps with
  | [] ->
    let ret_typ = maybe_rtyp scn "ret" ret_typ in
    ((fun s -> s), ret_typ, eval scn.env ret_typ, fun e -> e)
  | RParam (x, t) :: ps ->
    let t = maybe_rtyp scn x t in
    let vt = eval scn.env t in
    let scn = assume scn x vt in
    let (mkscn, all_typ, ret_typ, lams) = process_params scn ps ret_typ in
    ((fun s -> mkscn (assume s x vt)), Arrow (t, all_typ), ret_typ, fun e -> Lam (x, t, lams e))
  | RTParam (x, k) :: ps ->
    let k = maybe_rkind x k in
    let scn = assume_typ scn x k `EUnsolved in
    let (mkscn, all_typ, ret_typ, lams) = process_params scn ps ret_typ in
    ((fun s -> mkscn (assume_typ s x k `EUnsolved)), Forall (x, k, B all_typ), ret_typ, fun e -> Tlam (x, k, lams e))

(* compute the scene representing a [let]'s inner scope, with all parameters bound.
  also returns the entire binding's type, and just its return type (without parameters)
*)
and scene_of_let (scn : scene) (rc : bool) (x : name) (ps : rparam list) (ret_typ : rtyp option) : scene * vtyp * vtyp * (expr -> expr) =
  let (mkscn, all_typ, ret_typ, lams) = process_params scn ps ret_typ in
  let all_typ = eval scn.env all_typ in
  (* if the binding is recursive, extend the scene with it *)
  let inner_scn = mkscn @@ if rc then assume scn x all_typ else scn in
  (inner_scn, all_typ, ret_typ, lams)

and infer_let (scn : scene) (rc : bool) (x : name) (ps : rparam list) (t : rtyp option) (e : rexpr) : scene * expr * vtyp =
  let (inner_scn, all_typ, ret_typ, lams) = scene_of_let scn rc x ps t in
  let e = lams @@ check inner_scn e ret_typ in
  (assume scn x all_typ, e, all_typ)

and infer_branch (scn : scene) (scrut_typ : vtyp) (pat : rpattern) (branch : rexpr) : pattern * expr * vtyp =
  let (pat, scn) = scene_of_pattern scn scrut_typ pat in
  let (branch, branch_typ) = infer scn branch in
  (pat, branch, branch_typ)

and check_branch (scn : scene) (scrut_typ : vtyp) (pat : rpattern) (branch : rexpr) (ret_typ : vtyp) : pattern * expr =
  let (pat, scn) = scene_of_pattern scn scrut_typ pat in
  let ret_typ = vnorm scn.env ret_typ in
  let branch = check scn branch ret_typ in
  (pat, branch)

(* get the last type in a chain of arrows (including foralls as arrows), and a list of the params *)
let rec return_type (hi : lvl) : vtyp -> vtyp * vparam list = function
| VArrow (lt, rt) ->
  let ret, params = return_type hi rt
  in ret, `TmParam lt :: params
| VForall (x, c) ->
  let ret, params = return_type (inc hi) (cinst_at hi x c)
  in ret, `TpParam c.knd :: params
| t -> t, []

(* modify the scene with a new data declaration and its constructors *)
exception BadCtorReturn
let declare_ctor (parent : lvl) (scn : scene) (RCtor {nam; t} : rctor) : scene =
  let t = is_type scn t in
  let vt = eval scn.env t in
  let rett = return_type scn.height (eval scn.env t) in (* ctor's return type must be the data it belongs to *)
  match rett with
  | VNeut (VQvar i, _), params when parent = i ->
    define_ctor_params (assume scn nam vt) nam params
  | _ -> raise BadCtorReturn
let declare_data (scn : scene) (x : name) (k : rkind option) (ctors : rctor list) =
  let k = maybe_rkind (freshen "k") k in
  let parent = scn.height in (* slightly hacky: get the height before [assume_typ], will be the lvl of the type just defined *)
  let scn = assume_typ scn x k `ESolved in
  let scn = List.fold_left (declare_ctor parent) scn ctors in
  define_ctors scn x (List.map (fun (RCtor {nam; _}) -> nam) ctors)
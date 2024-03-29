open Syntax.Raw
open Syntax.Core
open Pretty
open Eval
open Unif
open Scene
open Pattern

open Errors

(* wrapper for [unify] to catch errors *)
let unify' (scn : scene) (expect : vtyp) (actual : vtyp) =
  try unify scn.height Global expect actual with
  | Ununifiable ->
    let expect_str = string_of_vtype scn.scope expect in
    let actual_str = string_of_vtype scn.scope actual in
    elab_complain scn (UnificationFailure (expect_str, actual_str))

let infer_lit : lit -> base = function
| `Int _ -> `Int
| `Bool _ -> `Bool

(* construct a closure around a value *)
let clos_of (scn : scene) (t : vtyp) (k : kind) : clos =
  {knd = k; env = scn.env; bdr = B (quote (inc scn.height) t)}

(* todo: rewrite [lam_ctor] and [saturate], these recursions are ugly and there must be a cleaner way *)

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
    let a = freshen_str "a" in
    Lam (a, quote hi t, go hi ps)
  | `TpParam k :: ps ->
    let b = freshen_str "b" in
    Tlam (b, k, go (inc hi) ps, `inserted)
  in go hi' params

(* make sure the function is fully applied to all its arguments by wrapping it in lambdas *)
let saturate (hi : lvl) (typ : vtyp) (fn : int -> arg list -> expr) : expr =
  let rec args_of_typ (hi : lvl) (typ : vtyp) : arg list * [`TmParam of typ | `TpParam of kind] list * int * int =
    match force typ with
    | VArrow(lt, rt) ->
      let args, ps, tpdepth, tmdepth = args_of_typ hi rt in
      `TmArg (Var (Idx tmdepth)) :: args, `TmParam (quote hi lt) :: ps, tpdepth, tmdepth+1
    | VForall (_, clos) ->
      let rt = cinst_at hi clos in
      let args, ps, tpdepth, tmdepth = args_of_typ (inc hi) rt in
      `TpArg (Qvar (Idx tpdepth)) :: args, `TpParam clos.knd :: ps, tpdepth+1, tmdepth
    | _ -> [], [], 0, 0
  in
  let args, params, _, _ = args_of_typ hi typ in

  let rec go (hi_shift : int) : [`TmParam of typ | `TpParam of kind] list -> expr = function
  | [] -> fn hi_shift args
  | `TmParam t :: ps ->
    let a = freshen_str "a" in
    Lam (a, t, go (hi_shift + 1) ps)
  | `TpParam k :: ps ->
    let b = freshen_str "b" in
    Tlam (b, k, go hi_shift ps, `inserted)
  in go 0 params

(* to allow implicit instantiation, we sometimes insert an application for the user *)
let rec insert (scn : scene) (e, t : expr * vtyp) : expr * vtyp =
  match force t with
  | VForall (x, bod) ->
    let m = fresh (mask_of scn) x in
    let m' = eval scn.env m in
    insert scn (Inst (e, m), capp bod m')
  | t -> (e, t)
let insert_unless (scn : scene) (e, t : expr * vtyp) : expr * vtyp =
  match e with
  | Tlam (_, _, _, `user) -> (e, t) (* don't immediately apply user's lambdas! *)
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
  let (rest, krest) = kind_of (fst @@ define_typ x vt k scn) rest in
  (TLet (x, k, t, rest), krest)
| RTAbs (x, xk, t) ->
  let xk = maybe_rkind "k" xk in
  let (t, tk) = kind_of (fst @@ assume_typ x xk `EUnsolved scn) t in
  (TAbs (x, xk, B t), KArrow (xk, tk))
| RForall (x, xk, t) ->
  let xk = maybe_rkind "k" xk in
  let t = is_type (fst @@ assume_typ x xk `EUnsolved scn) t in
  (Forall (x, xk, B t), Star)
| RHole -> (fresh (mask_of scn) "t", Star)
| RQvar x -> begin match x with
  | ["builtin"; "int"] -> Base `Int, Star
  | ["builtin"; "bool"] -> Base `Bool, Star
  | x -> match lookup_type x scn with
    | None -> elab_complain scn (UndefinedQVar x)
    | Some (i, k) -> Qvar i, k
  end
and is_type (scn : scene) (t : rtyp) : typ =
  let (t, k) = kind_of scn t in
  unify_kinds k Star;
  t
and maybe_rtyp (scn : scene) (x : string) : rtyp option -> typ = function
| Some t -> is_type scn t
| None -> fresh (mask_of scn) x
and maybe_rkind (x : string) : rkind option -> kind = function
| Some k -> lower_kind k
| None -> freshk x

and infer_let_type (scn : scene) (x : string) (_ : rkind option) (t : rtyp) : scene * typ * vtyp * kind =
  let (t, k) = kind_of scn t in
  let vt = eval scn.env t in
  let t = quote scn.height vt in
  (fst @@ define_typ x vt k scn, t, vt, k)

(* intermediary type used in inference lookahead *)
type split_arg = [`app of rexpr | `inst of rtyp]
type splitted =
| Ctor of idx * vparam list * split_arg list
| Expr of expr * vtyp

(* given an expression, return its core representation and infer its type *)
let rec infer (scn : scene) : rexpr -> expr * vtyp = function
| RSrcRange (rng, e) -> scn.range <- rng; infer scn e

| RAnn (e, t) ->
  let t = eval scn.env (is_type scn t) in
  let e = check scn e t in
  (e, t)

| RVar x ->
  begin match x with
  | ["builtin"; "int-add"] ->
    let t = VArrow (VBase `Int, VArrow (VBase `Int, VBase `Int)) in
    let e = saturate scn.height t (fun _ -> function
    | [`TmArg e1; `TmArg e2] -> BinOp (e1, IntAdd, e2)
    | _ -> failwith "absurd!")
    in e, t
  | ["builtin"; "int-mul"] ->
    let t = VArrow (VBase `Int, VArrow (VBase `Int, VBase `Int)) in
    let e = saturate scn.height t (fun _ -> function
    | [`TmArg e1; `TmArg e2] -> BinOp (e1, IntMul, e2)
    | _ -> failwith "absurd!")
    in e, t
  | ["builtin"; "bool-true"] -> Lit (`Bool true), VBase `Bool
  | ["builtin"; "bool-false"] -> Lit (`Bool false), VBase `Bool
  | x -> match lookup_term x scn with
    | None -> elab_complain scn (UndefinedVar x)
    | Some (Idx i, t, ECtor {parent = _}) ->
      saturate scn.height t (fun shift args -> Ctor (Idx (i + shift), args)), t
    | Some (i, t, EVar) -> Var i, t
  end

| RLam (x, xt, e) ->
  let xt = eval scn.env (maybe_rtyp scn "x" xt) in
  let (e, te) = infer (fst @@ assume x xt scn) e in
  (Lam (x, quote scn.height xt, e), VArrow (xt, te))

| RTlam (x, xk, e) ->
  let xk = maybe_rkind "k" xk in
  let (e, te) = insert_unless scn @@ infer (fst @@ assume_typ x xk `EUnsolved scn) e in
  (Tlam (x, xk, e, `user), VForall (x, clos_of scn te xk))

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
  let (e2, _) = insert_unless scn (e2, lt) in
  (App (e1, e2), rt)

| RInst (e, t) ->
  let (e, te) = infer scn e in
  let (t, k) = kind_of scn t in

  let x = freshen_str "x" in
  let ret = fresh (mask_of (fst @@ assume_typ x k `ESolved scn)) "ret" in
  let clos = {knd = k; env = scn.env; bdr = B ret} in

  unify' scn (VForall (x, clos)) te;
  (Inst (e, t), capp clos (eval scn.env t))

| RLet (rc, x, ps, t, e, rest) ->
  let (scn, _, e, te) = infer_let scn rc x ps t e in
  let (rest, trest) = infer (fst @@ assume x te scn) rest in
  (Let (rc, x, quote scn.height te, e, rest), trest)

(* TODO: reorganize this case (and more stuff with ctors) *)
| RMatch (scrut, branches) ->
  let (scrut, scrut_typ) = infer scn scrut in
  let t = eval scn.env (fresh (mask_of scn) "t") in
  let branch_typs = List.map (fun (pat, branch) -> infer_branch scn scrut_typ pat branch) branches in
  ignore @@ List.map (fun (_, _, t') -> unify' scn t t') branch_typs;

  let branches' = List.map (fun (p, e, _) -> (p, e)) branch_typs in
  let patterns = List.map (fun (p, _) -> p) branches' in

  check_coverage scn patterns;
  (Match (scrut, branches'), t)

| RLit n ->
  (Lit n, VBase (infer_lit n))

(* look ahead to see if the head of the expression is a ctor *)
and split_head : rexpr -> rexpr * split_arg list = function (* todo: make tail recursive :) *)
| RApp (e1, e2) ->
  let e, es = split_head e1 in
  e, `app e2 :: es
| RInst (e, t) ->
  let e, es = split_head e in
  e, `inst t :: es
| e -> e, []

and check (scn : scene) (e : rexpr) (t : vtyp) : expr = match e, force t with
| RSrcRange (rng, e), t -> scn.range <- rng; check scn e t

| RLam (x, Some xt, e), VArrow (lt, rt) ->
  let xt = eval scn.env (is_type scn xt) in
  unify' scn xt lt;
  check scn (RLam (x, None, e)) (VArrow (lt, rt))
  
| RLam (x, None, e), VArrow (lt, rt) ->
  let e = check (fst @@ assume x lt scn) e rt in
  Lam (x, quote scn.height lt, e)

| RTlam (x, Some _, e), VForall (x', c) ->
  (*todo unify k with the kind of x'*)
  check scn (RTlam (x, None, e)) (VForall (x', c))

| RTlam (x, None, e), VForall (_, c) ->
  let ret_typ = cinst_at scn.height c in
  let e = check (fst @@ assume_typ x c.knd `EUnsolved scn) e ret_typ in
  Tlam (x, c.knd, e, `user)

| RLet (rc, x, ps, t, e, rest), t_rest ->
  let (scn, _, e, te) = infer_let scn rc x ps t e in
  let rest = check scn rest t_rest in
  Let (rc, x, quote scn.height te, e, rest)

| RMatch (scrut, branches), ret_typ ->
  let (scrut, scrut_typ) = infer scn scrut in
  let branch_typs = List.map (fun (pat, branch) -> check_branch scn scrut_typ pat branch ret_typ) branches in
  check_coverage scn (fst @@ List.split branch_typs);
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
    let scn = fst @@ assume x vt scn in
    let (mkscn, all_typ, ret_typ, lams) = process_params scn ps ret_typ in
    ((fun s -> mkscn (fst @@ assume x vt s)), Arrow (t, all_typ), ret_typ, fun e -> Lam (x, t, lams e))
  | RTParam (x, k) :: ps ->
    let k = maybe_rkind x k in
    let scn = fst @@ assume_typ x k `EUnsolved scn in
    let (mkscn, all_typ, ret_typ, lams) = process_params scn ps ret_typ in
    ((fun s -> mkscn (fst @@ assume_typ x k `EUnsolved s)), Forall (x, k, B all_typ), ret_typ, fun e -> Tlam (x, k, lams e, `user))

(* compute the scene representing a [let]'s inner scope, with all parameters bound.
  also returns the entire binding's type, and just its return type (without parameters)
*)
and scene_of_let (scn : scene) (rc : bool) (x : string) (ps : rparam list) (ret_typ : rtyp option) : scene * vtyp * vtyp * (expr -> expr) =
  let (mkscn, all_typ, ret_typ, lams) = process_params scn ps ret_typ in
  let all_typ = eval scn.env all_typ in
  (* if the binding is recursive, extend the scene with it *)
  let inner_scn = mkscn @@ if rc then fst @@ assume x all_typ scn else scn in
  (inner_scn, all_typ, ret_typ, lams)

and infer_let (scn : scene) (rc : bool) (x : string) (ps : rparam list) (t : rtyp option) (e : rexpr) : scene * scene * expr * vtyp =
  let (inner_scn, all_typ, ret_typ, lams) = scene_of_let scn rc x ps t in
  let bod = lams @@ check inner_scn e ret_typ in
  (fst @@ assume x all_typ scn, inner_scn, bod, all_typ)

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
| VForall (_, c) ->
  let ret, params = return_type (inc hi) (cinst_at hi c)
  in ret, `TpParam c.knd :: params
| t -> t, []

let lvls_of_tparams (hi : lvl) (tps : rtparam list) : tparam list * lvl list =
  let rec go hi tps = match tps with (* TODO make tailrec *)
  | [] -> hi, [], []
  | RTParam (x, k) :: rest ->
    let k = maybe_rkind "k" k in
    let scn, tps', lvls' = go (inc hi) rest in
    scn, (TParam (x, k) :: tps'), (lvls' @ [hi])
  in let _, tps, lvls = go hi tps in tps, lvls
let scene_of_tparams (scn : scene) (tps : tparam list) : scene =
  let rec go scn tps = match tps with (* TODO make tailrec? *)
  | [] -> scn
  | TParam (x, k) :: rest ->
    let scn, _ = assume_typ x k `EUnsolved scn in
    go scn rest
  in go scn tps
let rec data_full_kind (tps : tparam list) (ret_k : kind) : kind =
  match tps with
  | [] -> ret_k
  | TParam (_, k) :: rest -> KArrow (k, data_full_kind rest ret_k)

exception BadCtorReturn
let matches_parent (expect_i : lvl) (expect_lvls : lvl list) (rett : vtyp) : unit =
  let rec go = function
  | _, [] -> ()
  | VNeut (VQvar i, []) :: spine, lvl :: lvls when lvl = i -> go (spine, lvls)
  | _ -> raise BadCtorReturn
  in match rett with
  | VNeut (VQvar actual_i, spine) when expect_i = actual_i -> go (spine, expect_lvls)
  | _ -> raise BadCtorReturn
let rec add_tparams (tps : tparam list) (t : typ) : typ =
  match tps with
  | [] -> t
  | TParam (x, k) :: rest -> Forall (x, k, B (add_tparams rest t))

(* modify the scene with a new data declaration and its constructors *)

(* when processing a data declaration,
- extract full kind of parent
- add parent to outer scene
- build scene with parameters, for checking ctors
- for each ctor
  - verify type under inner scene
  - add params to ctor type
  - add ctor with full type to outer scene
*)
let declare_data (scn : scene) (x : string) (tps : rtparam list) (ret_k : rkind) (ctors : rctor list) : scene * tparam list * kind * string list =
  (* extract full kind *)
  let ret_k = lower_kind ret_k in
  let tps, lvls = lvls_of_tparams (inc scn.height) tps in (* increment height to account for the type name itself *)
  let full_k = data_full_kind tps ret_k in

  (* add parent to outer scene *)
  let outer_scn, parent = assume_typ x full_k `ESolved scn in
  let inner_scn = scene_of_tparams outer_scn tps in

  (* process ctors *)
  let outer_scn, ctors' = ctors |> List.fold_left_map (fun outer_scn (RCtor {nam; t}) ->
    (* evaluate ctor's type *)
    let t = is_type inner_scn t in
    let vt = eval inner_scn.env t in

    (* validate ctor's return type *)
    let ret_t, _ = return_type inner_scn.height vt in
    matches_parent parent lvls ret_t;

    (* build full type and add to ctx *)
    let full_t = eval outer_scn.env (add_tparams tps t) in
    let outer_scn, lvl = assume_ctor nam full_t parent outer_scn in
    outer_scn, (nam, lvl)
  ) outer_scn in
  
  let ctor_names, ctor_lvls = List.split ctors' in
  let outer_scn = assume_ctors_of parent ctor_lvls outer_scn in
  outer_scn, tps, full_k, ctor_names
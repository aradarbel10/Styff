open Batteries.Uref
open Syntax.Common
module S = Syntax.Core
module Z = Syntax.Zonked
open Typecheck.Eval


(* identifiers in styff may contain quotes (') and symbols (user-defined operators)
   which must be eliminated towards the backend. *)
let sanitize (nm : name) : name =
  let allowed : char -> bool = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' -> true
  | _ -> false
  in if String.for_all allowed nm then nm else freshen "nm"


exception UnsolvedKVar
exception UnsolvedTVar
let rec zonk_kind (k : S.kind) : Z.kind =
  match k with
  | Star -> Star
  | KArrow (k1, k2) -> KArrow (zonk_kind k1, zonk_kind k2)
  | KVar kv ->
    match uget kv with
    | KSolved k -> zonk_kind k
    | KUnsolved _ -> raise UnsolvedKVar

let zonk_type (tps : name list) (t : S.typ) : Z.typ =
  let rec go (tps : name list) (t : S.typ) : Z.typ =
    match t with
    | Tvar (tv, _) ->
      begin match uget tv with
      | Solved t -> go tps (quote (S.height tps) t)
      | Unsolved _ -> raise UnsolvedTVar
      end
    | Inserted _ -> failwith "absurd! normalized types cannot contain inserted metas"
    | Qvar (Idx i) -> Qvar (List.nth tps i)
    | Arrow (lt, rt) -> Arrow (go tps lt, go tps rt)
    | Tapp (t1, t2) -> TApp (go tps t1, go tps t2)
    | TAbs (x, k, B t) -> TAbs (x, zonk_kind k, go (x::tps) t)
    | TLet _ -> failwith "absurd! normalized types cannot contain type-level let bindings"
    | Forall (x, k, B t) -> Forall (x, zonk_kind k, go (x::tps) t)
    | Base b -> Base b
  in go tps t

exception UnannotatedExpr
let zonk_expr nms tps =
  let rec go (nms : name list) (tps : name list) (e : S.expr) : Z.expr =
    match e with
    | Var (Idx i) -> Var (List.nth nms i)
    | Ctor (Idx i, es) -> Ctor (List.nth nms i, List.map (go_arg nms tps) es)
    | Lam (x, t, e) -> Lam (x, zonk_type tps t, go (sanitize x :: nms) tps e)
    | Tlam (x, k, e) -> Tlam (x, zonk_kind k, go nms (sanitize x :: tps) e)
    | App (e1, e2) -> App (go nms tps e1, go nms tps e2)
    | Inst (e, t) -> Inst (go nms tps e, zonk_type tps t)
    | Let (rc, x, _, e, e') ->
      let x = sanitize x in
      let nms = if rc then x :: nms else nms in
      Let (x, go nms tps e, go (x :: nms) tps e')
    | Match (e, branches) -> Match (go nms tps e, go_branches nms tps branches)
    | Lit l -> Lit l

  and scope_pattern nms tps (PCtor (Idx i, ps) : S.pattern) =
    let ctor = List.nth nms i in
    let rec go (nms : name list) (tps : name list) (ps : pat_arg list) (full : pat_arg list) =
      match ps with
      | [] -> nms, tps, Z.PCtor (ctor, full)
      | PVar x :: ps ->
        let x = sanitize x in
        go (x :: nms) tps ps (full @ [PVar x])
      | PTvar x :: ps -> go nms (x :: tps) ps (full @ [PTvar x])
    in go nms tps ps []

  and go_branches nms tps bs =
    List.map (fun (p, e) -> let nms, tps, p = scope_pattern nms tps p in (p, go nms tps e)) bs
  and go_arg nms tps : S.arg -> Z.arg = function
  | `TmArg e -> `TmArg (go nms tps e)
  | `TpArg t -> `TpArg (zonk_type tps t)
  in go nms tps


(* constant folding (beta reduction) on the zonked language *)
type env = (name * Z.expr) list
type tenv = (name * Z.typ) list

let rec beta_fold_typ tenv : Z.typ -> Z.typ = function
  | Qvar x ->
    begin match List.assoc_opt x tenv with
    | Some e -> e
    | None -> Qvar x
    end
  | Arrow (lt, rt) -> Arrow (beta_fold_typ tenv lt, beta_fold_typ tenv rt)
  | TApp (t1, t2) -> TApp (beta_fold_typ tenv t1, beta_fold_typ tenv t2)
  | TAbs (x, k, t) -> TAbs (x, k, beta_fold_typ tenv t)
  | Forall (x, k, t) -> Forall (x, k, beta_fold_typ tenv t)
  | Prod ts -> Prod (List.map (beta_fold_typ tenv) ts)
  | Base b -> Base b

let beta_fold_expr : Z.expr -> Z.expr =
  let rec go (env : env) (tenv : tenv) : Z.expr -> Z.expr = function
  | Var x ->
    begin match List.assoc_opt x env with
    | Some e -> e
    | None -> Var x
    end
  | Ctor (x, es) -> Ctor (x, List.map (go_arg env tenv) es)
  | Lam (x, t, e) -> Lam (x, beta_fold_typ tenv t, go env tenv e)
  | Tlam (x, k, e) -> Tlam (x, k, go env tenv e)
  | App (e1, e2) ->
    let e2 = go env tenv e2 in
    begin match go env tenv e1 with
    | Lam (x, _, e) -> go ((x, e2) :: env) tenv e
    | e1 -> App (e1, e2)
    end
  | Inst (e, t) ->
    let t = beta_fold_typ tenv t in
    begin match go env tenv e with
    | Tlam (x, _, e) -> go env ((x, t) :: tenv) e
    | e -> Inst (e, t)
    end
  | Let (x, e, rest) -> Let (x, go env tenv e, go env tenv rest)
  | Match (e, bs) -> Match (go env tenv e,
    List.map (fun (p, b) -> (p, go env tenv b)) bs)
  | Tup es -> Tup (List.map (go env tenv) es)
  | ProjAt (e, i) -> ProjAt (go env tenv e, i)
  | Lit l -> Lit l
  | BinOp (e1, op, e2) -> BinOp (go env tenv e1, op, go env tenv e2)
  and go_arg env tenv : Z.arg -> Z.arg = function
  | `TmArg e -> `TmArg (go env tenv e)
  | `TpArg t -> `TpArg (beta_fold_typ tenv t)
  in go [] []

let beta_fold_prog : Z.prog -> Z.prog =
  let go_stmt : Z.stmt -> Z.stmt = function
  | Def (rc, x, t, e) -> Def (rc, x, beta_fold_typ [] t, beta_fold_expr e)
  | TDef (x, k, t) -> TDef (x, k, beta_fold_typ [] t)
  in List.map go_stmt
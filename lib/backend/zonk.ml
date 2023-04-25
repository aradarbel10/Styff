open Syntax.Common
module C = Syntax.Core
module Z = Syntax.Zonked
open Typecheck.Eval
open Typecheck.Errors

(* identifiers in styff may contain quotes (') and symbols (user-defined operators)
   which must be eliminated towards the backend. *)
let sanitize_str (nm : string) : string =
  let allowed : char -> bool = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' -> true
  | _ -> false
  in if String.for_all allowed nm then nm else freshen_str "nm"
let sanitize : name -> name = List.map sanitize_str


type zonk_scope = {nms : string list; tps : string list}

exception UnsolvedKVar
exception UnsolvedTVar of string
let rec zonk_kind (k : C.kind) : Z.kind =
  match k with
  | Star -> Star
  | KArrow (k1, k2) -> KArrow (zonk_kind k1, zonk_kind k2)
  | KVar kv ->
    match !kv with
    | KSolved k -> zonk_kind k
    | KUnsolved _ -> raise UnsolvedKVar

let zonk_type : zonk_scope -> C.typ -> Z.typ =
  let rec go (scp : zonk_scope) (t : C.typ) : Z.typ =
    match t with
    | Tvar (tv, _) ->
      begin match !tv with
      | Solved t -> go scp (quote (C.height scp.tps) t)
      | Unsolved x -> raise (UnsolvedTVar x)
      end
    | Inserted _ -> raise (EvalFailure {code = UnnormalizedInsertedMeta})(* failwith "absurd! normalized types cannot contain inserted metas" *)
    | Qvar i -> Qvar (at_idx scp.tps i)
    | Arrow (lt, rt) -> Arrow (go scp lt, go scp rt)
    | Tapp (t1, t2) -> TApp (go scp t1, go scp t2)
    | TAbs (x, k, B t) -> TAbs (x, zonk_kind k, go {scp with tps = x :: scp.tps} t)
    | TLet _ -> failwith "absurd! normalized types cannot contain type-level let bindings"
    | Forall (x, k, B t) -> Forall (x, zonk_kind k, go {scp with tps = x :: scp.tps} t)
    | Base b -> Base b
  in go

let zonk_expr : zonk_scope -> C.expr -> Z.expr =
  let rec go (scp : zonk_scope) (e : C.expr) : Z.expr =
    match e with
    | Var i -> Var (at_idx scp.nms i)
    | Ctor (i, es) -> Ctor (at_idx scp.nms i, List.map (go_arg scp) es)
    | Lam (x, t, e) -> Lam (x, zonk_type scp t, go {scp with nms = sanitize_str x :: scp.nms} e)
    | Tlam (x, k, e, _) -> Tlam (x, zonk_kind k, go {scp with tps = sanitize_str x :: scp.tps} e)
    | App (e1, e2) -> App (go scp e1, go scp e2)
    | Inst (e, t) -> Inst (go scp e, zonk_type scp t)
    | Let (rc, x, _, e, e') ->
      let x = sanitize_str x in
      let scp = if rc then {scp with nms = x :: scp.nms} else scp in
      Let (x, go scp e, go {scp with nms = x :: scp.nms} e')
    | Match (e, branches) -> Match (go scp e, go_branches scp branches)
    | Lit l -> Lit l
    | BinOp (e1, op, e2) -> BinOp (go scp e1, op, go scp e2)

  and scope_pattern (scp : zonk_scope) (PCtor (i, ps) : C.pattern) =
    let ctor = at_idx scp.nms i in
    let rec go (scp : zonk_scope) (ps : pat_arg list) (full : pat_arg list) =
      match ps with
      | [] -> scp, Z.PCtor (ctor, List.rev full)
      | PVar x :: ps ->
        let x = sanitize_str x in
        go {scp with nms = x :: scp.nms} ps (PVar x :: full)
      | PTvar x :: ps ->
        go {scp with tps = x :: scp.tps} ps (PTvar x :: full)
    in go scp ps []

  and go_branches (scp : zonk_scope) bs =
    List.map (fun (p, e) -> let scp, p = scope_pattern scp p in (p, go scp e)) bs
  and go_arg (scp : zonk_scope) : C.arg -> Z.arg = function
  | `TmArg e -> `TmArg (go scp e)
  | `TpArg t -> `TpArg (zonk_type scp t)
  in go


(*
    constant folding (beta reduction) on the zonked language
*)
type env = (string * Z.expr) list
type tenv = (string * Z.typ) list

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
  | Def (x, t, e) -> Def (x, beta_fold_typ [] t, beta_fold_expr e)
  | Print str -> Print str
  in List.map go_stmt
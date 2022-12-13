open Batteries.Uref
open Syntax.Common
module S = Syntax.Core
module Z = Syntax.Zonked
open Eval

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
    | Lam (x, t, e) -> Lam (x, zonk_type tps t, go (x::nms) tps e)
    | Tlam (x, k, e) -> Tlam (x, zonk_kind k, go nms (x::tps) e)
    | App (e1, e2) -> App (go nms tps e1, go nms tps e2)
    | Inst (e, t) -> Inst (go nms tps e, zonk_type tps t)
    | Let (rc, x, _, e, e') ->
      let nms = if rc then x::nms else nms in
      Let (x, go nms tps e, go nms tps e')
    | Match (e, branches) -> Match (go nms tps e, go_branches nms tps branches)
    | Lit l -> Lit l
  and go_branches nms tps = List.map (fun (p, e) -> (p, go nms tps e))
  in go nms tps
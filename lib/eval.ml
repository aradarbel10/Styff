open Batteries.Uref
open Expr

exception IndexOutOfScope
exception AppNonAbs
exception IllLengthedMask

let rec forcek (k : kind) : kind =
  match k with
  | KVar kv ->
    begin match uget kv with
    | KSolved k' -> forcek k'
    | _ -> k
    end
  | _ -> k

let rec eval (env : env) : typ -> vtyp = function
| Arrow (lt, rt) -> VArrow (eval env lt, eval env rt)
| TAbs (x, b) -> VAbs (x, {env = env; bdr = b})
| Forall (x, b) -> VForall (x, {env = env; bdr = b})
| Tapp (t1, t2) -> vapp (eval env t1) (eval env t2)
| Tvar tv -> vtvar tv
| Inserted (tv, msk) -> app_mask env msk (vtvar tv)
| Qvar i ->
  begin match lookup i env with
  | Some (_, t) -> t
  | None -> raise IndexOutOfScope
  end
| Base b -> VBase b

and capp (x : name) ({env = env; bdr = B b} : clos) (t : vtyp) : vtyp =
  eval ((x, t) :: env) b
and cinst_at (hi : lvl) (x : name) (c : clos) =
  capp x c (vqvar hi)
and vapp (t1 : vtyp) (t2 : vtyp): vtyp =
  match t1 with
  | VAbs (x, c) -> capp x c t2
  | VNeut (hd, sp) -> VNeut (hd, t2 :: sp)
  | _ -> raise AppNonAbs
and vtvar (tv : tvar uref) : vtyp =
  match uget tv with
  | Solved t -> t
  | Unsolved _ -> VNeut (VTvar tv, [])
and app_mask (env : env) (msk : mask) (hd : vtyp) : vtyp =
  match env, msk with
  | [], [] -> hd
  | (_, t) :: env, bound :: msk ->
    let hd = (app_mask env msk hd) in
    if bound
      then vapp hd t
      else hd
  | _ -> raise IllLengthedMask

let rec app_spine (t : vtyp) (sp : spine) : vtyp =
  match sp with
  | [] -> t
  | arg :: sp -> vapp (app_spine t sp) arg

let rec force (t : vtyp) : vtyp =
  match t with
  | VNeut (VTvar tv, sp) ->
    begin match uget tv with
    | Solved t' -> force (app_spine t' sp)
    | _ -> t
    end
  | _ -> t


let rec quote (hi : lvl) (t: vtyp) : typ =
  match force t with
| VArrow (lt, rt) -> Arrow (quote hi lt, quote hi rt)
| VAbs (x, c) -> TAbs (x, quote_clos hi x c)
| VForall (x, c) -> Forall (x, quote_clos hi x c)
| VBase b -> Base b
| VNeut (hd, sp) -> quote_spine hi (quote_head hi hd) sp
and quote_spine (hi : lvl) (hd : typ) (sp : spine) : typ =
  match sp with
  | [] -> hd
  | arg :: sp -> Tapp (quote_spine hi hd sp, quote hi arg)
and quote_head (hi : lvl) : head -> typ = function
| VQvar i -> Qvar (lvl2idx hi i)
| VTvar tv -> Tvar tv
and quote_clos (hi : lvl) (x : name) (c : clos) : bdr =
  let bod = cinst_at hi x c in
  let bdr = quote (inc hi) bod in
  B bdr
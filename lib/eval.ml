open Batteries.Uref
open Expr

exception IndexOutOfScope
exception AppNonForall
exception IllLengthedMask

let rec eval (env : env) : typ -> vtyp = function
| Arrow (lt, rt) -> VArrow (eval env lt, eval env rt)
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
and vapp (t1 : vtyp) (t2 : vtyp) : vtyp =
  match t1 with
  | VForall (x, c) -> capp x c t2
  | VNeut (hd, sp) -> VNeut (hd, t2 :: sp)
  | _ -> raise AppNonForall
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


let rec quote (hi : lvl) : vtyp -> typ = function
| VArrow (lt, rt) -> Arrow (quote hi lt, quote hi rt)
| VForall (x, c) ->
  let bod = cinst_at hi x c in
  let bdr = quote (inc hi) bod in
  Forall (x, B bdr)
| VBase b -> Base b
| VNeut (hd, sp) -> quote_neut hi hd sp
and quote_neut (hi : lvl) (hd : head) (sp : spine) : typ =
  let hd = quote_head hi hd in
  List.fold_left (fun fnc arg -> Tapp (fnc, quote hi arg)) hd sp
and quote_head (hi : lvl) : head -> typ = function
| VQvar i -> Qvar (lvl2idx hi i)
| VTvar tv -> Tvar tv



let rec force (t : vtyp) : vtyp =
  match t with
  | VNeut (VTvar tv, sp) ->
    begin match uget tv with
    | Solved t' -> force (List.fold_left vapp t' sp)
    | _ -> t
    end
  | _ -> t
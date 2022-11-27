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

(* NbE - Normalization by Evaluation
   
               eval
  Syntax ----------------> Semantics
  (Core) <----------------  (Values)
              quote  

normalization is only needed for types (not exprs) because
they are what's tested for equality during unification.
*)

(* evaluation, eliminates all redexes without going under binders *)
let rec eval (env : env) : typ -> vtyp = function
| Arrow (lt, rt) -> VArrow (eval env lt, eval env rt)
| TAbs (x, b) -> VAbs (x, {env = env; bdr = b})
| TLet (x, t, rest) ->
  let vt = eval env t in
  eval ((x, `ESolved, `EDefed, vt) :: env) rest
| Forall (x, b) -> VForall (x, {env = env; bdr = b})
| Tapp (t1, t2) -> vapp (eval env t1) (eval env t2)
| Tvar tv -> vtvar tv
| Inserted (tv, msk) -> app_mask env msk (vtvar tv)
| Qvar i ->
  begin match lookup i env with
  | Some (_, _, _, t) -> t
  | None -> raise IndexOutOfScope
  end
| Base b -> VBase b

(* eliminate a closure by evaling it under an extended env *)
and capp (x : name) ({env = env; bdr = B b} : clos) (t : vtyp) : vtyp =
  eval ((x, `ESolved, `EDefed, t) :: env) b
and cinst_at (hi : lvl) (x : name) (c : clos) = (* instantiate closure [c] at env of height [hi] *)
  capp x c (vqvar hi)
and vapp (t1 : vtyp) (t2 : vtyp): vtyp =
  match force t1 with
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
  | (_, _, _, t) :: env, bound :: msk ->
    let hd = (app_mask env msk hd) in
    begin match bound with
    | `EBound -> vapp hd t
    | `EDefed -> hd
    end
  | _ -> raise IllLengthedMask

and app_spine (t : vtyp) (sp : spine) : vtyp =
  match sp with
  | [] -> t
  | arg :: sp -> vapp (app_spine t sp) arg

and force (t : vtyp) : vtyp =
  match t with
  | VNeut (VTvar tv, sp) ->
    begin match uget tv with
    | Solved t' -> force (app_spine t' sp)
    | _ -> t
    end
  | _ -> t

(* convert a value back to its normal form, including going under binders with their "actual" env *)
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

(* evaling and quoteing = normalizing *)
let norm (env : env) (t : typ) : typ =
  let vt = eval env t in
  quote (Lvl (List.length env)) vt

(* normalize each type in the expression (not the expression itself) *)
let rec norm_expr (env : env) (e : expr) : expr =
  match e with
  | Var i -> Var i
  | Lam (x, t, e) -> Lam (x, norm env t, norm_expr env e)
  | Tlam (x, e) ->
    let v = vqvar (Lvl (List.length env)) in
    Tlam (x, norm_expr ((x, `EUnsolved, `EBound, v) :: env) e)
  | App (e1, e2) -> App (norm_expr env e1, norm_expr env e2)
  | Inst (e, t) -> Inst (norm_expr env e, norm env t)
  | Let (rc, x, t, e, rest) -> Let (rc, x, norm env t, norm_expr env e, norm_expr env rest)
  | Lit l -> Lit l
  | Match (e, bs) -> Match (norm_expr env e, List.map (norm_branch env) bs)
and norm_branch (env : env) (((PCtor (_, args) as pat), bod) : pattern * expr) : pattern * expr =
  let rec env_of_pattern (args : pat_arg list) (env : env) : env =
    begin match args with
    | [] -> env
    | PVar  _ :: args -> env_of_pattern args env
    | PTvar x :: args -> 
      let v = vqvar (Lvl (List.length env)) in
      (x, `EUnsolved, `EBound, v) :: env_of_pattern args env
    end
  in
  (pat, norm_expr (env_of_pattern args env) bod)
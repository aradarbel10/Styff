open Batteries.Uref
open Syntax.Core

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
| TAbs (x, k, b) -> VAbs (x, {knd = k; env = env; bdr = b})
| TLet (_x, _, t, rest) ->
  let vt = eval env t in
  eval ((`ESolved, `EDefed, vt) :: env) rest
| Forall (x, k, b) -> VForall (x, {knd = k; env = env; bdr = b})
| Tapp (t1, t2) -> vapp (eval env t1) (eval env t2)
| Tvar (tv, k) -> vtvar tv k
| Inserted (tv, k, msk) -> app_mask env msk (vtvar tv k)
| Qvar i ->
  begin match lookup i env with
  | Some (_, _, t) -> t
  | None -> raise IndexOutOfScope
  end
| Base b -> VBase b

(* eliminate a closure by evaling it under an extended env *)
and capp ({knd = _; env = env; bdr = B b} : clos) (t : vtyp) : vtyp =
  eval ((`ESolved, `EDefed, t) :: env) b
and cinst_at (hi : lvl) (c : clos) = (* instantiate closure [c] at env of height [hi] *)
  capp c (vqvar hi)
and vapp (t1 : vtyp) (t2 : vtyp): vtyp =
  match force t1 with
  | VAbs (_, c) -> capp c t2
  | VNeut (hd, sp) -> VNeut (hd, t2 :: sp)
  | _ -> raise AppNonAbs
and vtvar (tv : tvar uref) (k : kind) : vtyp =
  match uget tv with
  | Solved t -> t
  | Unsolved _ -> VNeut (VTvar (tv, k), [])
and app_mask (env : env) (msk : mask) (hd : vtyp) : vtyp =
  match env, msk with
  | [], [] -> hd
  | (_, _, t) :: env, bound :: msk ->
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
  begin match t with
  | VNeut (VTvar (tv, _), sp) ->
    begin match uget tv with
    | Solved t' -> force (app_spine t' sp)
    | _ -> t
    end
  | _ -> t
  end

(* convert a value back to its normal form, including going under binders with their "actual" env *)
let rec quote (hi : lvl) (t: vtyp) : typ =
  match force t with
| VArrow (lt, rt) -> Arrow (quote hi lt, quote hi rt)
| VAbs (x, c) -> TAbs (x, c.knd, quote_clos hi c)
| VForall (x, c) -> Forall (x, c.knd, quote_clos hi c)
| VBase b -> Base b
| VNeut (hd, sp) -> quote_spine hi (quote_head hi hd) sp
and quote_spine (hi : lvl) (hd : typ) (sp : spine) : typ =
  match sp with
  | [] -> hd
  | arg :: sp -> Tapp (quote_spine hi hd sp, quote hi arg)
and quote_head (hi : lvl) : head -> typ = function
| VQvar i -> Qvar (lvl2idx hi i)
| VTvar (tv, k) -> Tvar (tv, k)
and quote_clos (hi : lvl) (c : clos) : bdr =
  let bod = cinst_at hi c in
  let bdr = quote (inc hi) bod in
  B bdr

(* evaling and quoteing = normalizing *)
let norm (env : env) (t : typ) : typ = quote (height env) (eval env t)
(* usually values are already normalized, but we want to re-norm after the environment is refined (to open definitions) *)
let vnorm (env : env) (t : vtyp) : vtyp = eval env (quote (height env) t)

(* normalize each type in the expression (not the expression itself) *)
let rec norm_expr (env : env) (e : expr) : expr =
  match e with
  | Var i -> Var i
  | Ctor (i, es) -> Ctor (i, List.map (norm_arg env) es)
  | Lam (x, t, e) -> Lam (x, norm env t, norm_expr env e)
  | Tlam (x, k, e) ->
    let v = vqvar (height env) in
    Tlam (x, k, norm_expr ((`EUnsolved, `EBound, v) :: env) e)
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
    | PTvar _x :: args -> 
      let v = vqvar (height env) in
      (`EUnsolved, `EBound, v) :: env_of_pattern args env
    end
  in
  (pat, norm_expr (env_of_pattern args env) bod)
and norm_arg (env : env) (arg : arg) : arg =
  match arg with
  | `TmArg e -> `TmArg (norm_expr env e)
  | `TpArg t -> `TpArg (norm env t)
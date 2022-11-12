open Batteries.Uref
open Expr
open Eval

type partial_renaming = {
  dom : lvl;
  cod : lvl;
  ren : (lvl * lvl) list; (* forall cod --> dom *)
}

let lift ({dom; cod; ren} : partial_renaming) : partial_renaming =
  { dom = inc dom; cod = inc cod; ren = (cod, dom) :: ren }

exception NonVarInSpine
exception NonLinearSpine
exception OccursError
exception IllScopedSpine

let rec invert (hi : lvl) : spine -> partial_renaming = function
| [] -> { dom = Lvl 0; cod = hi; ren = [] }
| (t' :: sp) ->
  match force t' with
  | VNeut (VQvar t, []) -> let r = invert hi sp in
    begin match List.mem_assoc t r.ren with
    | true -> raise NonLinearSpine
    | false -> { dom = inc r.dom; cod = r.cod; ren = (t, r.dom) :: r.ren }
    end
  | _ -> raise NonVarInSpine

let rec rename (r : partial_renaming) (t : vtyp) (tv' : tvar uref) : typ =
  match force t with
  | VNeut (hd, sp) ->
    begin match hd with
    | VTvar tv ->
      if equal tv tv'
        then raise OccursError
        else rename_spine r (Tvar tv) sp tv'
    | VQvar i ->
      match List.assoc_opt i r.ren with
      | None -> raise IllScopedSpine
      | Some i' -> rename_spine r (Qvar (lvl2idx r.dom i')) sp tv'
    end
  | VArrow (lt, rt) -> Arrow (rename r lt tv', rename r rt tv')
  | VAbs (x, c) -> TAbs (x, rename_clos r x c tv')
  | VForall (x, c) -> Forall (x, rename_clos r x c tv')
  | VBase b -> Base b
and rename_clos (r : partial_renaming) (x : name) (c : clos) (tv' : tvar uref) : bdr =
  let bod = cinst_at r.cod x c in
  let bdr = rename (lift r) bod tv' in
  B bdr
and rename_spine (r : partial_renaming) (t : typ) (sp : spine) (tv' : tvar uref) : typ =
  match sp with
  | [] -> t
  | em :: sp -> Tapp (rename_spine r t sp tv', rename r em tv')


exception Ununifiable
exception DifferentSpineLength
exception UnunifiableKinds

let rec close (Lvl i : lvl) (t : typ) : typ =
  if i < 0
    then raise (Invalid_argument "can't wrap negative lambdas")
  else if i = 0
    then t
  else
    close (Lvl (i - 1)) (TAbs ("x" ^ string_of_int i, B t))

let solve (hi : lvl) (tv : tvar uref) (sp : spine) (t : vtyp) : unit =
  let ren = invert hi sp in
  let rhs = rename ren t tv in
  let sol = eval [] (close ren.dom rhs) in
  uset tv (Solved sol)

let rec unify (hi : lvl) (typ : vtyp) (typ' : vtyp) : unit =
  match force typ, force typ' with
  | VNeut (VTvar tv, sp), VNeut (VTvar tv', sp') when tv = tv' -> unify_spines hi sp sp'
  | VNeut (VQvar i, sp), VNeut (VQvar i', sp') when i = i' -> unify_spines hi sp sp'
  | VNeut (VTvar tv, sp), t | t, VNeut (VTvar tv, sp) -> solve hi tv sp t
  | VArrow (ltyp, rtyp), VArrow (ltyp', rtyp') ->
    unify hi ltyp ltyp'; unify hi rtyp rtyp'
  | VAbs (x, c), VAbs (x', c') -> unify (inc hi) (cinst_at hi x c) (cinst_at hi x' c')
  | VForall (x, c), VForall (x', c') -> unify (inc hi) (cinst_at hi x c) (cinst_at hi x' c')
  | VBase b, VBase b' when b = b' -> ()
  | t, t' -> let _ = (t, t') in raise Ununifiable
and unify_spines (hi : lvl) (sp : spine) (sp' : spine) =
  match sp, sp' with
  | [], [] -> ()
  | (t :: sp), (t' :: sp') -> unify_spines hi sp sp'; unify hi t t'
  | _ -> raise DifferentSpineLength

and unify_kinds (k : kind) (k' : kind) =
  match forcek k, forcek k' with
  | Star, Star -> ()
  | KArrow (lk, rk), KArrow (lk', rk') -> unify_kinds lk lk'; unify_kinds rk rk'
  | KVar kv, KVar kv' when kv = kv' -> ()
  | KVar kv, k | k, KVar kv -> uset kv (KSolved k)
  | _ -> raise UnunifiableKinds
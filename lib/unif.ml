open Batteries.Uref
open Expr
open Eval

(* choose between 'global' unification, which solves regular metavariables,
   and 'local' unification (aka LHS unification) which solves variables from the environment *)
type unif_mode =
| Global
| Local of env ref

(* contextual metavariables: metavars live in toplevel and may depend on names in their occurance's context
  when solving a metavar, we need to rename those names to toplevel *)
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

(* since hihger order unification is undecidable,
   we stick to the "pattern fragment" where equations can be solved easily by inversion.
   this happens when the spine contains only vars and is linear. *)
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

(* for maximum efficiency, we combine into the same function:
   apply renaming, quoting, occurs check *)
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
exception UnunifiableLocals
exception DifferentSpineLength
exception UnunifiableKinds

(* we encode contextual metas using type-level abstractions.
   this converts an (open) rhs to a closed term by wrapping it with abs *)
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

let rec assign_local (env : env ref) (lvl : lvl) (t : vtyp) : unit =
  let vne = List.rev !env in
  let (x, solved, _, _) = List.nth vne (unLvl lvl) in
  let entry = match solved with
    | `ESolved -> failwith "idk what to do"
    | `EUnsolved -> (x, `ESolved, `EDefed, t)
  in
  let vne' = List.mapi (fun i e -> if i = unLvl lvl then entry else e) vne in
  env := List.rev vne';
and solve_local (env : env ref) (_hi : lvl) (i : lvl) (i' : lvl) : unit =
  match lookup_lvl i !env, lookup_lvl i' !env with (* should maybe add some kind of forcing/just represent env more like metactx *)
  | None, _ | _, None -> failwith "absurd!" (* ill scoped value *)
  | Some (_, _, _, t), Some (_, _, _, t') when t = t' -> ()
  | Some (_, `EUnsolved, _, u), Some (_, _, _, t) | Some (_, _, _, t), Some (_, `EUnsolved, _, u) ->
    begin match force u with
    | VNeut (VQvar i, []) -> assign_local env i t
    | _ -> failwith "absurd!" (* invalid unsolved value *)
    end
  | Some (_, `ESolved, _, t), Some (_, `ESolved, _, t') -> (* unify hi (Local env) t t' *)
    if t = t' then () else raise UnunifiableLocals

(* confirm two types are equal, solve metavars along the way if needed.
   thanks to NbE we don't need to worry about a complicated equational theory. *)
and unify (hi : lvl) (mode : unif_mode) (typ : vtyp) (typ' : vtyp) : unit =
  match mode, force typ, force typ' with
  | _, VNeut (VTvar tv, sp), VNeut (VTvar tv', sp') when tv = tv' -> unify_spines hi mode sp sp'
  | Global, VNeut (VTvar tv, sp), t
  | Global, t, VNeut (VTvar tv, sp) -> solve hi tv sp t
  | Global, VNeut (VQvar i, sp), VNeut (VQvar i', sp') when i = i' -> unify_spines hi mode sp sp'
  | Local env, VNeut (VQvar i, sp), VNeut (VQvar i', sp') -> unify_spines hi mode sp sp'; solve_local env hi i i'
  | Local env, VNeut (VQvar i, []), t | Local env, t, VNeut (VQvar i, []) -> assign_local env i t
  (* | Local env, VNeut (VQvar i, sp), t
  | Local env, t, VNeut (VQvar i, sp) -> solve_local hi env i sp t *)
  | _, VArrow (ltyp, rtyp), VArrow (ltyp', rtyp') ->
    unify hi mode ltyp ltyp'; unify hi mode rtyp rtyp'
  | _, VAbs (x, c), VAbs (x', c') -> unify (inc hi) mode (cinst_at hi x c) (cinst_at hi x' c')
  | _, VForall (x, c), VForall (x', c') -> unify (inc hi) mode (cinst_at hi x c) (cinst_at hi x' c')
  | _, VBase b, VBase b' when b = b' -> ()
  | _, t, t' -> let _ = (t, t') in raise Ununifiable
and unify_spines (hi : lvl) (mode : unif_mode) (sp : spine) (sp' : spine) =
  match sp, sp' with
  | [], [] -> ()
  | (t :: sp), (t' :: sp') -> unify_spines hi mode sp sp'; unify hi mode t t'
  | _ -> raise DifferentSpineLength

and unify_kinds (k : kind) (k' : kind) =
  match forcek k, forcek k' with
  | Star, Star -> ()
  | KArrow (lk, rk), KArrow (lk', rk') -> unify_kinds lk lk'; unify_kinds rk rk'
  | KVar kv, KVar kv' when kv = kv' -> ()
  | KVar kv, k | k, KVar kv -> uset kv (KSolved k)
  | _ -> raise UnunifiableKinds
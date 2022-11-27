open Expr
open Unif
open Eval
open Scene

(*
  local_unify is similar to regular unification, but instead of solving metas it can solve locally bound variables.
*)
let local_unify (t : vtyp) (t' : vtyp) (scn : scene) : scene =
  let env = ref (scn.env) in
  unify scn.height (Local env) t t';
  {scn with env = !env}
  (*
  let env_metas = List.map2 entry_to_tvar scn.env scn.msk in
  let t  = eval scn.env t  in
  let t' = eval scn.env t' in
  unify (Lvl (List.length env_metas)) Local t t';
  let nms = List.map fst env_metas in
  let (env', msk') = unzip @@ List.map (fun (x, t) -> tvar_to_entry (Lvl (level_of x nms)) (x, t)) env_metas in
  {scn with env = env'; msk = msk'}
  - turn env to metas (bound ↦ unsolved, unbound (has value) ↦ solved)
  - (might not be needed) normalize/apply the change to env to the terms themselves
  - use regular unification (has access to env, thus prev step might not be needed)
  - convert metas back to a regular env
  *)

exception UndefinedCtor
exception TooManyArgsInPattern
exception UnexpectedTArgPattern
(* infer a pattern under the given scene. returns:
- elaborated version of the pattern (with implicit instantiations)
- modified scene with all pattern-variables bound
- the type of the pattern (return-type of the constructor)
*)
let rec infer_pattern (scn : scene) (PCtor (ctor, args) : pattern) : scene * pattern * vtyp =
  match args with
  | [] ->
    begin match List.assoc_opt ctor scn.ctx with
    | Some t -> (scn, PCtor (ctor, []), t)
    | None -> failwith "absurd!" (* ctors will be verified before going into branches *)
    end
  | PVar  v :: args ->
    let (scn, PCtor (ctor, args), t) = insert_pattern @@ infer_pattern scn (PCtor (ctor, args)) in
    begin match t with
    | VArrow (lt, rt) -> (assume scn v lt, PCtor (ctor, PVar v :: args), rt)
    | VForall _ -> failwith "absurd!" (* would be eliminated by [insert_pattern] *)
    | _ -> raise TooManyArgsInPattern
    end
  | PTvar v :: args ->
    let (scn, PCtor (ctor, args), t) = infer_pattern scn (PCtor (ctor, args)) in
    begin match t with
    | VForall (_, c) -> (assume_typ scn v Star `EUnsolved, PCtor (ctor, PTvar v :: args), cinst_at scn.height v c)
    | _ -> raise UnexpectedTArgPattern
    end
(* the pattern equivalent of [insert], adds implicit instantiations as far as the type allows *)
and insert_pattern ((scn, (PCtor (ctor, args) as pat), t) : scene * pattern * vtyp) : scene * pattern * vtyp =
  match force t with
  | VForall (x, c) -> (assume_typ scn x Star `EUnsolved, PCtor (ctor, PTvar x :: args), cinst_at scn.height x c)
  | t -> (scn, pat, t)

(*
  when inferring a scene type, we use bound tvars in the types of bound vars.
  then, after local_unify some of these bound tvars might get solved,
  so we need to re-normalize the added parts of the [ctx]

  optimization idea: separate tvars instantiated in patterns to their own type of metavar,
    the solution of which is referenced within types in the ctx. then this normalization is redundant
*)
let norm_branch_scn (PCtor (_, args) : pattern) (scn : scene) : scene =
  let rec go (ctx : ctx) (env : env) (args : pat_arg list) : ctx =
    match args with
    | [] -> ctx
    | PVar  _ :: args ->
      begin match ctx with
      | [] -> failwith "absurd!"
      | (x, t) :: ctx ->
        let ctx = go ctx env args in
        let t = eval env (quote (Lvl (List.length env)) t) in
        (x, t) :: ctx
      end
    | PTvar _ :: args ->
      begin match env with
      | [] -> failwith "absurd!"
      | _ :: env -> go ctx env args
      end
  in
  let ctx = go scn.ctx scn.env args in
  {scn with ctx = ctx}
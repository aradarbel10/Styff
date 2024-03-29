open Syntax.Core
open Syntax.Raw
open Unif
open Eval
open Scene
open! Util
open Errors

(*
  local_unify is similar to regular unification, but instead of solving metas it can solve locally bound variables.
*)
let local_unify (t : vtyp) (t' : vtyp) (scn : scene) : scene =
  let env = ref (scn.env) in
  unify scn.height (Local env) t t';
  {scn with env = !env}

(* infer a pattern under the given scene. returns:
- elaborated version of the pattern (with implicit instantiations)
- modified scene with all pattern-variables bound
- the type of the pattern (return-type of the constructor)
*)
let infer_pattern (scn : scene) (RPCtor (ctor, args) : rpattern) : scene * pattern * vtyp =
  match lookup_term ctor scn with
  | None | Some (_, _, EVar) -> elab_complain scn (UndefinedVar ctor)
  | Some (i, typ_all, ECtor _) ->
    let rec go (scn, acc : scene * pat_arg list) (args : pat_arg list) (typ : vtyp) : scene * pat_arg list * vtyp =
      match args, force typ with
      | PTvar v :: args, VForall (_, c) ->
        let rest_typ = cinst_at scn.height c in
        let scn, _ = assume_typ v c.knd `EUnsolved scn in
        go (scn, PTvar v :: acc) args rest_typ
      | args, (VForall (x, _) as typ) ->
        go (scn, acc) (PTvar x :: args) typ (* insert artificial param-tvar and retry with same typ *)
      | PTvar _ :: _, _ -> raise (ElabFailure {code = UnexpectedTArgPattern; scp = scn.scope; range = scn.range})
      | PVar v :: args, VArrow (lt, rt) ->
        let scn = fst @@ assume v lt scn in
        go (scn, PVar v :: acc) args rt
      | PVar _ :: _, _ -> raise (ElabFailure {code = TooManyArgsInPattern ctor; scp = scn.scope; range = scn.range})
      | [], typ -> scn, List.rev acc, typ
    in
    let scn, args, ret_typ = go (scn, []) (args) typ_all
    in scn, PCtor (i, args), ret_typ

(*
  when inferring a scene type, we use bound tvars in the types of bound vars.
  then, after local_unify some of these bound tvars might get solved,
  so we need to re-normalize the added parts of the [ctx]

  optimization idea: separate tvars instantiated in patterns to their own type of metavar,
    the solution of which is referenced within types in the ctx. then this normalization is redundant
*)
let norm_branch_scn (PCtor (_, args) : pattern) (scn : scene) : scene =
  let rec go (args : pat_arg list) (ctx : ctx) (env : env) : ctx =
    match args, ctx, env with
    | [], _, _ -> ctx
    | PVar  _ :: args, (t, entry) :: ctx, env ->
      let ctx = go args ctx env in
      (vnorm env t, entry) :: ctx
    | PTvar _ :: args, ctx, _ :: env ->
      go args ctx env
    | _ -> failwith "absurd!" (* args and scene will be synchronized *)
  in {scn with ctx = go (List.rev args) scn.ctx scn.env}

let scene_of_pattern (scn : scene) (scrut_typ : vtyp) (pat : rpattern) : pattern * scene =
  let (scn, pat, pat_typ) = infer_pattern scn pat in
  let scn = norm_branch_scn pat @@ local_unify pat_typ scrut_typ scn in
  (pat, scn)
  
(* check all constructors are matched exactly once *)
let check_same_parent (scn : scene) (pats : pattern list) : lvl * idx list =
  let parents= List.map (fun (PCtor (i, _)) -> match at_idx scn.ctx i with
    | _, ECtor {parent; _} -> (parent, i)
    | _ -> failwith "absurd!") pats in
  match parents with
  | [] -> failwith "empty match unsupported"
  | (parent, _) :: rest ->
    rest |> List.iter (fun (p, ctor) ->
      if p != parent
        then elab_complain scn (UnrelatedCase ctor)
        else ());
    parent, snd (List.split parents)

let check_coverage (scn : scene) (pats : pattern list) : unit =
  let parent, ctors = check_same_parent scn pats in
  match List.assoc_opt parent scn.ctors_of with
  | None -> failwith "absurd!" (* parent returned from scene must exist *)
  | Some cover ->
    let cover = List.map (lvl2idx (Lvl scn.scope.term_height)) cover in
    List.iter (fun ctor ->
      if mem_once ctor ctors
        then ()
      else if List.mem ctor ctors
        then elab_complain scn (DuplicateCase ctor) (* TODO: put back name in error *)
        else elab_complain scn (MissingCases (Util.diff cover ctors)) (* TODO: put back name in error *)
    ) cover
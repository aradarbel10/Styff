open Syntax.Core
open Syntax.Raw
open Unif
open Eval
open Scene
open Util

(*
  local_unify is similar to regular unification, but instead of solving metas it can solve locally bound variables.
*)
let local_unify (t : vtyp) (t' : vtyp) (scn : scene) : scene =
  let env = ref (scn.env) in
  unify scn.height (Local env) t t';
  {scn with env = !env}

exception UndefinedCtor
exception TooManyArgsInPattern
exception UnexpectedTArgPattern
(* infer a pattern under the given scene. returns:
- elaborated version of the pattern (with implicit instantiations)
- modified scene with all pattern-variables bound
- the type of the pattern (return-type of the constructor)
*)
let infer_pattern (scn : scene) (RPCtor (ctor, args) : rpattern) : scene * pattern * vtyp =
  match lookup ctor scn with
  | None -> failwith "absurd!" (* ctors will be verified before going into branches *)
  | Some (i, typ_all) ->
    let rec go (scn, acc : scene * pat_arg list) (args : pat_arg list) (typ : vtyp) : scene * pat_arg list * vtyp =
      match args, force typ with
      | PTvar v :: args, VForall (_, c) ->
        let rest_typ = cinst_at scn.height c in
        let scn = assume_typ v c.knd `EUnsolved scn in
        go (scn, PTvar v :: acc) args rest_typ
      | args, (VForall (x, _) as typ) ->
        go (scn, acc) (PTvar x :: args) typ (* insert artificial param-tvar and retry with same typ *)
      | PTvar _ :: _, _ -> raise UnexpectedTArgPattern
      | PVar v :: args, VArrow (lt, rt) ->
        let scn = assume v lt scn in
        go (scn, PVar v :: acc) args rt
      | PVar _ :: _, _ -> raise TooManyArgsInPattern
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
    | PVar  _ :: args, t :: ctx, env ->
      let ctx = go args ctx env in
      let t = vnorm env t in
      t :: ctx
    | PTvar _ :: args, ctx, _ :: env ->
      go args ctx env
    | _ -> failwith "absurd!" (* args and scene will be synchronized *)
  in {scn with ctx = go (List.rev args) scn.ctx scn.env}

let scene_of_pattern (scn : scene) (scrut_typ : vtyp) (pat : rpattern) : pattern * scene =
  let (scn, pat, pat_typ) = infer_pattern scn pat in
  let scn = norm_branch_scn pat @@ local_unify pat_typ scrut_typ scn in
  (pat, scn)

(* check all constructors are matched exactly once *)
exception DuplicateCases
exception MissingCases
exception UnrelatedCases

let check_same_parent (scn : scene) (ctors : name list) : name =
  let parents = List.map (fun c -> List.assoc c scn.parents) ctors in
  match parents with
  | [] -> failwith "empty match unsupported"
  | parent :: rest ->
    if List.for_all (fun p -> p = parent) rest
      then parent
      else raise UnrelatedCases

let check_coverage (scn : scene) (branches : (rpattern * rexpr) list) : unit =
  let ctors = List.map (fun (RPCtor (x, _), _) -> x) branches in
  let parent = check_same_parent scn ctors in
  match List.assoc_opt parent scn.ctors with
  | None -> failwith "absurd!" (* parent returned from scene must exist *)
  | Some cover ->
    List.iter (fun ctor ->
      if mem_once ctor ctors
        then ()
      else if List.mem ctor ctors
        then raise DuplicateCases
        else raise MissingCases
    ) cover
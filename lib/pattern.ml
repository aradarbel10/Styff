open Expr
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
        let t = eval env (quote (height env) t) in
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

let scene_of_pattern (scn : scene) (scrut_typ : vtyp) (pat : pattern) : pattern * scene =
  let (scn, pat, pat_typ) = insert_pattern @@ infer_pattern scn pat in
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

let check_coverage (scn : scene) (branches : (pattern * rexpr) list) : unit =
  let ctors = List.map (fun (PCtor (x, _), _) -> x) branches in
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
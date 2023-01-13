open Syntax.Core

module Sectioned = struct
  type entry =
    | Entry of name
    | Sect of string * entry list
  type t = (string * entry list) list

  (* [t] represents an "unfinished" hierarchy of entries. eg
  ```
  let a
  let b
  section n
    let c
    section m
      let d
    end
    let e
  ```
  here, the section [n] is not closed yet (there might still be definitions inside it!)
  so [t] is a list of those partial "layers".
  when we exit the section, the top layer becomes the contents of the section.

  "basically a trie zipper with path-sensitive induction"
  *)

  (* canonical way to write functions out of [t] *)
  (* todo better efficiency, somehow allow to escape/break/return mid fold *)
  let cata (f : 'a -> name -> name -> 'a) (pacc : name * 'a) (t : t) : 'a =
    let rec go_t (pre, acc : name * 'a) (t : t) : name * 'a =
      List.fold_left (fun (pre, acc) (s, es) ->
        match s, pre with
        | "", _ -> go_sect (pre, [], acc) es
        | s, (s' :: pre') when s = s' ->
          let _, acc = go_sect (pre, [], acc) es in
          pre', acc
        | _ -> failwith "internal error: sectioned structure isn't synced with prefix"
          (* todo: is this really an internal error? other causes *)
        ) (pre, acc) t
    and go_sect (pre, qua, acc : name * name * 'a) (es : entry list) : name * 'a =
      match es with
      | [] -> pre, acc
      | Entry nm :: es -> go_sect (pre, qua, f acc (pre @ qua @ nm) (qua @ nm)) es
      | Sect (s, es) :: es' ->
        let pre, acc = go_sect (pre, qua @ [s], acc) es in
        go_sect (pre, qua, acc) es'
    in snd @@ go_t pacc t

  let height (pre : name) (t : t) = cata (fun i _ _ -> i + 1) (pre, 0) t

  let cata_i (f : 'a -> name -> name -> int -> 'a) (pre, acc : name * 'a) (t : t) : 'a =
    let f' (a, i) full_nm qual_nm = (f a full_nm qual_nm i, i + 1) in
    let pacc = (pre, (acc, 0)) in
    fst @@ cata f' pacc t

  let push (scd : t) (ent : entry) : t =
    match scd with
    | (s, es) :: es' -> (s, ent :: es) :: es'
    | [] -> failwith "absurd! can't have zero layers in scope"
  let enter (sect : string) (scd : t) : t = (sect, []) :: scd
  let exit (scd : t) : t =
    match scd with
    | (s, es) :: es' -> push es' (Sect (s, es))
    | [] -> failwith "absurd! can't exit layer when there's no layers"

  let ith (t : t) (pre : name) (Idx i : idx) : name option =
    cata_i (
      fun acc full_nm _ i' -> if i = i' then Some full_nm else acc
    ) (pre, None) t

  let lookup (t : t) (pre : name) (nm : name) : idx option =
    let i = cata_i (function
    | None -> fun _ qual_nm i ->
      if nm = qual_nm then Some i else None
    | Some i -> fun _ _ _ -> Some i
    ) (pre, None) t
    in match i with
    | None -> None
    | Some i -> Some (Idx i)
end

type scope = {nms : Sectioned.t; tps : Sectioned.t; prefix : name}
module Scope = struct
  let push (scp : scope) (nm : name) : scope = {scp with nms = Sectioned.push scp.nms (Entry nm)}
  let tpush (scp : scope) (nm : name) : scope = {scp with tps = Sectioned.push scp.tps (Entry nm)}
  let enter (scp : scope) (sect : string) : scope =
    {
      nms = Sectioned.enter sect scp.nms;
      tps = Sectioned.enter sect scp.tps;
      prefix = sect :: scp.prefix;
    }
  let exit (scp : scope) : scope =
    {
      nms = Sectioned.exit scp.nms;
      tps = Sectioned.exit scp.tps;
      prefix = List.tl scp.prefix;
    }

  let ith (scp : scope) (i : idx) : name = Option.get @@ Sectioned.ith scp.nms scp.prefix i
  let ith_type (scp : scope) (i : idx) : name = Option.get @@ Sectioned.ith scp.tps scp.prefix i
end

(* all typechecking occurs inside a [scene]:

  ctx - maps variables to types

  ctors - associates data to a list of constructors
  parents - associates constructors to their parents

  tctx - maps type variables to kinds 
  env - maps type variables to values
  height - length of tctx, stored separately to avoid re-calculation
  
  scope - all the bound names (term and type level) locally visible
  prefix - the path leading to the current scope

  trace - a "call stack" of the type checker
*)
type ctx = vtyp list
type tctx = kind list
type trace = string list

type scene = {
  ctx : ctx;

  ctors : (name * name list) list;
  parents : (name * name) list;
  ctor_params : (name * vparam list) list;

  height : lvl;
  tctx : tctx;
  env : env;

  scope : scope;
  trace : trace;
}

let empty_scope : scope = {nms = ["", []]; tps = ["", []]; prefix = []}
let empty_scene : scene = {
  ctx = [];
  ctors = [];
  parents = [];
  ctor_params = [];
  height = Lvl 0;
  tctx = [];
  env = [];
  scope = empty_scope;
  trace = []
}

let assume (x : string) (t : vtyp) (scn : scene) : scene =
  {scn with
    ctx = t :: scn.ctx;
    scope = Scope.push scn.scope [x];
  }

let assume_typ (x : string) (k : kind) (fixed : [`ESolved | `EUnsolved]) (scn : scene) : scene =
  {scn with
    height = inc scn.height;
    tctx = k :: scn.tctx;
    env = (fixed, `EBound, vqvar scn.height) :: scn.env;
    scope = Scope.tpush scn.scope [x];
  }

let define_typ (x : string) (t : vtyp) (k : kind) (scn : scene) : scene =
  {scn with
    height = inc scn.height;
    tctx = k :: scn.tctx;
    env = (`ESolved, `EDefed, t) :: scn.env;
    scope = Scope.tpush scn.scope [x]
  }

let mask_of (scn : scene) : mask =
  List.map (fun (_, bound, _) -> bound) scn.env

let define_ctor_params (ctor : string) (params : vparam list) (scn : scene) : scene =
  {scn with
    ctor_params = (ctor :: scn.scope.prefix, params) :: scn.ctor_params
  }

let define_ctors (x : string) (ctors : string list) (scn : scene) : scene =
  let x = x :: scn.scope.prefix in
  let ctors = List.map (fun c -> c :: scn.scope.prefix) ctors in
  {scn with
    ctors = (x, ctors) :: scn.ctors;
    parents = List.map (fun c -> (c, x)) ctors @ scn.parents
  }

let lookup (nm : name) (scn : scene) : (idx * vtyp) option =
  match Sectioned.lookup scn.scope.nms scn.scope.prefix nm with
  | None -> None
  | Some (Idx i) ->
    let t = List.nth scn.ctx i in
    Some (Idx i, t)

let lookup_type (nm : name) (scn : scene) : (idx * kind) option =
  match Sectioned.lookup scn.scope.tps scn.scope.prefix nm with
  | None -> None
  | Some (Idx i) ->
    let k = List.nth scn.tctx i in
    Some (Idx i, k)

let log (scn : scene) (msg : string) : scene = {scn with trace = msg :: scn.trace}
let print_event (msg : string) : unit =
  print_endline @@ "while " ^ msg
let complain (scn : scene) (err : string) : unit =
  print_endline err;
  List.iter print_event scn.trace
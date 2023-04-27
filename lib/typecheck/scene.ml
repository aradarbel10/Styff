open Syntax.Core

module Sectioned = struct
  type entry =
  | Entry of name * lvl
  | Sect of trie
  | Alias of entry (* TODO consider a different solution than just copying the entire thing *)
  and trie = (string * entry) list

  let add_entry (x : string) (e : entry) : (string * trie) list -> (string * trie) list = function
  | [] -> failwith "internal error: can't add entry to empty scopes"
  | (topsect, top) :: rest -> (topsect, (x, e) :: top) :: rest
  let rec force_entry : entry -> entry = function
  | Alias e -> force_entry e
  | e -> e

  let rec lookup_path (t : trie) : name -> entry option = function
  | [] -> Some (Sect t)
  | x :: xs -> match (Option.map force_entry @@ List.assoc_opt x t), xs with
    | Some (Entry (nm, i)), [] -> Some (Entry (nm, i))
    | Some (Entry _), _ :: _ -> failwith ""
    | Some (Sect t), xs -> lookup_path t xs
    | _ -> None

  type t = {
    names : (string * trie) list; (* TODO: abstract layer to its own type *)
    height : int;
    prefix : name;
  }

  let full_names (t : t) : name list =
    let rec go_layers (ls : (string * trie) list) : name list =
      match ls with
      | [] -> []
      | (_, trie) :: ls -> List.append (go_trie trie) (go_layers ls)
    and go_trie (trie : trie) : name list =
      match trie with
      | [] -> []
      | (_, e) :: rest -> List.append (go_entry e) (go_trie rest)
    and go_entry : entry -> name list = function
    | Entry (full, _) -> [full]
    | Sect trie -> go_trie trie
    | Alias _ -> []
    in go_layers t.names

  let visible_names (t : t) : name list =
    let rec go_layers (ls : (string * trie) list) : name list =
      match ls with
      | [] -> []
      | (_, trie) :: ls -> List.append (go_trie [] trie) (go_layers ls)
    and go_trie (pre : name) (trie : trie) : name list =
      match trie with
      | [] -> []
      | (x, e) :: rest -> List.append (go_entry (pre @ [x]) e) (go_trie pre rest)
    and go_entry (pre : name) (e : entry) : name list =
      match e with
      | Entry _ -> [pre]
      | Sect trie -> go_trie pre trie
      | Alias e -> go_entry pre e
    in go_layers t.names

  let empty = {names = ["", []]; height = 0; prefix = []}
  let push {names; height; prefix} x = {
    names = add_entry x (Entry (List.rev (x :: prefix), Lvl height)) names;
    height = height + 1;
    prefix = prefix;
  }
  let lookup_entry (t : t) (x : name) : entry option =
    List.fold_left (fun found (_, top) -> match found with
    | Some _ -> found
    | None -> lookup_path top x
    ) None t.names
  let lookup {names; height; _} x =
    List.fold_left (fun found (_, top) -> match found with
    | Some _ -> found
    | None -> match lookup_path top x with
      | Some (Entry (full, lvl)) -> Some (full, lvl2idx (Lvl height) lvl)
      | _ -> None
    ) None names
  let at_idx t (Idx i) = List.nth (full_names t) i (* TODO: super inefficient, probably memoize this in a dedicated field *)
  let enter sect {names; height; prefix} = { (* TODO: change order of parameters for consistency *)
    names = (sect, []) :: names;
    height = height;
    prefix = sect :: prefix;
  }
  let exit {names; height; prefix} =
    match names with
    | (topsect, top) :: rest -> {
      names = add_entry topsect (Sect top) rest;
      height = height;
      prefix = List.tl prefix;
    }
    | _ -> failwith "internal error: can't exit a section when not inside any section"
  let alias (t : t) (new_nm : string) (old_nm : name) : t =
    match lookup_entry t old_nm with
    | Some e -> {t with names = add_entry new_nm (Alias e) t.names}
    | None -> failwith "can't alias a nonexistent name"
  let open_section (t : t) (sect : name) : t =
    match lookup_entry t sect with
    | Some (Sect es) ->
      let add_alias names (x, e) = add_entry x (Alias e) names in
      let names' = List.fold_left add_alias t.names es in
      {t with names = names'}
    | _ -> failwith "can't open an undefined section/name which doesn't refer to a section"
      (* TODO turn into a proper compilation error *)
    
end

type scope = {nms : Sectioned.t; tps : Sectioned.t}
module Scope = struct
  let push (scp : scope) (nm : string) : scope = {scp with nms = Sectioned.push scp.nms nm}
  let tpush (scp : scope) (nm : string) : scope = {scp with tps = Sectioned.push scp.tps nm}
  let enter (scp : scope) (sect : string) : scope = {
    nms = Sectioned.enter sect scp.nms;
    tps = Sectioned.enter sect scp.tps;
  }
  let exit (scp : scope) : scope = {
    nms = Sectioned.exit scp.nms;
    tps = Sectioned.exit scp.tps;
  }

  let ith (scp : scope) (i : idx) : name = Sectioned.at_idx scp.nms i
  let ith_type (scp : scope) (i : idx) : name = Sectioned.at_idx scp.tps i
  let open_section (scp : scope) (sect : name) : scope = {
    nms = Sectioned.open_section scp.nms sect;
    tps = Sectioned.open_section scp.tps sect;
  }
end

(* all typechecking occurs inside a [scene]:

  ctx - maps variables to types

  ctors - associates data to a list of constructors
  parents - associates constructors to their parents

  tctx - maps type variables to kinds 
  env - maps type variables to values
  height - length of tctx, stored separately to avoid re-calculation
  
  scope - all the bound names (term and type level) locally visible
  range - the range in source of the AST node currently processed
*)
type ctx = vtyp list
type tctx = kind list

type scene = {
  ctx : ctx;

  ctors : (name * name list) list;
  parents : (name * name) list;
  ctor_params : (name * vparam list) list;

  height : lvl;
  tctx : tctx;
  env : env;

  scope : scope;
  mutable range : src_range;
}

let empty_scope : scope = {nms = Sectioned.empty; tps = Sectioned.empty}
let empty_scene : scene = {
  ctx = [];
  ctors = [];
  parents = [];
  ctor_params = [];
  height = Lvl 0;
  tctx = [];
  env = [];
  scope = empty_scope;
  range = dummy_range;
}

let assume (x : string) (t : vtyp) (scn : scene) : scene =
  {scn with
    ctx = t :: scn.ctx;
    scope = Scope.push scn.scope x;
  }

let assume_typ (x : string) (k : kind) (fixed : [`ESolved | `EUnsolved]) (scn : scene) : scene =
  {scn with
    height = inc scn.height;
    tctx = k :: scn.tctx;
    env = (fixed, `EBound, vqvar scn.height) :: scn.env;
    scope = Scope.tpush scn.scope x;
  }

let define_typ (x : string) (t : vtyp) (k : kind) (scn : scene) : scene =
  {scn with
    height = inc scn.height;
    tctx = k :: scn.tctx;
    env = (`ESolved, `EDefed, t) :: scn.env;
    scope = Scope.tpush scn.scope x
  }

let mask_of (scn : scene) : mask =
  List.map (fun (_, bound, _) -> bound) scn.env

let define_ctor_params (ctor : string) (params : vparam list) (scn : scene) : scene =
  {scn with
    ctor_params = (List.rev (ctor :: scn.scope.nms.prefix), params) :: scn.ctor_params
  }

let define_ctors (x : string) (ctors : string list) (scn : scene) : scene =
  let x = List.rev (x :: scn.scope.tps.prefix) in
  let ctors = List.map (fun c -> List.rev (c :: scn.scope.nms.prefix)) ctors in
  {scn with
    ctors = (x, ctors) :: scn.ctors;
    parents = List.map (fun c -> (c, x)) ctors @ scn.parents
  }

let lookup (nm : name) (scn : scene) : (idx * vtyp) option =
  match Sectioned.lookup scn.scope.nms nm with
  | None -> None
  | Some (_, Idx i) ->
    let t = List.nth scn.ctx i in
    Some (Idx i, t)

let lookup_type (nm : name) (scn : scene) : (idx * kind) option =
  match Sectioned.lookup scn.scope.tps nm with
  | None -> None
  | Some (_, Idx i) ->
    let k = List.nth scn.tctx i in
    Some (Idx i, k)

let qualify (scn : scene) (x : string) : name = List.rev (x :: scn.scope.nms.prefix)
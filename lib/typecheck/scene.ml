open Syntax.Core
open Util

module Scope = struct
  type entry =
  | TermEntry of name * lvl (* TODO: still need to keep full names here? *)
  | TypeEntry of name * lvl
  | Sect of trie
  | OpenSect of trie
  | Alias of entry
  and trie = (string * entry) list
  type layer = (string * trie) list

  let isTermEntry : entry -> bool = function
  | TermEntry _ -> true
  | _ -> false

  let isTypeEntry : entry -> bool = function
  | TypeEntry _ -> true
  | _ -> false

  let add_entry (x : string) (e : entry) : layer -> layer = function
  | [] -> failwith "internal error: can't add entry to empty scopes"
  | (topsect, top) :: rest -> (topsect, (x, e) :: top) :: rest
  let rec force_entry : entry -> entry = function
  | Alias e -> force_entry e
  | e -> e
  
  (* backtracking search to find the trie branch fitting the given path *)
  let lookup_path (guard : entry -> bool) =
    let rec go_trie (t : trie) (nm : name) : entry option =
      match t, nm with
      | [], _ -> None
      | (_, e)::_, [] when guard e -> Some e
      | (x', OpenSect t)::rest, x::xs -> go_trie t nm <|> go_trie ((x', Sect t)::rest) (x::xs)
      | (x', e)::rest, x::xs when x = x' -> go_entry e xs <|> go_trie rest (x::xs)
      | _::rest, nm -> go_trie rest nm
    and go_entry (e : entry) (nm : name) : entry option =
      match force_entry e, nm with
      | e, [] when guard e -> Some e
      | Sect t, nm -> go_trie t nm
      | OpenSect _, _ -> failwith "absurd! should be intercepted in [go_trie]"
      | _ -> None
    in go_trie

  type t = {
    names : layer;
    prefix : name;
    term_height : int;
    type_height : int;
    term_scope : name list;
    type_scope : name list; (* TODO: abstract over syntactic classes *)
  }

  let visible_names (t : t) : name list * name list =
    let rec go_layers (ls : (string * trie) list) : name list * name list =
      match ls with
      | [] -> [], []
      | (_, trie) :: ls -> append2 (go_trie [] trie) (go_layers ls)
    and go_trie (pre : name) (trie : trie) : name list * name list =
      match trie with
      | [] -> [], []
      | (x, e) :: rest -> append2 (go_entry (pre @ [x]) e) (go_trie pre rest)
    and go_entry (pre : name) (e : entry) : name list * name list =
      match e with
      | TermEntry _ -> [pre], []
      | TypeEntry _ -> [], [pre]
      | Sect trie -> go_trie pre trie
      | Alias e -> go_entry pre e
      | OpenSect trie -> append2 (go_trie pre trie) (go_trie (List.tl pre) trie)
    in go_layers t.names

  let empty = {
    names = ["", []];
    prefix = [];
    term_height = 0;
    type_height = 0;
    term_scope = [];
    type_scope = [];
  }
  let push_term {names; prefix; term_height; type_height; term_scope; type_scope} x =
    let full = List.rev (x :: prefix) in
    {
      names = add_entry x (TermEntry (full, Lvl term_height)) names;
      prefix = prefix;
      term_height = term_height + 1;
      type_height = type_height;
      term_scope = full :: term_scope;
      type_scope = type_scope;
    }
  let push_type {names; prefix; term_height; type_height; term_scope; type_scope} x =
    let full = List.rev (x :: prefix) in
    {
      names = add_entry x (TypeEntry (full, Lvl type_height)) names;
      prefix = prefix;
      term_height = term_height;
      type_height = type_height + 1;
      term_scope = term_scope;
      type_scope = full :: type_scope;
    }
  let lookup_entry (t : t) (x : name) : entry option =
    List.fold_left (fun found (_, top) ->
      found <|> lookup_path (fun _ -> true) top x
    ) None t.names
  let lookup_term {names; term_height; _} x : (name * idx) option =
    List.fold_left (fun found (_, top) -> match found with
    | Some _ -> found
    | None -> match lookup_path isTermEntry top x with
      | Some (TermEntry (full, lvl)) -> Some (full, lvl2idx (Lvl term_height) lvl)
      | _ -> None
    ) None names
  let lookup_type {names; type_height; _} x : (name * idx) option =
    List.fold_left (fun found (_, top) -> match found with
    | Some _ -> found
    | None -> match lookup_path isTypeEntry top x with
      | Some (TypeEntry (full, lvl)) -> Some (full, lvl2idx (Lvl type_height) lvl)
      | _ -> None
    ) None names
  let ith_term t (Idx i) = List.nth t.term_scope i
  let ith_type t (Idx i) = List.nth t.type_scope i
  let enter t sect = {t with
    names = (sect, []) :: t.names;
    prefix = sect :: t.prefix;
  }
  let exit t (is_open : [`opened | `closed]) =
    match t.names with
    | (topsect, top) :: rest -> {t with
      names = add_entry topsect (match is_open with | `opened -> OpenSect top | `closed -> Sect top) rest;
      prefix = List.tl t.prefix;
    }
    | _ -> failwith "internal error: can't exit a section when not inside any section"
  let alias (t : t) (new_nm : string) (old_nm : name) : t =
    match lookup_entry t old_nm with
    | Some e -> {t with names = add_entry new_nm (Alias e) t.names}
    | None -> failwith "can't alias a nonexistent name"
      (* TODO turn into a proper compilation error *)
  let open_section (t : t) (sect : name) : t =
    match lookup_entry t sect with
    | Some (Sect es) ->
      let add_alias names (x, e) = add_entry x (Alias e) names in
      let names' = List.fold_left add_alias t.names es in
      {t with names = names'}
    | Some (OpenSect _) -> failwith "can't open an open-by-default section"
    | _ -> failwith "can't open an undefined section/name which doesn't refer to a section"
      (* TODO turn into a proper compilation error *)
    
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

  scope : Scope.t;
  mutable range : src_range;
}

let empty_scene : scene = {
  ctx = [];
  ctors = [];
  parents = [];
  ctor_params = [];
  height = Lvl 0;
  tctx = [];
  env = [];
  scope = Scope.empty;
  range = dummy_range;
}

let assume (x : string) (t : vtyp) (scn : scene) : scene =
  {scn with
    ctx = t :: scn.ctx;
    scope = Scope.push_term scn.scope x;
  }

let assume_typ (x : string) (k : kind) (fixed : [`ESolved | `EUnsolved]) (scn : scene) : scene =
  {scn with
    height = inc scn.height;
    tctx = k :: scn.tctx;
    env = (fixed, `EBound, vqvar scn.height) :: scn.env;
    scope = Scope.push_type scn.scope x;
  }

let define_typ (x : string) (t : vtyp) (k : kind) (scn : scene) : scene =
  {scn with
    height = inc scn.height;
    tctx = k :: scn.tctx;
    env = (`ESolved, `EDefed, t) :: scn.env;
    scope = Scope.push_type scn.scope x
  }

let mask_of (scn : scene) : mask =
  List.map (fun (_, bound, _) -> bound) scn.env
let qualify (scn : scene) (x : string) : name = List.rev (x :: scn.scope.prefix)


let define_ctor_params (ctor : string) (params : vparam list) (scn : scene) : scene =
  {scn with
    ctor_params = (qualify scn ctor, params) :: scn.ctor_params
  }

let define_ctors (x : string) (ctors : string list) (scn : scene) : scene =
  let x = qualify scn x in
  let ctors = List.map (qualify scn) ctors in
  {scn with
    ctors = (x, ctors) :: scn.ctors;
    parents = List.map (fun c -> (c, x)) ctors @ scn.parents
  }

let lookup_term (nm : name) (scn : scene) : (idx * vtyp) option =
  match Scope.lookup_term scn.scope nm with
  | None -> None
  | Some (_, Idx i) ->
    let t = List.nth scn.ctx i in
    Some (Idx i, t)

let lookup_type (nm : name) (scn : scene) : (idx * kind) option =
  match Scope.lookup_type scn.scope nm with
  | None -> None
  | Some (_, Idx i) ->
    let k = List.nth scn.tctx i in
    Some (Idx i, k)
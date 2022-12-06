open Syntax.Core

(* all typechecking occurs inside a [scene]:

  ctx - maps variables to types

  ctors - associates data to a list of constructors
  parents - associates constructors to their parents

  tctx - maps type variables to kinds 
  env - maps type variables to values
  height - length of tctx, stored separately to avoid re-calculation
  
  trace - a "call stack" of the type checker
*)
type ctx = (name * vtyp) list
type tctx = (name * kind) list
type trace = string list

type scene = {
  ctx : ctx;

  ctors : (name * name list) list;
  parents : (name * name) list;

  height : lvl;
  tctx : tctx;
  env : env;

  trace : trace;
}

let empty_scene : scene = {ctx = []; ctors = []; parents = []; height = Lvl 0; tctx = []; env = []; trace = []}
let names scn = List.map fst scn.ctx
let tps scn = List.map fst scn.tctx

let assume (scn : scene) (x : name) (t : vtyp) : scene =
  {scn with
    ctx = (x, t) :: scn.ctx;
  }

let assume_typ (scn : scene) (x : name) (k : kind) (fixed : [`ESolved | `EUnsolved]) : scene =
  {scn with
    height = inc scn.height;
    tctx = (x, k) :: scn.tctx;
    env = (x, fixed, `EBound, vqvar scn.height) :: scn.env;
  }

let define_typ (scn : scene) (x : name) (t : vtyp) (k : kind) : scene =
  {scn with
    height = inc scn.height;
    tctx = (x, k) :: scn.tctx;
    env = (x, `ESolved, `EDefed, t) :: scn.env;
  }

let mask_of (scn : scene) : mask =
  List.map (fun (_, _, bound, _) -> bound) scn.env

let define_ctors (scn : scene) (x : name) (ctors : name list) : scene =
  {scn with
    ctors = (x, ctors) :: scn.ctors;
    parents = List.map (fun c -> (c, x)) ctors @ scn.parents
  }

let log (scn : scene) (msg : string) : scene = {scn with trace = msg :: scn.trace}
let print_event (msg : string) : unit =
  print_endline @@ "while " ^ msg
let complain (scn : scene) (err : string) : unit =
  print_endline err;
  List.iter print_event scn.trace
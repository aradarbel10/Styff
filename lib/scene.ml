open Expr

(* all typechecking occurs inside a [scene]:

  ctx - maps variables to types

  ctors - associates data to a list of constructors
  parents - associates constructors to their parents

  tctx - maps type variables to kinds 
  env - maps type variables to values
  height - length of tctx, stored separately to avoid re-calculation *)
type ctx = (name * vtyp) list
type tctx = (name * kind) list
type scene = {
  ctx : ctx;

  ctors : (name * name list) list;
  parents : (name * name) list;

  height : lvl;
  tctx : tctx;
  env : env;
}

let empty_scene : scene = {ctx = []; ctors = []; parents = []; height = Lvl 0; tctx = []; env = []}
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
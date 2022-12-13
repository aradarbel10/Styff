open Syntax.Common
module Z = Syntax.Zonked

module Set = BatSet

module A = struct
  type pattern = name * name list
  type value =
  | Lit of lit
  | Var of name
  | Lam of name list * term
  and expr =
  | App of value * value list
  | Tup of value list
  | ProjAt of value * int
  and term =
  | Let of name * expr * term
  | Match of value * (pattern * term) list
  | Ret of value
end
let ret v = A.Ret v
let rhs v = A.App (v, [])

let rec to_anf (e : Z.expr) (c : A.value -> A.term) : A.term =
  let ( let* ) = to_anf in
  let erase_pat (PCtor (ctor, args)) : A.pattern =
    (ctor, List.filter_map (function | PVar x -> Some x | PTvar _ -> None) args)
  in

  match e with
  | Var x -> c @@ Var x
  | Lit l -> c (Lit l)
  | Lam (x, _, e) -> c @@ Lam ([x], to_anf e ret)
  | Tlam (_, _, e) -> to_anf e c
  | App (e1, e2) ->
    let* v1 = e1 in
    let* v2 = e2 in
    let x = freshen "v" in
    Let (x, App (v1, [v2]), 
      c @@ Var x)
  | Inst (e, _) -> to_anf e c
  | Let (x, e, e') ->
    let* v = e in
    Let (x, rhs v, to_anf e' c)
  | Match (e, bs) ->
    let* v = e in
    let bs = List.map (fun (p, b) -> (erase_pat p, to_anf b c)) bs in
    Match (v, bs)
  | Tup es ->
    let rec go_tup vs es : A.term =
      match es with
      | [] ->
        let v = freshen "v" in
        Let (v, Tup (List.rev vs), c (Var v))
      | e :: es ->
        let* v = e in
        go_tup (v :: vs) es
    in go_tup [] es
  | ProjAt (e, i) ->
    let x = freshen "x" in
    let* v = e in
    Let (x, ProjAt (v, i), c (Var x))


let free_vars (xs : name list) (e : A.term) : name list =
  let rec go_term : A.term -> name Set.t = function
  | Let (x, e, t) -> Set.union (Set.remove x (go_expr e)) (go_term t)
  | Match (v, bs) ->
    let v_bs = List.map (fun (p, b) -> Set.diff (go_term b) (go_pat p)) bs in
    List.fold_left Set.union (go_value v) v_bs
  | Ret v -> go_value v
  and go_expr : A.expr -> name Set.t = function
  | App (v, vs) ->
    let v_vs = List.map go_value vs in
    List.fold_left Set.union (go_value v) v_vs
  | Tup vs -> List.fold_left Set.union Set.empty (List.map go_value vs)
  | ProjAt (v, _) -> go_value v
  and go_value : A.value -> name Set.t = function
  | Lit _ -> Set.empty
  | Var x -> Set.singleton x
  | Lam (xs, t) -> Set.diff (go_term t) (Set.of_list xs)
  and go_pat ((_, args) : A.pattern) : name Set.t = Set.of_list args
  in
  Set.to_list (go_value (Lam (xs, e)))

let closure_conv =

  let rec go_term : A.term -> A.term = function
  | Let (x, e, t) -> go_expr e @@ fun v -> A.Let (x, v, go_term t)
  | Match (v, bs) -> Match (go_value v, List.map (fun (p, b) -> (p, go_term b)) bs)
  | Ret v -> Ret (go_value v)
  and go_expr (e : A.expr) (c : A.expr -> A.term) : A.term =
    match e with
    | App (v, vs) ->
      let v = go_value v in
      let vs = List.map go_value vs in

      let code = freshen "c" in
      let env = freshen "e" in

      Let (code, ProjAt (v, 1),
      Let (env, ProjAt (v, 2),
      c (App (Var code, Var env :: vs))))
    | Tup vs -> c @@ Tup (List.map go_value vs)
    | ProjAt (v, i) -> c @@ ProjAt (go_value v, i)
  and go_value : A.value -> A.value = function
  | Lit l -> Lit l
  | Var x -> Var x
  | Lam (xs, t) ->
    let fvs = List.mapi (fun i v -> (i, v)) (free_vars xs t) in
    let t = go_term t in

    let env = freshen "n" in

    (* unpack entire environment in function body *)
    let body = List.fold_right (fun (i, v) bod -> A.Let (v, ProjAt (Var env, i), bod)) fvs t in
    Lam (env :: xs, body)
  in
  go_term
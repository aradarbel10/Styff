open Syntax.Common
module Z = Syntax.Zonked

module K = struct
  type typ =
  | Qvar of name
  | Cont of (name * Z.kind) list * typ list (* → ⊥  in CPS the functions don't return *)
  | TApp of typ * typ
  | Prod of typ list
  | Base of base

  type value = naked_value * typ
  and naked_value =
  | Var of name
  | Lit of lit
  | Tup of value list
  | Abs of name * (name * Z.kind) list * (name * typ) list * expr
  and rhs =
  | Assgn of value
  | ProjAt of value * int
  and expr =
  | Let of name * rhs * expr
  | Call of value * typ list * value list
  | Match of value * (pattern * expr) list
  | Halt of value
end

let rec cps_of_type : Z.typ -> K.typ = function
| Qvar x -> Qvar x
| Arrow (lt, rt) -> Cont ([], [(cps_of_type lt); (cps_of_cont rt)])
| Forall (x, k, t) -> Cont ([(x, k)], [(cps_of_cont t)])
| Base b -> Base b
| TApp (t1, t2) -> TApp (cps_of_type t1, cps_of_type t2)
| TAbs _ -> failwith "todo"
| Prod ts -> Prod (List.map cps_of_type ts)
and cps_of_cont (t : Z.typ) : K.typ = Cont ([], [(cps_of_type t)])

let rec cps_of_expr ((e, e_typ) : Z.expr) (kont : K.value -> K.expr) : K.expr =
  let (let*) = cps_of_expr in

  match e with
  | Lit l ->
    let e_typ = cps_of_type e_typ in
    kont @@ (Lit l, e_typ)

  | Lam (x, x_typ, bod) ->
    let x_typ = cps_of_type x_typ in
    let bod_typ = cps_of_cont (snd bod) in
    let c = freshen "c" in
    let cont = intern_call c bod_typ in
    let bod = cps_of_expr bod cont in
    kont @@ (Abs ("", [], [x, x_typ; c, bod_typ], bod), cps_of_type e_typ)

  | Tlam (x, x_knd, bod) ->
    let bod_typ = cps_of_cont (snd bod) in
    let c = freshen "c" in
    let cont = intern_call c bod_typ in
    let bod = cps_of_expr bod cont in
    kont @@ (Abs ("", [x, x_knd], [c, bod_typ], bod), cps_of_type e_typ)

  | Var x ->
    kont @@ (Var x, cps_of_type e_typ)

  | App (e1, e2) ->
    let kont = reify_cont kont e_typ in
    let* v1 = e1 in
    let* v2 = e2 in
    Call (v1, [], [v2; kont])

  | Inst (e, t) ->
    let kont = reify_cont kont e_typ in
    let* v = e in
    let t = cps_of_type t in
    Call (v, [t], [kont])

  | Tup es ->
    let rec go (es : Z.expr list) (vacc : K.value list) (tacc : K.typ list) =
      match es with
      | [] -> kont (K.Tup vacc, K.Prod tacc)
      | e :: es ->
        let* v = e in
        let v_typ = snd v in
        go es (v :: vacc) (v_typ :: tacc)
    in
    go es [] []

  | Match (e, branches) ->
    let* v = e in
    let branches = List.map (fun (pat, branch) ->
      (pat, cps_of_expr branch kont)) branches in
    Match (v, branches)

  | ProjAt (e, i) ->
    let* v = e in
    let x = freshen "x" in
    let x_val = (K.Var x, cps_of_type e_typ) in
    Let (x, ProjAt (v, i), kont x_val)

  | Let (x, body, rest) ->
    let* body = body in
    Let (x, Assgn body, cps_of_expr rest kont)

and reify_cont (kont : K.value -> K.expr) (param_typ : Z.typ) : K.value =
  let v = freshen "v" in
  let param_typ = cps_of_type param_typ in
  let bod = kont (Var v, param_typ) in
  let cont = K.Abs ("", [], [(v, param_typ)], bod) in
  let cont_typ = K.Cont ([], [param_typ]) in
  (cont, cont_typ)
and intern_call (c : name) (t : K.typ) : K.value -> K.expr = fun v -> Call ((K.Var c, t), [], [v])

let cps_of_prog (e : Z.expr) : K.expr =
  cps_of_expr e (fun e -> Halt e)
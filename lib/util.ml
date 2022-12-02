let rec index_of (x : 'a) (xs : 'a list) : int =
  match xs with
  | [] -> raise Not_found
  | (x' :: xs') -> if x = x' then 0 else 1 + index_of x xs'

let level_of (x : 'a) (xs : 'a list) : int =
  List.length xs - index_of x xs - 1

let rec assoc_idx (x : 'a) (xs : ('a * 'b) list) : (int * 'b) option =
  match xs with
  | [] -> None
  | ((x', y) :: xs') ->
    if x = x' then Some (0, y) else
    match assoc_idx x xs' with
    | None -> None
    | Some (i, y') -> Some (i + 1, y')

let rec mem_once (y : 'a) (xs : 'a list) : bool =
  match xs with
  | [] -> false
  | x::xs ->
    if x = y
      then not (List.mem y xs)
      else mem_once y xs
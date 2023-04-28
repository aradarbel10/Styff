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

(* split the list to the `n`-long init and the rest, or if the list is too short return `None` *)
let rec split_at (i : int) (xs : 'a list) : ('a list * 'a list) option =
  if i < 0 then raise (Invalid_argument "split_at") else
  if i = 0 then Some ([], xs) else
  match xs with
  | [] -> None
  | x :: xs ->
    match split_at (i - 1) xs with
    | None -> None
    | Some (front, back) -> Some (x :: front, back)

let rec drop (n : int) (xs : 'a list) : 'a list =
  if n = 0 then xs else
  match xs with
  | [] -> []
  | _ :: xs -> drop (n - 1) xs

let take_or_less (n : int) (xs : 'a list) : 'a list * int option =
  match split_at n xs with
  | None -> xs, None
  | Some (xs, rest) -> xs, Some (List.length rest)

let diff (xs : 'a list) (ys : 'a list) : 'a list =
  List.filter (fun x -> not (List.mem x ys)) xs

let append2 (xs, ys : 'a list * 'b list) (xs', ys' : 'a list * 'b list) : 'a list * 'b list =
  List.append xs xs', List.append ys ys'
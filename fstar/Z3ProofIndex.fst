module Z3ProofIndex

let bind_opt (#a #b:Type) (x:option a) (f:a -> option b) : option b =
  match x with Some y -> f y | None -> None

let ( >>= ) = bind_opt

let rec opt_map (#a #b:Type) (f:a -> option b) (xs:list a)
  : Tot (option (list b)) (decreases xs) =
  match xs with
  | [] -> Some []
  | x :: rest ->
    (match f x, opt_map f rest with
     | Some y, Some ys -> Some (y :: ys)
     | _, _ -> None)

noeq
type index_tree (a:Type) =
  | Empty : index_tree a
  | Branch : option a -> index_tree a -> index_tree a -> index_tree a

let rec index_get (#a:Type) (tree:index_tree a) (key:nat)
  : Tot (option a) (decreases key) =
  match tree with
  | Empty -> None
  | Branch value left right ->
    if key = 0 then value
    else if key % 2 = 1 then index_get left ((key - 1) / 2)
    else index_get right ((key - 1) / 2)

let rec index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a)
  : Tot (index_tree a) (decreases key) =
  let old, left, right =
    match tree with
    | Empty -> None, Empty, Empty
    | Branch old left right -> old, left, right
  in
  if key = 0 then Branch (Some value) left right
  else if key % 2 = 1 then Branch old (index_put left ((key - 1) / 2) value) right
  else Branch old left (index_put right ((key - 1) / 2) value)

let index_find (#a:Type) (tree:index_tree a) (key:int) : option a =
  if key < 0 then None else index_get tree key

let rec lemma_index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a) (query:nat)
  : Lemma (index_get (index_put tree key value) query ==
           (if query = key then Some value else index_get tree query))
          (decreases key) =
  if key = 0 || query = 0 then ()
  else
    let left, right =
      match tree with Empty -> Empty, Empty | Branch _ left right -> left, right
    in
    if key % 2 = query % 2 then
      lemma_index_put (if key % 2 = 1 then left else right)
        ((key - 1) / 2) value ((query - 1) / 2)

module Z3IndependentProofIndex

module IX = Z3ProofIndex

let rec depth (key:nat) : Tot pos (decreases key) =
  if key = 0 then 1 else 1 + depth ((key - 1) / 2)

let rec get_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat)
  : Tot (option (option a & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match tree with
    | IX.Empty -> Some (None, 1)
    | IX.Branch value left right ->
      if key = 0 then Some (value, 1)
      else
        let child = if key % 2 = 1 then left else right in
        match get_metered (fuel - 1) child ((key - 1) / 2) with
        | None -> None
        | Some (result, work) -> Some (result, work + 1)

let rec lemma_get_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat)
  : Lemma (match get_metered fuel tree key with
           | None -> fuel < depth key
           | Some (result, work) ->
             result == IX.index_get tree key /\ 0 < work /\
             work <= fuel /\ work <= depth key)
          (decreases fuel) =
  if fuel = 0 then ()
  else
    match tree with
    | IX.Empty -> ()
    | IX.Branch _ left right ->
      if key > 0 then
        lemma_get_metered (fuel - 1)
          (if key % 2 = 1 then left else right) ((key - 1) / 2)

let rec put_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat) (value:a)
  : Tot (option (IX.index_tree a & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    let old, left, right =
      match tree with
      | IX.Empty -> None, IX.Empty, IX.Empty
      | IX.Branch old left right -> old, left, right
    in
    if key = 0 then Some (IX.Branch (Some value) left right, 1)
    else if key % 2 = 1 then
      match put_metered (fuel - 1) left ((key - 1) / 2) value with
      | None -> None
      | Some (result, work) -> Some (IX.Branch old result right, work + 1)
    else
      match put_metered (fuel - 1) right ((key - 1) / 2) value with
      | None -> None
      | Some (result, work) -> Some (IX.Branch old left result, work + 1)

let rec lemma_put_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat) (value:a)
  : Lemma (match put_metered fuel tree key value with
           | None -> fuel < depth key
           | Some (result, work) ->
             result == IX.index_put tree key value /\ work == depth key /\ work <= fuel)
          (decreases fuel) =
  if fuel = 0 || key = 0 then ()
  else
    let left, right =
      match tree with
      | IX.Empty -> IX.Empty, IX.Empty
      | IX.Branch _ left right -> left, right
    in
    lemma_put_metered (fuel - 1)
      (if key % 2 = 1 then left else right) ((key - 1) / 2) value

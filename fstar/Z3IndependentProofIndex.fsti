module Z3IndependentProofIndex

module IX = Z3ProofIndex

val depth (key:nat) : Tot pos
val get_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat)
  : Tot (option (option a & nat))
val lemma_get_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat)
  : Lemma (match get_metered fuel tree key with
           | None -> fuel < depth key
           | Some (result, work) ->
             result == IX.index_get tree key /\ 0 < work /\
             work <= fuel /\ work <= depth key)
val put_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat) (value:a)
  : Tot (option (IX.index_tree a & nat))
val lemma_put_metered (#a:Type) (fuel:nat) (tree:IX.index_tree a) (key:nat) (value:a)
  : Lemma (match put_metered fuel tree key value with
           | None -> fuel < depth key
           | Some (result, work) ->
             result == IX.index_put tree key value /\ work == depth key /\ work <= fuel)

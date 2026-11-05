module Z3IdTable

module I = Z3ProofIndex

let t a = I.index_tree a

let empty #a = I.Empty

let find #a tbl key = I.index_find tbl key

let put #a tbl key value = I.index_put tbl key value

let lemma_find_empty #a key = ()

let lemma_find_put #a tbl key value query =
  if query >= 0 then I.lemma_index_put tbl key value query

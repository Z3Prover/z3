module Z3IdTable

module L = FStar.List.Tot
module A = FStar.ImmutableArray

let t a = A.t (option a)

let rec lemma_index_snoc (#a:Type) (xs:list a) (v:a) (i:nat{i < L.length xs + 1})
  : Lemma (ensures L.length (L.append xs [v]) == L.length xs + 1 /\
                   L.index (L.append xs [v]) i == (if i < L.length xs then L.index xs i else v))
          (decreases xs) =
  L.append_length xs [v];
  match xs with
  | [] -> ()
  | _ :: rest -> if i = 0 then () else lemma_index_snoc rest v (i - 1)

let lemma_push (#a:Type) (s:A.t a) (v:a) (i:nat)
  : Lemma (ensures A.length (A.push s v) == A.length s + 1 /\
                   (i < A.length s + 1 ==>
                    A.index (A.push s v) i == (if i < A.length s then A.index s i else v))) =
  A.length_spec s;
  A.length_spec (A.push s v);
  if i < A.length s + 1 then lemma_index_snoc (A.to_list s) v i
  else L.append_length (A.to_list s) [v]

let empty #a = A.of_list []

let find #a tbl key = if key < 0 || key >= A.length tbl then None else A.index tbl key

let rec pad (#a:Type0) (tbl:t a) (n:nat)
  : Tot (r:t a{A.length r == A.length tbl + n /\
               (forall (i:int). find r i == find tbl i)}) (decreases n) =
  if n = 0 then tbl
  else (
    let tbl' = A.push tbl None in
    let aux (i:int) : Lemma (find tbl' i == find tbl i) =
      if i >= 0 then lemma_push tbl None i in
    lemma_push tbl None 0;
    FStar.Classical.forall_intro aux;
    pad tbl' (n - 1))

let put #a tbl key value =
  if key < A.length tbl then A.upd tbl key (Some value)
  else A.push (pad tbl (key - A.length tbl)) (Some value)

let lemma_find_empty #a key = A.length_spec (A.of_list #(option a) [])

let lemma_find_put #a tbl key value query =
  if key < A.length tbl then ()
  else (
    let padded = pad tbl (key - A.length tbl) in
    assert (find padded query == find tbl query);
    if query >= 0 then lemma_push padded (Some value) query
    else lemma_push padded (Some value) 0)

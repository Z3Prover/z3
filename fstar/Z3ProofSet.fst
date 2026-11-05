module Z3ProofSet

open Z3ProofIndex
module L = FStar.List.Tot

type set (a:eqtype) = index_tree (list a)

let key (#a:eqtype) (hash:a -> nat) (value:a) : nat =
  hash value % 65521

let member (#a:eqtype) (hash:a -> nat) (value:a) (s:set a) : bool =
  match index_get s (key hash value) with
  | Some bucket -> L.mem value bucket
  | None -> false

let insert (#a:eqtype) (hash:a -> nat) (value:a) (s:set a) : set a =
  let bucket = match index_get s (key hash value) with Some xs -> xs | None -> [] in
  index_put s (key hash value) (value :: bucket)

let lemma_insert (#a:eqtype) (hash:a -> nat) (value query:a) (s:set a)
  : Lemma (member hash query (insert hash value s) ==
           (query = value || member hash query s))
  = let bucket = match index_get s (key hash value) with Some xs -> xs | None -> [] in
    lemma_index_put s (key hash value) (value :: bucket) (key hash query);
    if key hash query = key hash value then
      (match index_get s (key hash value) with Some _ -> () | None -> ())
    else ()

let rec insert_all (#a:eqtype) (hash:a -> nat) (xs:list a) (old:set a)
  : Tot (s:set a{forall (query:a).
      member hash query s == (L.mem query xs || member hash query old)})
        (decreases xs) =
  match xs with
  | [] -> old
  | value :: rest ->
    let next = insert hash value old in
    let result = insert_all hash rest next in
    let queries (query:a)
      : Lemma (member hash query result == (L.mem query xs || member hash query old))
      = lemma_insert hash value query old in
    FStar.Classical.forall_intro queries;
    result

let of_list (#a:eqtype) (hash:a -> nat) (xs:list a)
  : Tot (s:set a{forall (query:a). member hash query s == L.mem query xs}) =
  insert_all hash xs Empty

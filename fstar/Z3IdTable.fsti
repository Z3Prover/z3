module Z3IdTable

(* Finite maps from proof ids to values, for the per-entry caches of proof
   checking.  Ids are usually allocated densely from zero.  The verified
   (and OCaml) implementation, Z3IdTable.fst, is a binary trie with logarithmic
   access.  The Cherry implementation, Z3IdTable-c.cherry.fst, is an immutable
   array, which Cherry updates in place when the table is not shared; [put] at
   the next unused id is then amortized constant time. *)

val t (a:Type0) : Type0

val empty (#a:Type0) : t a

val find (#a:Type0) (tbl:t a) (key:int) : option a

val put (#a:Type0) (tbl:t a) (key:nat) (value:a) : t a

val lemma_find_empty (#a:Type0) (key:int)
  : Lemma (find (empty #a) key == None)
          [SMTPat (find (empty #a) key)]

val lemma_find_put (#a:Type0) (tbl:t a) (key:nat) (value:a) (query:int)
  : Lemma (find (put tbl key value) query == (if query = key then Some value else find tbl query))
          [SMTPat (find (put tbl key value) query)]

module Z3SatPopShrink
(* Model of sat2goal::mc::m_var2expr after PR 11481: a vector of optional
   expression ids. shrink(n) is guarded by n < size as in the C++ code. *)
open FStar.Seq

type vec = seq (option nat)

let get (v:vec) (i:nat) : option nat = if i < length v then index v i else None

let shrink (v:vec) (n:nat) : vec = if n < length v then slice v 0 n else v

(* O1: no popped variable (>= n) keeps an expression. *)
let o1 (v:vec) (n:nat) (i:nat)
  : Lemma (requires i >= n) (ensures get (shrink v n) i == None) = ()

(* O2: variables below n keep their expression. *)
let o2 (v:vec) (n:nat) (i:nat)
  : Lemma (requires i < n) (ensures get (shrink v n) i == get v i) = ()

(* O3: the guard never grows the vector (shrink to larger n is identity). *)
let o3 (v:vec) (n:nat)
  : Lemma (ensures length (shrink v n) <= length v /\ (n >= length v ==> shrink v n == v)) = ()

(* Reachable witness of the bug on base: without shrink, a reused number
   (var 2, popped, new num_vars = 2) still maps to the old expression. *)
let old_vec : vec = Seq.cons None (Seq.cons None (Seq.cons (Some 5) Seq.empty))
let base_witness () : Lemma (get old_vec 2 == Some 5 /\ get (shrink old_vec 2) 2 == None) =
  assert (length old_vec == 3);
  assert (index old_vec 2 == Some 5)

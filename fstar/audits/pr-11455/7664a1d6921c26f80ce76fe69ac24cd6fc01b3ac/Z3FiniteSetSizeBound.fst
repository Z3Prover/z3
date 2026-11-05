module Z3FiniteSetSizeBound
(* Audit of PR 11455: finite_set_axioms::size_ub_axiom now emits
   set.size(S) <= N when elem_sort->get_num_elements().is_finite() with size N.
   Model: the element sort is the index range [0,N); a finite set is its
   membership predicate on that range; set.size counts members. *)

type sort_size =
  | Finite : nat -> sort_size
  | VeryBig : sort_size
  | Infinite : sort_size

let rec count (f:nat -> bool) (n:nat) : Tot nat (decreases n) =
  if n = 0 then 0 else count f (n-1) + (if f (n-1) then 1 else 0)

(* Guard from the PR: bound emitted only for exactly-finite sorts. *)
let emitted_bound (s:sort_size) : option nat =
  match s with Finite n -> Some n | _ -> None

(* O1: soundness of the new axiom: every set over a domain of N elements
   has size <= N. *)
let rec lemma_size_le_domain (f:nat -> bool) (n:nat)
  : Lemma (ensures count f n <= n) (decreases n)
  = if n = 0 then () else lemma_size_le_domain f (n-1)

(* O2: no over-restriction: the bound is attained (full set), so the axiom
   never excludes a valid cardinality. *)
let rec lemma_bound_tight (n:nat)
  : Lemma (ensures count (fun _ -> true) n = n) (decreases n)
  = if n = 0 then () else lemma_bound_tight (n-1)

(* O3: every size k in [0,N] is realisable by a prefix set, so the bound
   excludes no satisfiable cardinality. *)
let rec lemma_prefix (k:nat) (n:nat)
  : Lemma (ensures count (fun i -> i < k) n = (if k < n then k else n)) (decreases n)
  = if n = 0 then () else lemma_prefix k (n-1)

(* O4: motivating instance. FiniteSet Bool (N=2) cannot have size 3. *)
let lemma_bool_size3 (f:nat -> bool) : Lemma (count f 2 <> 3) = lemma_size_le_domain f 2

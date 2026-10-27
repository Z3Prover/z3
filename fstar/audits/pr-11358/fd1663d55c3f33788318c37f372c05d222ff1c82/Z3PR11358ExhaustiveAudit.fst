module Z3PR11358ExhaustiveAudit
(* Self-contained re-statement of the integer/list-level control logic of the PR's
   exhaustive_clause (Z3FiniteFieldLemma.fst at fd1663d5): within_budget,
   for_all_vectors/for_all_heads and vector_value. The PR module is not imported. *)
module L = FStar.List.Tot
module M = FStar.Math.Lemmas

let max_assignments : nat = 4096

let rec within_budget (p:int) (n:nat) (acc:int) : Tot bool (decreases n) =
  if acc > max_assignments then false
  else if n = 0 then true
  else within_budget p (n - 1) (acc * p)

let rec power (p:int) (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else p * power p (n - 1)

(* O1: entering enumeration implies acc * p^n <= max_assignments. *)
let rec lemma_within_budget (p:pos) (n:nat) (acc:pos)
  : Lemma (requires within_budget p n acc) (ensures acc * power p n <= max_assignments)
          (decreases n)
  = if n = 0 then ()
    else (lemma_within_budget p (n - 1) (acc * p);
          M.paren_mul_right acc p (power p (n - 1)))

let with_head (f:list int -> bool) (x:int) (r:list int) : bool = f (x :: r)

let rec for_all_vectors (p:nat) (n:nat) (f:list int -> bool) : Tot bool (decreases %[n; 0; 0]) =
  if n = 0 then f [] else for_all_heads p p (n - 1) f

and for_all_heads (p:nat) (k:nat) (n:nat) (f:list int -> bool) : Tot bool (decreases %[n; 1; k]) =
  if k = 0 then true
  else for_all_vectors p n (with_head f (k - 1)) && for_all_heads p (k - 1) n f

let rec in_range (p:int) (r:list int) : Tot bool (decreases r) =
  match r with
  | [] -> true
  | x :: rest -> 0 <= x && x < p && in_range p rest

(* O2: coverage; every length-n vector of residues in [0,p) satisfies f. *)
let rec lemma_for_all_vectors (p:nat) (n:nat) (f:list int -> bool) (r:list int)
  : Lemma (requires for_all_vectors p n f /\ L.length r == n /\ in_range p r)
          (ensures f r) (decreases %[n; 0; 0])
  = match r with
    | [] -> ()
    | x :: rest -> lemma_for_all_heads p p (n - 1) f x rest

and lemma_for_all_heads (p:nat) (k:nat) (n:nat) (f:list int -> bool) (x:int) (rest:list int)
  : Lemma (requires for_all_heads p k n f /\ 0 <= x /\ x < k /\ L.length rest == n /\ in_range p rest)
          (ensures f (x :: rest)) (decreases %[n; 1; k])
  = if x = k - 1 then lemma_for_all_vectors p n (with_head f (k - 1)) rest
    else lemma_for_all_heads p (k - 1) n f x rest

let vector_value (r:list int) : nat -> int =
  fun k -> if k < L.length r then L.index r k else 0

(* O3: for an in-range vector of length n, every leaf index k < n gets a residue in [0,p). *)
let rec lemma_index_in_range (p:int) (r:list int) (k:nat)
  : Lemma (requires in_range p r /\ k < L.length r)
          (ensures 0 <= L.index r k /\ L.index r k < p) (decreases r)
  = match r with
    | _ :: rest -> if k = 0 then () else lemma_index_in_range p rest (k - 1)

let lemma_vector_value_range (p:int) (r:list int) (k:nat)
  : Lemma (requires in_range p r /\ k < L.length r)
          (ensures 0 <= vector_value r k /\ vector_value r k < p)
  = lemma_index_in_range p r k

(* Composition: if the enumeration succeeds, the predicate holds on every in-range assignment. *)
let lemma_exhaustive (p:nat) (n:nat) (f:list int -> bool) (r:list int)
  : Lemma (requires for_all_vectors p n f /\ L.length r == n /\ in_range p r)
          (ensures f r /\ (forall (k:nat). k < n ==> 0 <= vector_value r k /\ vector_value r k < p))
  = lemma_for_all_vectors p n f r;
    FStar.Classical.forall_intro (fun (k:nat) ->
      FStar.Classical.move_requires (lemma_vector_value_range p r) k)

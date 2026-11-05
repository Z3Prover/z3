(*
   Z3SeqIndexOf.fst

   Soundness proofs for the `str.indexof`/`str.last_indexof`/`str.replace`
   axioms of src/ast/seq/seq_axioms.cpp (`seq::axioms::indexof_axiom`,
   `last_indexof_axiom`, `replace_axiom`). These all pivot on "first
   (or last) occurrence of a pattern in a sequence", which is modeled
   here via ground-truth functions `first_occ`/`last_occ`, rather than
   reconstructed solely from Skolem witnesses + `tightest_prefix`-style
   side conditions (the Z3 encoding's approach). Proving the clauses
   against this ground-truth model is what "soundness" means here: Z3's
   clause-based characterization and this direct definition agree.

   `replace_all_axiom` (seq_axioms.cpp:1325-1379) is not formalized: the
   C++ implementation itself is incomplete and unconditionally throws
   `default_exception("no support for replace-all")` (seq_axioms.cpp:1354,
   dead code below guarded by `#if 0`), so there is no shipped behavior
   to verify.
*)
module Z3SeqIndexOf

open Z3SeqTheory
open Z3SeqRewrites
open Z3SeqAxioms

(* len s == 0 <=> s == empty. Small bridging fact, proved locally to
   avoid a cross-module dependency on the regex development. *)
let rec lemma_len_zero_iff_empty (#a:eqtype) (s:seq a)
  : Lemma (ensures (len s == 0) == (s == empty))
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_len_zero_iff_empty s'

(* ================================================================= *)
(* A generic "occurrence at position k decomposes the sequence"        *)
(* helper, shared by the first_occ and last_occ developments below.    *)
(* ================================================================= *)

(* If `pat` occurs at position k in t (i.e. is a prefix of the suffix
   starting there), then t decomposes as (take t k) ++ pat ++ (the
   remaining suffix), and the prefix part has length exactly k. *)
let lemma_is_prefix_at_decompose (#a:eqtype) (t pat:seq a) (k:nat)
  : Lemma (requires k <= len t /\ is_prefix pat (drop t k))
          (ensures concat (concat (take t k) pat) (drop t (k + len pat)) == t
                   /\ len (take t k) == k)
  = lemma_prefix_extract_reconstruct pat (drop t k);
    lemma_drop_drop t k (len pat);
    lemma_take_drop_reconstruct t k;
    lemma_concat_assoc (take t k) pat (drop t (k + len pat));
    lemma_len_take t k

(* ================================================================= *)
(* first_occ / index_of : ground-truth "first occurrence" model        *)
(* ================================================================= *)

(* first_occ t pat : the smallest k such that `pat` is a prefix of
   `drop t k`, or None if no such k exists (i.e. `pat` does not occur
   anywhere in `t`). *)
let rec first_occ (#a:eqtype) (t pat:seq a) : Tot (option nat) (decreases t)
  = if is_prefix pat t then Some 0
    else
      match t with
      | [] -> None
      | _ :: t' ->
        (match first_occ t' pat with
         | None -> None
         | Some k -> Some (k + 1))

(* str.indexof(t, pat, off) (both the 2-arg form, off = 0, and the
   3-arg form). *)
let index_of (#a:eqtype) (t pat:seq a) (off:int) : int =
  if off < 0 || off > len t then -1
  else
    match first_occ (drop t off) pat with
    | None -> -1
    | Some k -> off + k

(* `first_occ` finds an occurrence exactly when `contains` says there
   is one. *)
let rec lemma_first_occ_some_iff_contains (#a:eqtype) (t pat:seq a)
  : Lemma (ensures Some? (first_occ t pat) == contains t pat)
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' -> if is_prefix pat t then () else lemma_first_occ_some_iff_contains t' pat

(* `contains` is monotone under taking a (later) suffix: if a suffix of
   t contains pat, so does t itself. Used for indexof_axiom's clauses
   that hold "for any offset" once `~contains t pat` is known. *)
let rec lemma_contains_drop_mono (#a:eqtype) (t pat:seq a) (off:nat)
  : Lemma (ensures contains (drop t off) pat ==> contains t pat)
          (decreases off)
  = if off = 0 then ()
    else
      match t with
      | [] -> ()
      | _ :: t' -> lemma_contains_drop_mono t' pat (off - 1)

(* first_occ's witness is within bounds. *)
let rec lemma_first_occ_bound (#a:eqtype) (t pat:seq a)
  : Lemma (requires Some? (first_occ t pat))
          (ensures Some?.v (first_occ t pat) <= len t)
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' -> if is_prefix pat t then () else lemma_first_occ_bound t' pat

(* first_occ's witness really is an occurrence position. *)
let rec lemma_first_occ_is_prefix (#a:eqtype) (t pat:seq a)
  : Lemma (requires Some? (first_occ t pat))
          (ensures is_prefix pat (drop t (Some?.v (first_occ t pat))))
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' -> if is_prefix pat t then () else lemma_first_occ_is_prefix t' pat

(* Full decomposition at the first-occurrence position. *)
let lemma_first_occ_decompose (#a:eqtype) (t pat:seq a)
  : Lemma (requires Some? (first_occ t pat))
          (ensures (let k = Some?.v (first_occ t pat) in
                      concat (concat (take t k) pat) (drop t (k + len pat)) == t
                      /\ len (take t k) == k))
  = lemma_first_occ_bound t pat;
    lemma_first_occ_is_prefix t pat;
    lemma_is_prefix_at_decompose t pat (Some?.v (first_occ t pat))

(* first_occ finds the *first* (smallest) occurrence: no smaller
   offset admits `pat` as a prefix of the corresponding suffix. This is
   the ground-truth counterpart of `tightest_prefix`. *)
let rec lemma_first_occ_minimal (#a:eqtype) (t pat:seq a)
  : Lemma (requires Some? (first_occ t pat))
          (ensures (let k = Some?.v (first_occ t pat) in
                      forall (j:nat). j < k ==> ~(is_prefix pat (drop t j))))
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' ->
      if is_prefix pat t then ()
      else lemma_first_occ_minimal t' pat

(* ================================================================= *)
(* indexof_axiom, seq_axioms.cpp:431-561                               *)
(* ================================================================= *)

(* i >= -1, always. *)
let lemma_indexof_ge_m1 (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (ensures index_of t pat off >= -1)
  = ()

(* ~contains(t,pat) ==> indexof(t,pat,off) = -1, for every offset. *)
let lemma_indexof_not_contains (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (requires ~(contains t pat))
          (ensures index_of t pat off == -1)
  = if off < 0 || off > len t then ()
    else
      (match first_occ (drop t off) pat with
       | None -> ()
       | Some _ ->
         lemma_first_occ_some_iff_contains (drop t off) pat;
         lemma_contains_drop_mono t pat off)

(* len t = 0 ==> len pat = 0 \/ indexof(t,pat,off) = -1. *)
let lemma_indexof_empty_t (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (requires len t == 0)
          (ensures len pat == 0 \/ index_of t pat off == -1)
  = if len pat = 0 then ()
    else begin
      lemma_prefix_of_empty pat;
      lemma_first_occ_some_iff_contains t pat
    end

(* len pat = 0 ==> indexof(t,pat,0) = 0 (offset-0 form). *)
let lemma_indexof_empty_pat (#a:eqtype) (t pat:seq a)
  : Lemma (requires len pat == 0)
          (ensures index_of t pat 0 == 0)
  = lemma_prefix_empty t

(* contains(t,pat) /\ len pat > 0 ==>
     exists x y. t = x ++ pat ++ y /\ len x = indexof(t,pat,0)
   with x,y instantiated to (take t k)/(drop t (k+len pat)),
   k = indexof(t,pat,0), and no smaller position also matches. This is
   the soundness statement for indexof_axiom's Skolem-based
   decomposition clauses (`m_sk.mk_indexof_left/right`) together with
   `tightest_prefix`. *)
let lemma_indexof_decompose (#a:eqtype) (t pat:seq a)
  : Lemma (requires contains t pat /\ len pat > 0)
          (ensures (let k = index_of t pat 0 in
                      k >= 0
                      /\ concat (concat (take t k) pat) (drop t (k + len pat)) == t
                      /\ len (take t k) == k
                      /\ (forall (j:nat). j < k ==> ~(is_prefix pat (drop t j)))))
  = lemma_first_occ_some_iff_contains t pat;
    lemma_first_occ_decompose t pat;
    lemma_first_occ_minimal t pat

(* offset >= len t /\ len pat > 0 ==> indexof(t,pat,offset) = -1. *)
let lemma_indexof_offset_ge_len_nonempty (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (requires off >= len t /\ len pat > 0)
          (ensures index_of t pat off == -1)
  = if off > len t then ()
    else begin
      // off = len t : drop t off = empty, and `pat` (nonempty) is not
      // a prefix of empty.
      lemma_drop_all t;
      lemma_prefix_of_empty pat
    end

(* offset = len t /\ len pat = 0 ==> indexof(t,pat,offset) = offset. *)
let lemma_indexof_offset_eq_len_empty_pat (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (requires off == len t /\ len pat == 0)
          (ensures index_of t pat off == off)
  = lemma_drop_all t;
    lemma_prefix_empty (drop t off)

(* offset < 0 ==> indexof(t,pat,offset) = -1 : immediate from the
   definition of `index_of`. *)
let lemma_indexof_offset_neg (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (requires off < 0) (ensures index_of t pat off == -1)
  = ()

(* 0 <= offset <= len t ==>
     t = x ++ y /\ len x = offset /\
     (indexof(y,pat,0) = -1 ==> indexof(t,pat,offset) = -1) /\
     (indexof(y,pat,0) >= 0 ==> indexof(t,pat,offset) = indexof(y,pat,0) + offset)
   with x,y := (take t offset)/(drop t offset). This is the soundness
   statement for indexof_axiom's offset-shifting recursion
   (`m_sk.mk_indexof_left/right(t,pat,offset)` + the recursive call to
   `indexof(y,pat,0)`); both sides unfold to the same `first_occ y pat`
   match, shifted by `off`. *)
let lemma_indexof_offset_shift (#a:eqtype) (t pat:seq a) (off:int)
  : Lemma (requires 0 <= off /\ off <= len t)
          (ensures (let y = drop t off in
                      concat (take t off) y == t
                      /\ len (take t off) == off
                      /\ (index_of y pat 0 == -1 ==> index_of t pat off == -1)
                      /\ (index_of y pat 0 >= 0 ==> index_of t pat off == index_of y pat 0 + off)))
  = lemma_take_drop_reconstruct t off;
    lemma_len_take t off

(* ================================================================= *)
(* last_indexof_axiom, seq_axioms.cpp:563-608                          *)
(*                                                                      *)
(* `str.last_indexof` is modeled directly as a right-to-left scan       *)
(* (`last_occ`), preferring a later match over an earlier one, rather   *)
(* than going through `reverse` (keeping the proofs structurally        *)
(* parallel to `first_occ` above).                                      *)
(* ================================================================= *)

let rec last_occ (#a:eqtype) (t pat:seq a) : Tot (option nat) (decreases t)
  = match t with
    | [] -> if is_prefix pat empty then Some 0 else None
    | _ :: t' ->
      (match last_occ t' pat with
       | Some k -> Some (k + 1)
       | None -> if is_prefix pat t then Some 0 else None)

let last_index_of (#a:eqtype) (t pat:seq a) : int =
  match last_occ t pat with
  | None -> -1
  | Some k -> k

let rec lemma_last_occ_some_iff_contains (#a:eqtype) (t pat:seq a)
  : Lemma (ensures Some? (last_occ t pat) == contains t pat)
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' -> lemma_last_occ_some_iff_contains t' pat

let rec lemma_last_occ_bound (#a:eqtype) (t pat:seq a)
  : Lemma (requires Some? (last_occ t pat))
          (ensures Some?.v (last_occ t pat) <= len t)
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' ->
      (match last_occ t' pat with
       | Some _ -> lemma_last_occ_bound t' pat
       | None -> ())

let rec lemma_last_occ_is_prefix (#a:eqtype) (t pat:seq a)
  : Lemma (requires Some? (last_occ t pat))
          (ensures is_prefix pat (drop t (Some?.v (last_occ t pat))))
          (decreases t)
  = match t with
    | [] -> ()
    | _ :: t' ->
      (match last_occ t' pat with
       | Some _ -> lemma_last_occ_is_prefix t' pat
       | None -> ())

(* ~contains(t,pat) ==> last_indexof(t,pat) = -1. *)
let lemma_last_indexof_not_contains (#a:eqtype) (t pat:seq a)
  : Lemma (requires ~(contains t pat))
          (ensures last_index_of t pat == -1)
  = lemma_last_occ_some_iff_contains t pat

(* len t = 0 ==> len pat = 0 \/ last_indexof(t,pat) = -1. *)
let lemma_last_indexof_empty_t (#a:eqtype) (t pat:seq a)
  : Lemma (requires len t == 0)
          (ensures len pat == 0 \/ last_index_of t pat == -1)
  = if len pat = 0 then () else lemma_prefix_of_empty pat

(* len pat = 0 ==> last_indexof(t,pat) = len t : the empty pattern's
   last (and only reachable) occurrence is recorded at the very end. *)
let rec lemma_last_indexof_empty_pat (#a:eqtype) (t pat:seq a)
  : Lemma (requires len pat == 0)
          (ensures last_index_of t pat == len t)
          (decreases t)
  = lemma_len_zero_iff_empty pat;
    lemma_prefix_empty (empty #a);
    match t with
    | [] -> ()
    | _ :: t' -> lemma_last_indexof_empty_pat t' pat

(* contains(t,pat) ==> t = x ++ pat ++ y with len x = last_indexof(t,pat),
   i.e. the same decomposition fact as for `first_occ`, instantiated at
   the *last* occurrence position. *)
let lemma_last_indexof_decompose (#a:eqtype) (t pat:seq a)
  : Lemma (requires contains t pat)
          (ensures (let k = last_index_of t pat in
                      k >= 0
                      /\ concat (concat (take t k) pat) (drop t (k + len pat)) == t
                      /\ len (take t k) == k))
  = lemma_last_occ_some_iff_contains t pat;
    lemma_last_occ_bound t pat;
    lemma_last_occ_is_prefix t pat;
    lemma_is_prefix_at_decompose t pat (Some?.v (last_occ t pat))

(* ================================================================= *)
(* replace_axiom, seq_axioms.cpp:628-658                                *)
(*                                                                      *)
(* The non-trivial clause (pat, u both nonempty, contains u pat)        *)
(* asserts u = x.pat.y and r = x.t.y for the same Skolem x,y used by    *)
(* indexof_axiom (`m_sk.mk_indexof_left/right`, i.e. the *first*        *)
(* occurrence). The lemma below shows this matches `replace`'s actual   *)
(* (leftmost-match) recursive definition exactly.                       *)
(* ================================================================= *)

(* `replace u pat rep` performs exactly the same leftmost-match scan as
   `first_occ`: whenever `pat` occurs in `u`, the replacement happens
   at the first-occurrence position. *)
let rec lemma_replace_at_first_occ (#a:eqtype) (u pat rep:seq a)
  : Lemma (requires Some? (first_occ u pat))
          (ensures (let k = Some?.v (first_occ u pat) in
                      replace u pat rep == concat (concat (take u k) rep) (drop u (k + len pat))))
          (decreases u)
  = if is_prefix pat u then ()
    else
      match u with
      | _ :: u' -> lemma_replace_at_first_occ u' pat rep

(* contains(u,pat) /\ pat <> empty ==>
     exists x y. u = x ++ pat ++ y /\ replace(u,pat,rep) = x ++ rep ++ y
   with x,y := (take u k)/(drop u (k+len pat)), k = indexof(u,pat,0).
   This is the soundness statement for replace_axiom's
   contains-and-both-nonempty clauses. *)
let lemma_replace_axiom_decompose (#a:eqtype) (u pat rep:seq a)
  : Lemma (requires contains u pat /\ len pat > 0)
          (ensures (let k = index_of u pat 0 in
                      k >= 0
                      /\ concat (concat (take u k) pat) (drop u (k + len pat)) == u
                      /\ replace u pat rep == concat (concat (take u k) rep) (drop u (k + len pat))))
  = lemma_indexof_decompose u pat;
    lemma_first_occ_some_iff_contains u pat;
    lemma_replace_at_first_occ u pat rep

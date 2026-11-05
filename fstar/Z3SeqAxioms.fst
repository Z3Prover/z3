(*
   Z3SeqAxioms.fst

   Soundness proofs for the quantifier-instantiation axioms generated
   by src/ast/seq/seq_axioms.cpp (the `seq::axioms` class). Unlike
   seq_rewriter.cpp (formalized in Z3SeqRewrites.fst / Z3RegexRewrites.fst
   as *rewrite-preserves-equivalence* theorems), seq_axioms.cpp does not
   rewrite terms: it emits ground/quantifier-free *clauses* (asserted as
   lemmas to the underlying SAT/SMT core) that pin down the behavior of
   "complex" sequence operations (str.extract, str.at, str.indexof,
   str.prefixof, ...) in terms of "basic" ones (str.++, str.len,
   str.nth, equality) together with fresh Skolem witnesses.

   Soundness of such an axiom means: the clause is a valid consequence
   of the intended semantics -- i.e. restating the clause at the
   `seq a` level of Z3SeqTheory.fst (using the concrete functions
   `len`/`nth`/`at`/`take`/`drop`/`extract`/.. in place of the
   uninterpreted terms, and real existentials in place of Skolem
   constants) always holds. This file proves exactly that, function by
   function, reusing Z3SeqRewrites.fst's existing lemmas wherever
   possible.

   Scope: this is a first installment covering the "positional access"
   core (str.at / str.nth_i / str.extract / the str.extract-derived
   tail/drop_last special cases), the str.unit injectivity axiom, the
   str.len dispatch for str.extract, and the str.prefixof/str.suffixof
   "tightest counterexample" axioms. See SEQ_REWRITER_REPORT.md for the
   full per-function coverage table and the list of axioms not yet
   covered (str.indexof/last_indexof, str.replace[_all]/replace_re[_all],
   str.to_int/int.to_str, digit/code axioms, ubv2s/ubv2ch, str.^ power,
   unroll_not_contains, length_limit).
*)
module Z3SeqAxioms

open Z3SeqTheory
open Z3SeqRewrites
module Classical = FStar.Classical

(* ================================================================= *)
(* take/drop: length and reconstruction                                *)
(* ================================================================= *)

(* len (take s n) = min(n, len s). *)
let rec lemma_len_take (#a:eqtype) (s:seq a) (n:nat)
  : Lemma (ensures len (take s n) == (if n < len s then n else len s))
  = match s with
    | [] -> ()
    | _ :: s' -> if n = 0 then () else lemma_len_take s' (n - 1)

(* len (drop s n) = max(0, len s - n). *)
let rec lemma_len_drop (#a:eqtype) (s:seq a) (n:nat)
  : Lemma (ensures len (drop s n) == (if n < len s then len s - n else 0))
  = match s with
    | [] -> ()
    | _ :: s' -> if n = 0 then () else lemma_len_drop s' (n - 1)

(* drop s (len s) = empty : dropping everything leaves nothing. *)
let rec lemma_drop_all (#a:eqtype) (s:seq a)
  : Lemma (ensures drop s (len s) == empty)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_drop_all s'

(* take s n ++ drop s n = s : take/drop is a total decomposition of s
   at any cut point n (clamped at the ends, like `take`/`drop`
   themselves). *)
let rec lemma_take_drop_reconstruct (#a:eqtype) (s:seq a) (n:nat)
  : Lemma (ensures concat (take s n) (drop s n) == s)
  = match s with
    | [] -> ()
    | x :: s' -> if n = 0 then () else lemma_take_drop_reconstruct s' (n - 1)

(* ================================================================= *)
(* str.at / str.nth_i                                                  *)
(*                                                                      *)
(* seq_axioms.cpp:606-644 (at_axiom) and 654-677 (nth_axiom). The
   general (non-literal) branch of at_axiom introduces Skolem
   witnesses x = pre(s,i), y = tail(s,i) with the clauses
     0 <= i < |s| ==> s = x.e.y  /\  i = |x|
     i < 0 \/ i >= |s| ==> e = ""
     0 <= i < |s| ==> |e| = 1
   which is exactly the decomposition below with x := take s i,
   y := drop s (i+1), e := at s i. nth_axiom's defining equation
   "unit(nth_i(s,i)) = at(s,i)" for 0<=i<|s| is `lemma_at_in_range`
   (Z3SeqRewrites.fst), restated here as the nth_axiom corollary. *)
(* ================================================================= *)

(* s = (take s i) ++ (at s i) ++ (drop s (i+1)), and |take s i| = i,
   for 0 <= i < |s|. This is the soundness statement for at_axiom's
   in-range clauses (with x := take s i, y := drop s (i+1), e := at s i). *)
let lemma_at_decompose (#a:eqtype) (s:seq a) (i:int)
  : Lemma (requires 0 <= i /\ i < len s)
          (ensures concat (concat (take s i) (at s i)) (drop s (i + 1)) == s
                   /\ len (take s i) == i
                   /\ len (at s i) == 1)
  = lemma_at_in_range s i;
    lemma_len_take s i;
    lemma_take_drop_reconstruct s i;
    // drop s i = (at s i) ++ (drop s (i+1)), since at s i = unit (nth s i)
    // and i < len s, so `drop` peels exactly one element.
    let rec peel (s:seq a) (i:nat{i < len s})
      : Lemma (ensures drop s i == concat (at s i) (drop s (i + 1)))
      = match s with
        | x :: s' -> if i = 0 then () else peel s' (i - 1)
    in
    peel s i;
    lemma_concat_assoc (take s i) (at s i) (drop s (i + 1))

(* at_axiom, out-of-range clauses: already exactly `lemma_at_oob`
   (Z3SeqRewrites.fst): i < 0 \/ i >= len s ==> at s i == empty. *)

(* nth_axiom's defining equation, restated for direct citation:
   0 <= i < len s ==> unit (nth s i) == at s i. *)
let lemma_nth_axiom_sound (#a:eqtype) (s:seq a) (i:int)
  : Lemma (requires 0 <= i /\ i < len s)
          (ensures unit (nth s i) == at s i)
  = lemma_at_in_range s i

(* ================================================================= *)
(* str.unit injectivity (unit_axiom, seq_axioms.cpp:1214-1218)         *)
(*                                                                      *)
(* unit_axiom asserts `u = unit_inv(unit(u))`, i.e. introduces a left   *)
(* inverse for `str.unit`. This is sound exactly because `unit` is     *)
(* injective at the `seq a` level.                                     *)
(* ================================================================= *)

let lemma_unit_injective (#a:eqtype) (x y:a)
  : Lemma (requires unit x == unit y) (ensures x == y)
  = ()

(* ================================================================= *)
(* str.len dispatch on str.extract (length_axiom, extract branch,      *)
(* seq_axioms.cpp:1368-1407)                                           *)
(* ================================================================= *)

let lemma_length_axiom_extract (#a:eqtype) (s:seq a) (offs l:int)
  : Lemma (ensures
      (offs >= 0 /\ l >= 0 /\ len s >= offs + l ==> len (extract s offs l) == l)
      /\ ((offs < 0 \/ l <= 0 \/ len s < offs) ==> len (extract s offs l) == 0)
      /\ (offs >= 0 /\ len s >= offs /\ len s < offs + l ==> len (extract s offs l) == len s - offs))
  = if offs < 0 || l <= 0 then lemma_extract_neg_or_nonpos_len s offs l;
    if len s < offs then lemma_extract_pos_ge_len s offs l;
    if offs >= 0 && l > 0 && len s >= offs then lemma_len_extract_nat s offs l

(* ================================================================= *)
(* str.extract, general case (extract_axiom, seq_axioms.cpp:196-261)   *)
(*                                                                      *)
(* With x := take s i, y := drop s (i+l), e := extract s i l, the       *)
(* seven clauses of extract_axiom's general branch reduce to the        *)
(* following facts about `extract`/`take`/`drop`.                       *)
(* ================================================================= *)

let lemma_extract_axiom_general (#a:eqtype) (s:seq a) (i l:int)
  : Lemma (ensures
      // 0 <= i /\ l >= 0 ==> x.e.y = s
      (0 <= i /\ l >= 0
        ==> concat (concat (take s i) (extract s i l)) (drop s (i + l)) == s)
      // 0 <= i /\ i <= len s ==> |x| = i
      /\ (0 <= i /\ i <= len s ==> len (take s i) == i)
      // 0 <= i /\ i <= len s /\ l >= 0 /\ len s >= l + i ==> |e| = l
      /\ (0 <= i /\ i <= len s /\ l >= 0 /\ len s >= l + i ==> len (extract s i l) == l)
      // 0 <= i /\ i <= len s /\ l >= 0 /\ len s < l + i ==> |e| = len s - i
      /\ (0 <= i /\ i <= len s /\ l >= 0 /\ len s < l + i ==> len (extract s i l) == len s - i)
      // i < 0 \/ len s <= i \/ len s <= 0 \/ l <= 0 ==> |e| = 0
      /\ ((i < 0 \/ len s <= i \/ len s <= 0 \/ l <= 0) ==> len (extract s i l) == 0))
  = if i >= 0 && l > 0 then begin
      // x.e.y = s : extract s i l = take(drop s i) l, and
      // take s i ++ (take(drop s i) l ++ drop(drop s i) l) == take s i ++ drop s i == s.
      assert (extract s i l == extract_nat s i l);
      lemma_extract_nat_eq_take_drop s i l;
      lemma_drop_drop s i l;
      lemma_take_drop_reconstruct (drop s i) l;
      lemma_take_drop_reconstruct s i;
      lemma_concat_assoc (take s i) (extract s i l) (drop s (i + l))
    end
    else if i >= 0 && l = 0 then begin
      lemma_extract_neg_or_nonpos_len s i l;
      lemma_take_drop_reconstruct s i;
      lemma_concat_empty_r (take s i)
    end;
    if i >= 0 && i <= len s then lemma_len_take s i;
    lemma_length_axiom_extract s i l;
    (if i < 0 || l <= 0 then lemma_extract_neg_or_nonpos_len s i l);
    (if len s <= i then lemma_extract_pos_ge_len s i l)

(* ================================================================= *)
(* str.prefixof / str.suffixof "tightest counterexample"                *)
(* (prefix_axiom / suffix_axiom, seq_axioms.cpp:1286-1356, and          *)
(*  tightest_prefix, seq_axioms.cpp:372-390)                            *)
(*                                                                      *)
(* prefix_axiom's non-trivial branch (len s <= len t) asserts the       *)
(* existence of a common prefix x and a first mismatching pair of       *)
(* characters c <> d such that s = x.c.y and t = x.d.z. This is exactly *)
(* "first point of difference" for sequences that are not in the        *)
(* prefix relation; proved below by explicit construction (a            *)
(* recursive `mismatch` function) together with its correctness lemma.  *)
(* ================================================================= *)

let rec mismatch (#a:eqtype) (p s:seq a)
  : Tot (option (seq a & seq a & seq a & a & a)) (decreases p)
  = match p, s with
    | [], _ -> None
    | _, [] -> None
    | hp :: p', hs :: s' ->
      if hp <> hs then Some (empty, p', s', hp, hs)
      else
        match mismatch p' s' with
        | None -> None
        | Some (x, y, z, c, d) -> Some (concat (unit hp) x, y, z, c, d)

let rec lemma_mismatch_correct (#a:eqtype) (p s:seq a)
  : Lemma (requires len p <= len s /\ ~(is_prefix p s))
          (ensures Some? (mismatch p s)
                   /\ (let (x, y, z, c, d) = Some?.v (mismatch p s) in
                       ~(c == d)
                       /\ p == concat x (concat (unit c) y)
                       /\ s == concat x (concat (unit d) z)))
          (decreases p)
  = match p, s with
    | hp :: p', hs :: s' ->
      if hp <> hs then ()
      else lemma_mismatch_correct p' s'

(* prefix_axiom's existential clause, restated as a theorem: whenever
   len p <= len s and p is not a prefix of s, there exist x,y,z,c,d
   (instantiated to `mismatch p s`) such that p = x.c.y, s = x.d.z,
   c <> d. *)
let lemma_prefix_mismatch (#a:eqtype) (p s:seq a)
  : Lemma (requires len p <= len s /\ ~(is_prefix p s))
          (ensures exists (x y z:seq a) (c d:a).
                     ~(c == d) /\ p == concat x (concat (unit c) y)
                     /\ s == concat x (concat (unit d) z))
  = lemma_mismatch_correct p s;
    let (x, y, z, c, d) = Some?.v (mismatch p s) in
    Classical.exists_intro
      (fun x -> exists (y z:seq a) (c d:a).
                  ~(c == d) /\ p == concat x (concat (unit c) y)
                  /\ s == concat x (concat (unit d) z))
      x

(* len (reverse s) == len s. *)
let rec lemma_len_reverse (#a:eqtype) (s:seq a)
  : Lemma (ensures len (reverse s) == len s)
  = match s with
    | [] -> ()
    | x :: s' -> lemma_len_reverse s'; lemma_len_concat (reverse s') (unit x)

(* suffix_axiom is prefix_axiom applied to the reverses of s and t: by
   definition `is_suffix p s == is_prefix (reverse p) (reverse s)`, so
   running `mismatch` on the reversed sequences and reversing the
   witnesses back (via `lemma_reverse_concat`/`lemma_reverse_reverse`)
   yields the suffix-side counterexample directly; no Skolem/existential
   machinery beyond `mismatch` itself is needed. *)
let lemma_suffix_mismatch (#a:eqtype) (p s:seq a)
  : Lemma (requires len p <= len s /\ ~(is_suffix p s))
          (ensures exists (x y z:seq a) (c d:a).
                     ~(c == d) /\ p == concat y (concat (unit c) x)
                     /\ s == concat z (concat (unit d) x))
  = lemma_len_reverse p;
    lemma_len_reverse s;
    lemma_mismatch_correct (reverse p) (reverse s);
    let (x, y, z, c, d) = Some?.v (mismatch (reverse p) (reverse s)) in
    // reverse p == concat x (concat (unit c) y)  /\  reverse s == concat x (concat (unit d) z)
    lemma_reverse_concat x (concat (unit c) y);
    lemma_reverse_concat (unit c) y;
    lemma_reverse_unit c;
    lemma_concat_assoc (reverse y) (unit c) (reverse x);
    lemma_reverse_reverse p;
    // p == reverse (reverse p) == concat (reverse y) (concat (unit c) (reverse x))
    lemma_reverse_concat x (concat (unit d) z);
    lemma_reverse_concat (unit d) z;
    lemma_reverse_unit d;
    lemma_concat_assoc (reverse z) (unit d) (reverse x);
    lemma_reverse_reverse s;
    // s == reverse (reverse s) == concat (reverse z) (concat (unit d) (reverse x))
    Classical.exists_intro
      (fun (xx:seq a) -> exists (yy zz:seq a) (cc dd:a).
                  ~(cc == dd) /\ p == concat yy (concat (unit cc) xx)
                  /\ s == concat zz (concat (unit dd) xx))
      (reverse x);
    Classical.exists_intro
      (fun (yy:seq a) -> exists (zz:seq a) (cc dd:a).
                  ~(cc == dd) /\ p == concat yy (concat (unit cc) (reverse x))
                  /\ s == concat zz (concat (unit dd) (reverse x)))
      (reverse y);
    Classical.exists_intro
      (fun (zz:seq a) -> exists (cc dd:a).
                  ~(cc == dd) /\ p == concat (reverse y) (concat (unit cc) (reverse x))
                  /\ s == concat zz (concat (unit dd) (reverse x)))
      (reverse z);
    Classical.exists_intro
      (fun (cc:a) -> exists (dd:a).
                  ~(cc == dd) /\ p == concat (reverse y) (concat (unit cc) (reverse x))
                  /\ s == concat (reverse z) (concat (unit dd) (reverse x)))
      c;
    Classical.exists_intro
      (fun (dd:a) ->
                  ~(c == dd) /\ p == concat (reverse y) (concat (unit c) (reverse x))
                  /\ s == concat (reverse z) (concat (unit dd) (reverse x)))
      d

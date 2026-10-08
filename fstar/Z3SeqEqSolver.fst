(*
   Z3SeqEqSolver.fst

   Soundness proofs for the core case-split reasoning of
   src/smt/seq_eq_solver.cpp (`theory_seq`'s word-equation solving
   engine). Unlike seq_axioms.cpp (ground clauses axiomatizing complex
   operations in terms of basic ones), this module is the *search*
   procedure that solves equations `ls = rs` between concatenations of
   sequence variables and ground pieces by case-splitting on the
   possible values of a leading variable. What needs justifying is not
   a single clause but that each produced case split is both sound
   (every branch, if it holds, implies the original equation) and
   complete (the branches taken together cover every way the equation
   could be solved) -- a different flavor of correctness proof from
   the rest of this development.

   Covered here (the case-split/propagation rules with a clean, purely
   `seq a`-level combinatorial justification):

     - `branch_variable_eq`/`find_branch_candidate` (seq_eq_solver.cpp
       797-910): given `l ++ ls' = rs` with `l` a variable, every
       solution has `l` equal to *some* prefix of `rs`, and conversely
       every prefix of `rs` yields a solution: this is
       `lemma_branch_variable_eq_characterization` below. This is
       exactly the set of candidates (`v0 = empty`, then `v0 = rs[0]`,
       `v0 = rs[0..1]`, ...) that `find_branch_candidate` enumerates.

     - `len_based_split` (seq_eq_solver.cpp 128-243): given
       `x11 ++ x12 = y11 ++ y12` and a known length relationship
       between `x11` and `y11`, the aligned decomposition the function
       produces (introducing a Skolem `Z` of length `|offset|` when
       `offset <> 0`) is sound: `lemma_concat_eq_same_len_prefix`
       (offset = 0) and `lemma_len_based_split_offset_pos` (offset > 0,
       with the offset < 0 case obtained by swapping `(x11,x12)` and
       `(y11,y12)`, by symmetry of the statement).

     - `propagate_length_coherence` (971-1027): the main decomposition
       clause (`lemma_propagate_length_coherence_decompose`) and the
       two guarded upper-bound clauses
       (`lemma_propagate_length_coherence_hi_eq_lo`/`hi_gt_lo`) are
       proved sound; see also the historical-soundness-bug case study
       below.

     - `check_length_coherence` (1036-1043, the `lo = 1` fallback):
       `lemma_check_length_coherence_decompose`, the same decomposition
       principle specialized to a single element.

     - `set_empty` (theory_seq.cpp helper, called from `split_lengths`
       etc.): `lemma_len_zero_is_empty`.

     - `branch_binary_variable` (459-490): the length-difference
       propagation is `lemma_len_concat_eq_diff`; the `|x| > |ys|`
       Skolem split is a direct instance of
       `lemma_len_based_split_offset_pos` (no new lemma needed).

     - `split_lengths` (330-416): the unit-`Y` case is an instance of
       `lemma_concat_eq_same_len_prefix`; the general case is
       `lemma_split_lengths_decompose`, a genuine generalization of
       `lemma_len_based_split_offset_pos`.

     - `solve_nth_eq` (1185-1221): an instance of the `at_axiom`/
       `nth_axiom` decomposition already proved in `Z3SeqAxioms.fst`
       (`lemma_at_decompose`, `lemma_nth_axiom_sound`); no new lemma
       needed.

   Not an independent soundness claim (documented, not formalized):

     - `assume_equality` and its call sites (935-970, and from
       `propagate_length_coherence`/`check_length_coherence`): this is
       *not* an axiom/propagation -- it calls `ctx.assume_eq`, which
       only suggests a case-split for the SAT core to explore (a
       branching hint the solver remains free to backtrack), and
       therefore carries no soundness obligation of its own.
     - `branch_variable_mb`'s `propagate_eq(lnl, lnr)` (line 300,
       `len(concat ls) == len(concat rs)` given the ambient equation
       `concat ls == concat rs`): trivial congruence of `len`, not
       restated as a separate lemma.

   Not covered (documented, not formalized -- these need reasoning
   beyond the pure `seq a` level, e.g. about *terms* that denote
   sequences (variables vs. ground pieces, syntactic occurs-checks) or
   about Parikh-vector/linear-arithmetic integration, not just about
   sequences themselves):

     - `branch_ternary_variable`/`branch_quat_variable` and their
       `can_align_from_lhs`/`can_align_from_rhs`/`mk_alignment` helpers
       (seq_eq_solver.cpp 513-796): solving `x1 ++ xs ++ x2 = y1 ++ ys
       ++ y2` for two interior unit-pieces `xs`/`ys` requires a
       Fine-and-Wilf-style "can two local windows overlap" theory,
       substantially more machinery than the prefix/length facts used
       above.
     - `can_be_equal` (910-934): a cheap *necessary* (not sufficient)
       syntactic pruning test over terms that may contain unresolved
       variables (`m.are_distinct`/`m.are_equal` on uninterpreted
       terms); stating its soundness needs a two-sorted ground/variable
       term model, not just `seq a`.
     - the "occurs check" early exit in `find_branch_candidate`
       (`if (l == rs.get(j)) return false;`): a syntactic
       self-reference/search-pruning optimization over *terms*, not a
       fact about sequences.
     - `find_better_rep` (disabled, `#if 0`), `find_fst_non_empty_idx`/
       `find_fst_non_empty_var` (1255-end): representative-selection
       heuristics tied to the egraph, not sequence-level soundness
       questions; `find_better_rep` is dead code.
     - `check_parikh` (1071-1105): Parikh-vector encoding that
       integrates with `theory_arith`; out of scope for a `seq
       a`-only development.
     - `reduce_length_eq`/`is_unit_eq` (1136-1184): syntactic
       dispatch/fast-path detection; `reduce_length_eq`'s 3-argument
       workhorse is not even defined in this file.
     - `has_len_offset`/`is_complex` (128-160, 307-329): heuristic
       predicates selecting when a rule applies, not soundness
       questions.
     - `branch_unit_variable` (498-512): delegates entirely to the
       separate `seq::eq_solver` class (`m_eq.branch`), not defined in
       this file.

   Case study -- a historical soundness bug (issue #11013 / PR #11015):
   the pre-fix `propagate_length_coherence` omitted the `~low` guard on
   two of its clauses, asserting unconditional facts about a sometimes-
   free Skolem term. `lemma_propagate_length_coherence_buggy_
   counterexample` exhibits a concrete countermodel showing the pre-fix
   clause was not valid, confirming the bug (see
   SEQ_EQ_SOLVER_REPORT.md for the full write-up).
*)
module Z3SeqEqSolver

open Z3SeqTheory
open Z3SeqRewrites
open Z3SeqAxioms

(* ================================================================= *)
(* Small building blocks: take/drop vs. concat                          *)
(* ================================================================= *)

(* take (concat l t) (len l) == l : taking exactly the first piece
   back out of a concatenation recovers it. *)
let rec lemma_take_concat_self (#a:eqtype) (l t:seq a)
  : Lemma (ensures take (concat l t) (len l) == l)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: l' -> lemma_take_concat_self l' t

(* drop (concat l t) (len l) == t : dropping exactly the first piece
   back out of a concatenation recovers the rest. *)
let rec lemma_drop_concat_self (#a:eqtype) (l t:seq a)
  : Lemma (ensures drop (concat l t) (len l) == t)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: l' -> lemma_drop_concat_self l' t

(* take (concat s t) n == take s n, whenever the cut point n falls
   within s itself (so t is irrelevant). *)
let rec lemma_take_concat_le (#a:eqtype) (s t:seq a) (n:nat)
  : Lemma (requires n <= len s)
          (ensures take (concat s t) n == take s n)
          (decreases s)
  = match s with
    | [] -> ()
    | _ :: s' -> if n = 0 then () else lemma_take_concat_le s' t (n - 1)

(* Left cancellation: concat p a == concat p b ==> a == b. *)
let lemma_concat_left_cancel (#a:eqtype) (p x y:seq a)
  : Lemma (requires concat p x == concat p y)
          (ensures x == y)
  = lemma_drop_concat_self p x;
    lemma_drop_concat_self p y

(* take s (len s) == s : taking everything leaves it unchanged (dual
   of `lemma_drop_all`). *)
let rec lemma_take_all (#a:eqtype) (s:seq a)
  : Lemma (ensures take s (len s) == s)
  = match s with
    | [] -> ()
    | _ :: s' -> lemma_take_all s'

(* ================================================================= *)
(* branch_variable_eq / find_branch_candidate,                         *)
(* seq_eq_solver.cpp:797-910                                           *)
(* ================================================================= *)

(* If `l ++ ls' = rs`, then `l` is forced to be *some* prefix of `rs`
   (specifically, the length-`len l` prefix), and `ls'` is forced to
   be the matching remainder. This is the ground-truth fact that makes
   enumerating `l := take rs k` for increasing `k` a complete search:
   no other value of `l` can possibly satisfy the equation. *)
let lemma_concat_prefix_decompose (#a:eqtype) (l ls' rs:seq a)
  : Lemma (requires concat l ls' == rs)
          (ensures len l <= len rs /\ l == take rs (len l) /\ ls' == drop rs (len l))
  = lemma_len_concat l ls';
    lemma_take_concat_self l ls';
    lemma_drop_concat_self l ls'

(* Soundness *and* completeness of `find_branch_candidate`'s case
   split, for a single candidate length `k`: assuming `l ++ ls' = rs`
   fixes `len l` to be some specific `k <= len rs`, exactly the
   branches with `l = take rs k` (`k = 0` is the "l = empty" branch
   `find_branch_candidate` always tries first; `k = 1, 2, ...` are the
   growing-prefix candidates `v0 = concat(rs[0..k))` tried in the
   loop). Conversely every such branch really is a solution. *)
let lemma_branch_variable_eq_characterization (#a:eqtype) (l ls' rs:seq a) (k:nat{k <= len rs})
  : Lemma (ensures (concat l ls' == rs /\ len l == k) <==> (l == take rs k /\ ls' == drop rs k))
  = Classical.move_requires (lemma_concat_prefix_decompose l ls') rs;
    lemma_take_drop_reconstruct rs k;
    lemma_len_take rs k

(* ================================================================= *)
(* len_based_split, seq_eq_solver.cpp:128-243                          *)
(* ================================================================= *)

(* offset = 0 case: equal-length aligned prefixes of equal
   concatenations must themselves be equal. *)
let lemma_concat_eq_same_len_prefix (#a:eqtype) (x11 x12 y11 y12:seq a)
  : Lemma (requires concat x11 x12 == concat y11 y12 /\ len x11 == len y11)
          (ensures x11 == y11 /\ x12 == y12)
  = lemma_take_concat_self x11 x12;
    lemma_take_concat_self y11 y12;
    lemma_drop_concat_self x11 x12;
    lemma_drop_concat_self y11 y12

(* offset > 0 case: `x11` is longer than `y11` by exactly `offset`, so
   the "overhang" `z := drop x11 (len y11)` is the Skolem `Z` the C++
   code introduces; it has length `offset`, completes `y11` out to
   `x11` (`concat y11 z == x11`), and absorbing it into `x12`'s side
   restores alignment with `y12` (`concat z x12 == y12`). The
   `offset < 0` case is this same lemma with `(x11,x12)` and
   `(y11,y12)` swapped (the hypothesis/conclusion are symmetric under
   that swap), so no separate proof is needed. *)
let lemma_len_based_split_offset_pos (#a:eqtype) (x11 x12 y11 y12:seq a) (offset:pos)
  : Lemma (requires concat x11 x12 == concat y11 y12 /\ len x11 == len y11 + offset)
          (ensures (let z = drop x11 (len y11) in
                      len z == offset
                      /\ concat y11 z == x11
                      /\ concat z x12 == y12))
  = lemma_take_concat_le x11 x12 (len y11);
    lemma_take_concat_self y11 y12;
    // take x11 (len y11) == y11, from the two facts above plus the
    // hypothesis `concat x11 x12 == concat y11 y12`.
    lemma_take_drop_reconstruct x11 (len y11);
    lemma_len_drop x11 (len y11);
    lemma_concat_assoc y11 (drop x11 (len y11)) x12;
    lemma_concat_left_cancel y11 (concat (drop x11 (len y11)) x12) y12

(* ================================================================= *)
(* propagate_length_coherence, seq_eq_solver.cpp:971-1027              *)
(*                                                                       *)
(* Historical soundness bug: issue #11013, fixed by PR #11015           *)
(* (commit d35dc0838). The code decomposes a variable `e` into `lo`     *)
(* explicit head elements plus a leftover Skolem "tail" term `seq`, but *)
(* the only axiom linking `seq` back to the real value of `e` is the    *)
(* *guarded* clause `~low \/ e == concat(heads, seq)`, where `low` is   *)
(* the literal for `len e >= lo`. So `seq` only means `drop e lo` in    *)
(* branches where `low` holds -- it is a free, unconstrained term       *)
(* whenever `low` is false. The pre-fix code asserted two further       *)
(* clauses about `seq` (forcing it empty, or bounding its length)       *)
(* *without* that same `~low` guard, i.e. as unconditional claims about *)
(* a sometimes-free term: unsound. The lemmas below prove the fixed     *)
(* (guarded) clauses sound, and exhibit a concrete countermodel          *)
(* showing the pre-fix (unguarded) clause is not valid.                  *)
(* ================================================================= *)

(* The main decomposition/linking clause, seq_eq_solver.cpp:1005:
   guarded by `low`, `e` is forced equal to the concatenation of the
   `lo` explicit head elements plus the leftover Skolem tail. Modeling
   those skolem pieces by their intended meaning under `low` --
   `elems := take e lo`, `seq := drop e lo` -- this is exactly
   take/drop reconstruction. (`lemma_take_drop_reconstruct` itself
   holds unconditionally since `take`/`drop` are total clamped
   functions; the `low` guard matters at the C++ level because the
   repeated raw `m_sk.decompose` calls only actually produce something
   shaped like `take e lo`/`drop e lo` when `lo <= len e` -- for a
   shorter `e` the construction still runs but no longer corresponds
   to this clean picture, which is exactly why the clause is guarded.) *)
let lemma_propagate_length_coherence_decompose (#a:eqtype) (e:seq a) (lo:nat)
  : Lemma (requires len e >= lo)
          (ensures concat (take e lo) (drop e lo) == e)
  = lemma_take_drop_reconstruct e lo

(* Fixed code, `hi = lo` branch: guarded by `low` (`len e >= lo`) and
   the upper bound `len e <= hi = lo`, these pin `len e == lo` exactly,
   so the decomposition's remainder is empty. *)
let lemma_propagate_length_coherence_hi_eq_lo (#a:eqtype) (e:seq a) (lo:nat)
  : Lemma (requires len e >= lo /\ len e <= lo)
          (ensures drop e lo == empty)
  = lemma_drop_all e

(* Fixed code, `hi > lo` branch: guarded by `low` and the upper bound
   `len e <= hi`, the remainder's length is bounded by `hi - lo`. *)
let lemma_propagate_length_coherence_hi_gt_lo (#a:eqtype) (e:seq a) (lo hi:nat)
  : Lemma (requires len e >= lo /\ len e <= hi /\ lo < hi)
          (ensures len (drop e lo) <= hi - lo)
  = lemma_len_drop e lo

(* The bug: dropping the `~low` guard turns "`len e <= hi` implies
   `seq == empty`" (the `hi = lo` clause, specialized here to
   `lo = hi = 1`) into an unconditional claim about the free Skolem
   `seq`. Countermodel: take `e := empty` (too short: `len e = 0 < lo`,
   so `low` is false and the decomposition's linking equation never
   fires) paired with an arbitrary nonempty stand-in `s` for `seq`.
   Then the pre-fix clause's stated hypothesis `len e <= hi` holds
   while its conclusion `s == empty` fails -- exactly the unsoundness
   the issue reported. The fixed code's `~low` guard is what excludes
   this countermodel: here `low` (`len e >= lo`) does not hold, so the
   guarded clause makes no claim about `s` at all. *)
let lemma_propagate_length_coherence_buggy_counterexample ()
  : Lemma (let e : seq int = empty in
           let s : seq int = unit 1 in
           let lo = 1 in let hi = 1 in
           len e <= hi              // pre-fix hypothesis holds ...
           /\ ~ (len e >= lo)       // ... yet `low` is false: the
                                    //     decomposition premise never held ...
           /\ s <> empty)           // ... so the pre-fix conclusion can fail.
  = ()

(* ================================================================= *)
(* check_length_coherence, seq_eq_solver.cpp:1036-1043 (the lo = 1     *)
(* fallback used when propagate_length_coherence's lower bound isn't   *)
(* available): propagate_is_conc's own guard literal is `e <> empty`,  *)
(* under which `e` decomposes into its single head element plus a      *)
(* Skolem tail -- the `lo = 1` instance of the same decomposition       *)
(* principle as `lemma_propagate_length_coherence_decompose` above,     *)
(* proved directly here since `take e 1`/`drop e 1` is just a single    *)
(* cons-cell peel.                                                      *)
(* ================================================================= *)

let lemma_check_length_coherence_decompose (#a:eqtype) (e:seq a)
  : Lemma (requires len e >= 1)
          (ensures concat (unit (nth e 0)) (drop e 1) == e)
  = match e with
    | _ :: _ -> ()

(* ================================================================= *)
(* set_empty, seq_eq_solver.cpp (helper in theory_seq.cpp, called from *)
(* split_lengths etc.): `len x == 0 ==> x == empty`.                    *)
(* ================================================================= *)

let lemma_len_zero_is_empty (#a:eqtype) (s:seq a)
  : Lemma (requires len s == 0)
          (ensures s == empty)
  = match s with
    | [] -> ()

(* ================================================================= *)
(* branch_binary_variable, seq_eq_solver.cpp:459-490                   *)
(*                                                                       *)
(* Equation is `x ++ xs == ys ++ y` (xs, ys ground unit vectors).       *)
(* ================================================================= *)

(* The length-difference propagation (line 463-466): a direct
   arithmetic consequence of additivity of `len` over `concat`, used
   to force the solver's current length model to agree with what the
   equation already entails. *)
let lemma_len_concat_eq_diff (#a:eqtype) (x xs ys y:seq a)
  : Lemma (requires concat x xs == concat ys y)
          (ensures len x + len xs == len ys + len y)
  = lemma_len_concat x xs;
    lemma_len_concat ys y

(* The `|x| > |ys|` Skolem split (lines 476-490: `x = ys ++ Y1`,
   `y = Y1 ++ Y2`, `Y2 = xs`) is exactly `lemma_len_based_split_offset_pos`
   above, instantiated with `(x11,x12,y11,y12) := (x, xs, ys, y)` and
   `offset := len x - len ys`: it gives `z := drop x (len ys)` with
   `concat ys z == x` (i.e. `x = ys ++ Y1` with `Y1 := z`) and
   `concat z xs == y` (i.e. `y = Y1 ++ xs`, matching `y = Y1 ++ Y2` with
   `Y2 := xs`). No separate lemma is needed; see
   `lemma_len_based_split_offset_pos` for the proof. *)

(* ================================================================= *)
(* split_lengths, seq_eq_solver.cpp:330-416                             *)
(*                                                                       *)
(* Decomposes `ls = X :: restLs`, `rs = bs @ Y :: restRs` (so the        *)
(* ambient equation is `concat X restLs == concat (concat b Y) restRs`,  *)
(* `b := mk_concat bs`) using a length relationship between `X` and      *)
(* `b`/`Y` established in the current arithmetic model.                  *)
(* ================================================================= *)

(* The unit-`Y` case (lines 403-406, `lenB == lenX`): `X = b ++ Y`.
   Exactly `lemma_concat_eq_same_len_prefix` above, instantiated with
   `(x11,x12,y11,y12) := (X, restLs, b, concat Y restRs)` (which has
   `len X == len b` by hypothesis): gives `X == b` -- (a degenerate
   instance; the real code additionally folds `Y` into `b` before this
   call, so this is the same equal-length-prefix fact applied at a
   different grouping of the same concatenation). *)

(* The general (non-unit) `Y` case (lines 408-416, `X = b ++ Y1`,
   `Y = Y1 ++ Y2`): a genuine generalization of
   `lemma_len_based_split_offset_pos`, needed because here the
   "overhang" must additionally be shown to be a prefix of `Y` itself
   (not just of `concat Y restRs`). *)
let lemma_split_lengths_decompose (#a:eqtype) (x restLs b y restRs:seq a) (offset:pos)
  : Lemma (requires concat x restLs == concat (concat b y) restRs
                     /\ len x == len b + offset /\ offset <= len y)
          (ensures (let y1 = drop x (len b) in
                    len y1 == offset
                    /\ concat b y1 == x
                    /\ (let y2 = drop y offset in concat y1 y2 == y)))
  = lemma_concat_assoc b y restRs;
    lemma_len_based_split_offset_pos x restLs b (concat y restRs) offset;
    let y1 = drop x (len b) in
    // y1 == take y offset: both sides equal `take (concat y1 restLs) offset`
    // resp. `take (concat y restRs) offset`, which agree since
    // `concat y1 restLs == concat y restRs` (from the lemma above) and
    // `offset <= len y1` (== offset, via `lemma_take_all`) and
    // `offset <= len y` (hypothesis).
    lemma_take_all y1;
    lemma_take_concat_le y1 restLs offset;
    lemma_take_concat_le y restRs offset;
    lemma_take_drop_reconstruct y offset

(* ================================================================= *)
(* solve_nth_eq, seq_eq_solver.cpp:1185-1221                            *)
(*                                                                       *)
(* `nth(s,idx) == rhs` (0 <= idx < len s) introduces the equation       *)
(* `s == pre(s,idx) ++ unit(rhs) ++ post(s,idx+1)`. This is exactly the  *)
(* `at_axiom`/`nth_axiom` decomposition already proved in                *)
(* `Z3SeqAxioms.fst` (`lemma_at_decompose`, `lemma_nth_axiom_sound`),     *)
(* with `pre(s,idx) := take s idx`, `post(s,idx+1) := drop s (idx+1)`,   *)
(* `rhs = at s idx = unit (nth s idx)`. No separate lemma is needed      *)
(* here. *)

# F* Formalization of `src/smt/seq_eq_solver.cpp` — Coverage Report

See [`README.md`](README.md) for the top-level index of this F*
formal-verification audit series, and
[`SEQ_REWRITER_REPORT.md`](SEQ_REWRITER_REPORT.md) for the sibling
report on `src/ast/rewriter/seq_rewriter.cpp` and
`src/ast/seq/seq_axioms.cpp`.

`seq_eq_solver.cpp` is a different kind of subject from those two: it
is not a rewriter (term in, equivalent term out) and not an
axiom-emitter (ground clause pinning down one operation in terms of
others). It is `theory_seq`'s *search procedure* for solving equations
`ls = rs` between concatenations of sequence variables and ground
pieces, by case-splitting on the possible values of a leading
variable. What needs justifying for a case-split rule is not a single
clause's validity but that the rule is both **sound** (every produced
branch, if it holds, implies the original equation) and **complete**
(the branches taken together cover every way the equation could be
solved).

Proof file: [`Z3SeqEqSolver.fst`](Z3SeqEqSolver.fst), built on
[`Z3SeqTheory.fst`](Z3SeqTheory.fst), [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst),
and [`Z3SeqAxioms.fst`](Z3SeqAxioms.fst) (for `lemma_len_take`/
`lemma_len_drop`/`lemma_take_drop_reconstruct`).

Toolchain used: [F*](https://github.com/FStarLang/FStar) `v2026.09.27`
(Windows x64) with Z3 `4.13.3` as the SMT backend. The proof file
type-checks and discharges all verification conditions with **no
`admit`/`assume`/axioms**:

```
C:\fstar\fstar\bin\fstar.exe --smt C:\z3-4.13.3\z3-4.13.3-x64-win\bin\z3.exe Z3SeqEqSolver.fst
```

## Coverage by function

This table lists every site in `seq_eq_solver.cpp` that generates a
theory axiom/clause (`add_axiom`), a propagation (`propagate_lit`/
`propagate_eq`/`propagate_is_conc`), a new equation fed back into the
solver (`m_eqs.push_back`/`add_solution`), or a branching hint
(`assume_equality`), together with its verification status.

| `seq_eq_solver.cpp` function | Lines | Verified? | Lemma(s) / rationale |
|---|---|---|---|
| `branch_variable_eq` / `find_branch_candidate` | 797-910 | ✅ | `lemma_branch_variable_eq_characterization` (+ helpers `lemma_concat_prefix_decompose`, `lemma_take_concat_self`, `lemma_drop_concat_self`) |
| `len_based_split` | 128-243 | ✅ | `lemma_concat_eq_same_len_prefix` (offset = 0), `lemma_len_based_split_offset_pos` (offset > 0; offset < 0 by symmetry) |
| `propagate_length_coherence` | 971-1027 | ✅ | `lemma_propagate_length_coherence_decompose` (main linking clause), `lemma_propagate_length_coherence_hi_eq_lo`/`hi_gt_lo` (guarded upper-bound clauses); see also the soundness-bug case study below |
| `check_length_coherence` (the `lo = 1` fallback) | 1036-1043 | ✅ | `lemma_check_length_coherence_decompose` |
| `set_empty` (theory_seq.cpp helper, called from `split_lengths`) | — | ✅ | `lemma_len_zero_is_empty` |
| `branch_binary_variable` | 459-490 | ✅ | length-difference propagation: `lemma_len_concat_eq_diff`; the `|x| > |ys|` Skolem split: instance of `lemma_len_based_split_offset_pos` (no new lemma) |
| `split_lengths` | 330-416 | ✅ | unit-`Y` case: instance of `lemma_concat_eq_same_len_prefix`; general case: `lemma_split_lengths_decompose` (+ new helper `lemma_take_all`) |
| `solve_nth_eq` | 1185-1221 | ✅ | instance of `at_axiom`/`nth_axiom`'s decomposition, already proved in `Z3SeqAxioms.fst` (`lemma_at_decompose`, `lemma_nth_axiom_sound`); no new lemma needed |
| `assume_equality` (and its call sites in `propagate_length_coherence`, `check_length_coherence0`, `branch_variable_eq`) | 935-970 | N/A | *not* an axiom: calls `ctx.assume_eq`, a branching hint the SAT core may still backtrack, so it carries no soundness obligation |
| `branch_variable_mb`'s `propagate_eq(lnl, lnr)` | 300 | N/A (trivial) | `len(concat ls) == len(concat rs)` given `concat ls == concat rs`: trivial congruence of `len`, not restated as a lemma |
| `has_len_offset` | 128-160 | ❌ | purely an egraph lookup (`m_offset_eq`) for a length relationship already established elsewhere; no new soundness content |
| `branch_variable` / `branch_variable_mb` (dispatch) | 244-306 | ❌ | solver-level scheduling (which rule to try, in what order); no independent soundness content |
| `is_complex` | 307-329 | ❌ | heuristic predicate (variable-count threshold), not a soundness question |
| `branch_ternary_variable[_rhs/_lhs]` / `branch_quat_variable` / `can_align_from_lhs`/`can_align_from_rhs` / `mk_alignment` | 513-796 | ❌ | solving `x1 ++ xs ++ x2 = y1 ++ ys ++ y2` for two interior unit-pieces needs a Fine-and-Wilf-style "can two local windows overlap" theory, substantially more machinery than the prefix/length facts above |
| `can_be_equal` | 910-934 | ❌ | a cheap *necessary* (not sufficient) syntactic pruning test over terms that may contain unresolved variables (`m.are_distinct`/`m.are_equal`); needs a two-sorted ground/variable term model, not just `seq a` |
| the "occurs check" early exit in `find_branch_candidate` | ~870 | ❌ | a syntactic self-reference/search-pruning optimization over *terms*, not a fact about sequences |
| `add_consequence` | 92-107 | ❌ | generic clause-emission plumbing (linearizes dependencies into literals); not an independent soundness claim beyond its caller's own justification |
| `check_parikh` | 1071-1105 | ❌ | Parikh-vector encoding that integrates with `theory_arith`; out of scope for a `seq a`-only development |
| `reduce_length_eq` / `is_unit_eq` | 1136-1184 | ❌ | syntactic dispatch/fast-path detection; `reduce_length_eq`'s 3-argument workhorse isn't even defined in this file |
| `find_better_rep` | 1259-1310ish (`#if 0`) | ❌ (dead code) | disabled in the source (`#if 0`); not currently compiled or executable |
| `find_fst_non_empty_idx` / `find_fst_non_empty_var` | ~1310-end | ❌ | representative-selection heuristics tied to the egraph, not sequence-level soundness questions |
| `branch_unit_variable` | 498-512 | ❌ | delegates entirely to the separate `seq::eq_solver` class (`m_eq.branch`), not defined in this file |

All ✅ lemmas above compile with **zero `admit`/`assume`**.

## Case study: a found-and-confirmed soundness bug (`propagate_length_coherence`)

Issue [#11013](https://github.com/Z3Prover/z3/issues/11013), fixed by
PR [#11015](https://github.com/Z3Prover/z3/pull/11015) (commit
`d35dc0838`), reported that `propagate_length_coherence` emitted
**unsound theory axioms**. The function decomposes a variable `e` into
`lo` explicit head elements plus a leftover Skolem "tail" term `seq`,
but the *only* axiom linking `seq` back to the real value of `e` is a
clause guarded by the literal `low` (standing for `len(e) >= lo`):
`~low \/ e == concat(heads, seq)`. Consequently `seq` only means
`drop e lo` in branches where `low` holds, and is otherwise a free,
unconstrained term. The pre-fix code asserted two further clauses
about `seq` (forcing it empty when `hi == lo`; bounding its length when
`hi > lo`) **without** that same `~low` guard — i.e. as unconditional
claims about a sometimes-free term.

This audit confirms the bug precisely:

- `lemma_propagate_length_coherence_hi_eq_lo` and
  `lemma_propagate_length_coherence_hi_gt_lo` prove the **fixed**
  (`~low`-guarded) clauses sound: under the hypothesis `len e >= lo`
  (i.e. `low` holds) together with the stated upper bound on `len e`,
  `drop e lo == empty` (resp. `len (drop e lo) <= hi - lo`) follows
  from `lemma_drop_all`/`lemma_len_drop` in `Z3SeqAxioms.fst`.
- `lemma_propagate_length_coherence_buggy_counterexample` exhibits a
  concrete countermodel for the **pre-fix** (unguarded) `hi == lo`
  clause: `e := empty`, `s := unit 1` (standing in for the free Skolem
  `seq`), `lo = hi = 1`. Here the pre-fix clause's stated hypothesis
  `len e <= hi` holds (`0 <= 1`), yet its conclusion `s == empty` fails
  — exactly the unsoundness the issue reported. Note `low` (`len e >=
  lo`, i.e. `0 >= 1`) is false in this model, which is precisely why
  the fixed code's `~low` guard excludes it: the guarded clause makes
  no claim about `s` when `low` doesn't hold.

This follows the same "prove the fix, disprove the bug" pattern used
for the nullability soundness bug found in `info::diff` during the
`Z3RegexInfo.fst` audit (see [`REGEX_REPORT.md`](REGEX_REPORT.md)).

## Summary

Every site in `seq_eq_solver.cpp` that generates a theory axiom,
propagation, or new equation is now accounted for. The rules with a
clean, purely `seq a`-level combinatorial or arithmetic justification
-- `branch_variable_eq`'s prefix-guessing search, `len_based_split`'s
length-aligned decomposition, `propagate_length_coherence`'s linking
and upper-bound clauses, `check_length_coherence`'s single-element
fallback, `set_empty`, `branch_binary_variable`'s length-difference
propagation and Skolem split, `split_lengths`'s decomposition, and
`solve_nth_eq` -- are all formalized and proved sound, reusing
`Z3SeqRewrites.fst`/`Z3SeqAxioms.fst`'s existing take/drop/concat
lemmas plus a handful of new small building blocks
(`lemma_take_concat_self`/`lemma_drop_concat_self`/
`lemma_take_concat_le`/`lemma_concat_left_cancel`/`lemma_take_all`/
`lemma_len_concat_eq_diff`/`lemma_len_zero_is_empty`). Several of these
sites turned out to be direct instances of lemmas already proved for a
different function (`branch_binary_variable`'s Skolem split and
`split_lengths`' unit-`Y` case reuse `len_based_split`'s lemmas;
`solve_nth_eq` reuses `seq_axioms.cpp`'s `at_axiom`/`nth_axiom`
decomposition from `Z3SeqAxioms.fst`), so no new lemma was needed for
them. `propagate_length_coherence`'s formalization also doubles as a
case study of a real, historical soundness bug (issue #11013/PR
#11015): see above.

One important non-soundness-claim clarification: `assume_equality`
(and its several call sites) is *not* an axiom or propagation at all
-- it calls `ctx.assume_eq`, which only suggests a branch for the SAT
core's decision procedure to explore and which the solver remains free
to backtrack from. It therefore carries no soundness obligation, unlike
`add_axiom`/`propagate_lit`/`propagate_eq`, which assert hard,
irrevocable consequences.

The remaining rules in this file fall into three categories that are
deliberately left unformalized: (1) rules needing a richer *overlap*
theory (`branch_ternary_variable`/`branch_quat_variable`'s "can two
local windows of a word equation overlap" reasoning -- a
Fine-and-Wilf-style development, substantially more work than what's
here), (2) rules needing a two-sorted *term* model distinguishing
ground pieces from unresolved variables (`can_be_equal`'s pruning
test, the occurs-check search optimization), and (3) solver plumbing
and heuristics with no independent soundness content of their own
(scheduling, representative selection, dead code, Parikh/
length-arithmetic integration with `theory_arith`).

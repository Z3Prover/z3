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

| `seq_eq_solver.cpp` function | Lines | Lemma(s) in `Z3SeqEqSolver.fst` | Not covered |
|---|---|---|---|
| `branch_variable_eq` / `find_branch_candidate` | 797-910 | `lemma_branch_variable_eq_characterization` (+ helpers `lemma_concat_prefix_decompose`, `lemma_take_concat_self`, `lemma_drop_concat_self`) | the "occurs check" early exit (`if (l == rs.get(j)) return false;`) is a syntactic self-reference/search-pruning optimization over *terms*, not a fact about sequences |
| `len_based_split` | 128-243 | `lemma_concat_eq_same_len_prefix` (offset = 0 case), `lemma_len_based_split_offset_pos` (offset > 0 case; offset < 0 is the same lemma with `(x11,x12)`/`(y11,y12)` swapped, by symmetry) | — |
| `has_len_offset` | 128-160 | not covered | purely an egraph lookup (`m_offset_eq`) for a length relationship already established elsewhere; no new soundness content beyond what `len_based_split` already covers |
| `branch_variable` / `branch_variable_mb` | 244-306 | not covered | solver-level dispatch/heuristic scheduling (which rule to try, in what order); no independent soundness content |
| `is_complex` | 307-329 | not covered | a heuristic predicate (variable-count threshold) selecting when a rule applies, not a soundness question |
| `split_lengths` | 330-421 | not covered | a length-arithmetic case split (`Xa = bYc` decomposition driven by model length values) layered on top of the same prefix facts as `len_based_split`; not yet restated as its own lemma |
| `branch_ternary_variable[_rhs/_lhs]` / `branch_quat_variable` / `can_align_from_lhs`/`can_align_from_rhs` / `mk_alignment` | 513-796 | not covered | solving `x1 ++ xs ++ x2 = y1 ++ ys ++ y2` for two interior unit-pieces needs a Fine-and-Wilf-style "can two local windows overlap" theory, substantially more machinery than the prefix/length facts above |
| `can_be_equal` | 910-934 | not covered | a cheap *necessary* (not sufficient) syntactic pruning test over terms that may contain unresolved variables (`m.are_distinct`/`m.are_equal`); needs a two-sorted ground/variable term model, not just `seq a` |
| `assume_equality` / `add_consequence` | 92-107, 935-970 | not covered | solver plumbing (literal/clause bookkeeping), not an independent soundness claim |
| `propagate_length_coherence` | 971-1027 | `lemma_propagate_length_coherence_hi_eq_lo`, `lemma_propagate_length_coherence_hi_gt_lo` (+ `lemma_propagate_length_coherence_buggy_counterexample`, a historical-soundness-bug case study — see below) | the Parikh-vector bookkeeping (`elems`/`xs` accounting) feeding the guard literal `low` itself is not restated, only the two downstream upper-bound clauses it guards |
| `check_length_coherence[0]` / `check_parikh` | 1028-1135 | not covered | Parikh-vector and length-arithmetic reasoning integrating with `theory_arith`; out of scope for a `seq a`-only development |
| `reduce_length_eq` / `is_unit_eq` | 1136-1184 | not covered | syntactic dispatch/fast-path detection, not a soundness question |
| `solve_nth_eq` | 1185-1254 | not covered | nth-decomposition heuristic tied to the egraph |
| `find_better_rep` / `find_fst_non_empty_idx` / `find_fst_non_empty_var` | 1255-end | not covered | representative-selection heuristics, not sequence-level soundness questions |
| `branch_unit_variable` | 498-512 | not covered | delegates entirely to the separate `seq::eq_solver` class (`m_eq.branch`), not defined in this file |

All lemmas above compile with **zero `admit`/`assume`**.

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

The two case-split rules with the cleanest purely-`seq a`-level
combinatorial justification -- `branch_variable_eq`'s prefix-guessing
search and `len_based_split`'s length-aligned decomposition -- are now
formalized and proved sound and complete against the `seq a` ground
truth, reusing `Z3SeqRewrites.fst`/`Z3SeqAxioms.fst`'s existing
take/drop/concat lemmas plus two new small building blocks
(`lemma_take_concat_self`/`lemma_drop_concat_self`/
`lemma_take_concat_le`/`lemma_concat_left_cancel`). `propagate_length_
coherence`'s two guarded upper-bound clauses are also formalized and
proved sound, with a companion lemma confirming (via a concrete
countermodel) that the pre-fix, unguarded version of one of those
clauses -- a real soundness bug, issue #11013/PR #11015 -- was indeed
not valid. The remaining rules
in this file fall into three categories that are deliberately left
unformalized: (1) rules needing a richer *overlap* theory
(`branch_ternary_variable`/`branch_quat_variable`'s "can two local
windows of a word equation overlap" reasoning -- a Fine-and-Wilf-style
development, substantially more work than what's here), (2) rules
needing a two-sorted *term* model distinguishing ground pieces from
unresolved variables (`can_be_equal`'s pruning test, the occurs-check
search optimization), and (3) solver plumbing and heuristics with no
independent soundness content of their own (scheduling, representative
selection, Parikh/length-arithmetic integration with `theory_arith`).

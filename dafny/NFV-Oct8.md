# NFV Refutation Triage — Week of Oct 1–8, 2026

This report triages every NFV (neuro-formal-verification) formal-audit refutation that
**survived adjudication** over the past week: 22 audited PRs/manual-audit targets, 28
distinct findings. None of these had a recorded human review at the time of writing
(`nfv-refutation-reviews.json` lists them all `unreviewed`). The goal here is to separate
plausible genuine Z3 issues from artifacts of the Dafny translation model, and to explain
each claim in terms of the actual C++ source rather than the Dafny proof jargon.

Background: the NFV pipeline translates a C++ function and a natural-language property
into a Dafny model, then tries to prove or refute the property against that model. A
"refutation that survives adjudication" means Dafny found a concrete witness falsifying
the property *in the translated model*. Whether that witness corresponds to a reachable
Z3 execution, and whether the translation faithfully reflects the C++ semantics, is a
separate question that requires human judgment — this triage attempts exactly that
judgment, grounded in the real source.

## 🟢 Likely genuine bugs worth an engineer's look (2)

### z3#11098 — `seq_rewriter::mk_seq_index` / `zstring::indexofu`
**Claim:** `sequence_index_rewrites_preserve_indexof` — the rewrite's resulting integer
should exactly match the SMT-LIB `seq.index` value.

**Source (`src/util/zstring.cpp`):**
```cpp
int zstring::indexofu(zstring const& other, unsigned offset) const { ... }
```
and in `src/ast/rewriter/seq_rewriter.cpp`:
```cpp
int idx = s1.indexofu(s2, r.get_unsigned());
result = m_autil.mk_int(idx);
```
`indexofu` returns a signed C++ `int`, but SMT-LIB's `seq.index` is defined over
arbitrary-precision integers. For a concrete string whose length exceeds `INT_MAX`, the
correct index can't be represented in an `int` and the rewrite silently returns a
truncated/wrong value. This is a genuine type-width mismatch between the C++
implementation and the SMT-LIB semantics — though only reachable with an
astronomically long concrete string (length > 2^31), so practical impact is limited.

### z3#11080 — `seq_rewriter::mk_seq_extract`
**Claim:** `overlong_suffix_prefix_flattening` — flattening a prefix that removes `d`
elements from an overlong suffix must use the suffix's *available* length, not its
*requested* length.

The witness is small and concrete: `|X|=1`, `p=0`, `requested=2`, `d=1`. Taking
`extract(X, p, requested)` when `requested` exceeds the remaining string length yields a
suffix of only the available length (`X` itself, length 1). The prefix-flattening branch
in `mk_seq_extract` appears to reuse the caller-supplied `requested` value when computing
the flattened result length, rather than re-deriving it from the suffix's true length,
over-retaining one extra element. Small, concrete, and plausible — worth a direct code
read of the prefix/suffix-flattening branch in `mk_seq_extract`.

## 🔴 Likely NFV translation-model artifacts, not real Z3 bugs

Three of these were independently verified against current Z3 `master` source by hand;
the rest are flagged because the pipeline's own prose already admits the witness doesn't
actually challenge the stated property.

### z3#11050 — `is_dyadic_artifact` (verified false positive)
**Claim:** the helper requires denominator `2^k` with `k` *strictly greater than* 24.

**Source (`src/math/lp/nra_solver.cpp`):**
```cpp
unsigned const dyadic_artifact_threshold = 24;
...
return k >= threshold && den.is_one();
```
The real comparison is `k >= 24`, which matches the stated specification ("exponent **at
least** 24") — not the "strictly greater than 24" that the discussion claims the code
requires. The Dafny translation mis-modeled the loop's boundary condition; the actual
code is correct.

### z3#11031 — `goal::elim_true` (verified false positive)
**Claim:** for `F=[a, true, b]`, the destination slot for `b` keeps `true`'s stale
dependency because `i == j` suppresses the copy, producing dependencies `[0,1]` instead
of the required `[0,2]`.

**Source (`src/tactic/goal.cpp`):**
```cpp
void goal::elim_true() {
    unsigned i = 0, j = 0;
    for (const auto& [f, dep, pr] : *this) {
        if (m().is_true(f)) { ++i; continue; }
        if (i != j) { m().set(m_forms, j, f); ... m().set(m_dependencies, j, dep); }
        ++i; ++j;
    }
    shrink(j);
}
```
Tracing by hand: processing `a` leaves `i=1,j=1`; processing `true` advances `i=2,j=1`
(skip); processing `b` now has `i=2 != j=1`, so the copy **does** happen, writing `b`'s
own dependency (`D[2]=2`) into slot `j=1`. Final dependencies are `[D[0], D[2]] = [0,2]`
— exactly as the specification requires. The claimed `i==j` suppression never occurs for
this witness; the Dafny model miscoupled the loop counters during translation.

### z3#11091 — `reversed_concrete_range_is_empty_but_interpreted`
The pipeline's own text states: "this witness does not satisfy the proposition's own
stated `OP_RE_RANGE` assumption, so the result refutes only an unrestricted translated
postcondition, not the stated reversed-concrete-range case." Self-flagged non-issue.

### z3#11087 — `propagate_core` (`preserves_pre_refactor_behavior`)
Self-flagged: "evidence of underconstraint in the translated comparison model, not a
demonstrated behavioral difference between the C++ branches." The reference
("old") implementation is left unconstrained in the model, so any value can "differ"
from it trivially.

### z3#11038 — `refine_atan2` (both findings)
Both witnesses supply "frozen" input values (`yv`, `xv`, `vv`) per the property's own
assumption, but the translated function then **recomputes** those values independently
from internal state (`m_atan2_apps` / `s.values`) instead of using the supplied frozen
values — an artifact of how the translation captures mutable solver state, not a
behavioral bug in `refine_atan2` itself.

### z3#11099 — `new_match_uses_fixed_null_id`
The witness manufactures a `family_name` containing a literal embedded newline and tag
(`"\n[new-match]"`) purely to trick a line-counting heuristic in the property (counting
occurrences of the substring `[new-match]`) into reporting two matches. Not a reachable
trace-format regression.

### z3#11082 — both findings
- `equal_size_cores_use_lexicographic_ast_ids`: witness uses two **empty** cores, so
  "lexicographically smaller" is vacuously false for both orderings — the property's own
  tie-break definition is degenerate for this witness, not evidence of a wrong
  comparator.
- `spacer_obligations_receive_creation_order_ids`: the witness's precondition `pre.next_pob_id_value == 0`
  conflicts with the implementation's ID numbering, which starts at 1 — a spec-side
  off-by-one in the precondition, not an implementation defect.

### z3#11051 — `multiple_accessor_kinds_remain_supported`
Witness triggers an early `registryDefined == false` guard that's unrelated to the
accessor-pattern assumptions actually being tested — the property's precondition doesn't
constrain registry state, so the witness short-circuits before reaching the logic under
test.

### z3#11049 — `reduce_and_solve_only_after_actual_split`
Witness simply asserts the two sides of the predicate are inconsistent without deriving
that from any genuine control-flow path — looks like an underconstrained model rather
than a demonstrated call-count defect.

### z3#11079 — both findings
- `relevancy_setting_independence`: witness just sets `result[0].return_value = false`
  and `result[2].return_value = true` directly, with no derivation connecting them to the
  relevancy-setting difference — underconstrained translated state.
- `normalization_bridge_is_equivalence`: the witness takes the early
  `!can_propagate_core()` return branch, which never reaches (and therefore never tests)
  the equivalence logic the property is about.

## 🟡 Needs human reachability/judgment (plausible but inconclusive)

- **z3#11105** — `primal_dual_lns_follows_round_processing`, `core_rotation_lns_regression_cost_one`:
  plausible LNS/core-rotation ordering races, but both witnesses are minimal/degenerate
  edge cases (single check event; two-variable weighted MaxSAT instance) that don't
  clearly establish a reachable scheduling bug.
- **z3#11099** — `theory_event_ids_match`: in the existing `[inst-discovered]` case the
  first token differs (`theory-solving` vs `0x0`) from the `[instance]` line's token.
  Could be an intentional distinction between trace tags rather than a bug — needs a
  trace-format maintainer's opinion.
- **z3#11086** — `fpa2bv_converter::mk_to_fp_real`: the property and the implementation
  appear to disagree about which of two rounding-mode parameters (`rm` vs `bv_rm`) should
  govern rounding; could be a specification artifact (mismatched parameter naming in the
  translated property) rather than a real rounding bug.
- **z3#11062** — `theory_ff::propagate_roots`: a fairly concrete claim that product
  branching discards a zero numeral factor and emits an unsound root-split axiom
  (`¬(0*x=0) ∨ (x=0)`, refuted by `x=3`). Specific enough to warrant a direct look at the
  product-branching logic in `propagate_roots`.
- **z3#11052** — `theory_nseq::mk_value`: claims a token that is both a sequence and a
  regular-expression sort takes an early regex short-circuit branch and returns a
  length-0 value instead of the required length-1 value. Concrete and specific — worth
  checking whether that dual-sort case is actually reachable.
- **z3#11023** — `update` (lifted upper bound): the pipeline's own text notes "the
  claimed value and ordering hold" but a separate `ValidUpper` postcondition fails for a
  refuted-but-unvalidated hint — a subtle edge case around what counts as a "valid" bound
  after a refutation, worth a second look.
- **z3#11020** — `conflict_is_valid_explanation`, `check_returns_only_sound_answers`:
  witnesses use degenerate zero-length input sequences; the underlying question (does
  `prepare`/`check` correctly propagate stale `l_false` state) is plausible but not
  conclusively demonstrated by these particular witnesses.
- **z3#11007** — `unknown_fallback_registers_ff`: claims the no-argument fallback path
  of `setup::setup_unknown` can append a duplicate `"setup_ff"` entry to the
  configuration trace. If true this looks cosmetic (duplicate trace entry, not a
  functional defect, assuming `setup_ff` registration is idempotent) but wasn't fully
  confirmed against the fallback's call sequence.

## ⚠️ Pipeline reporting gap (not Z3 bug claims)

Two "findings" are not real bug claims at all — a defect in the NFV **reporting**
pipeline lost the original property name and claim text during report generation:

- **z3#11059** (discussion https://github.com/Z3Prover/bench/discussions/6223)
- **manual audit of `src/model/numeral_factory.cpp`** (discussion https://github.com/Z3Prover/bench/discussions/5549)

Both show `### \`None\` — ?` with `asserted: ""` and an internal detail block literally
reading `original claim: (not recorded)`. These should be excluded from bug-triage counts
and instead tracked as an NFV pipeline bug (property metadata not surviving to the
rendered discussion).

## Summary table

| Category | Count | Examples |
|---|---|---|
| Likely genuine bug | 2 | #11098 `indexofu` int width, #11080 `mk_seq_extract` length |
| Confirmed/strongly suspected translation artifact | 13 | #11050, #11031 (both hand-verified false), #11087, #11091, #11038 (x2), #11099 (new_match), #11082 (x2), #11051, #11049, #11079 (x2) |
| Needs human reachability/judgment | 9 | #11105 (x2), #11099 (theory_event_ids_match), #11086, #11062, #11052, #11023, #11020 (x2), #11007 |
| Pipeline reporting gap | 2 | z3#11059, `numeral_factory.cpp` manual audit |

**Bottom line:** of 28 surviving findings this week, only 2 look like plausible,
concretely-grounded Z3 defects; roughly half are demonstrably or very likely artifacts of
the Dafny translation model (vacuous witnesses, mis-modeled loop bounds, frozen-value
recomputation, or label-text heuristics); the remainder require a human to judge
reachability, consistent with the pipeline's own standing caveat that a refutation is
evidence against the *translated model*, not proof of a reachable Z3 defect.

---
*Generated from NFV Formal Audit discussions in Z3Prover/bench covering Oct 1–8, 2026.
Source line references verified against Z3Prover/z3 `master` as of this report's date.*

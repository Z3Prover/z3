# Audit: Open Floating-Point Issues/PRs vs. the `to_fp`-from-Real Rounding Encoding

This report is a focused follow-up to [`FPA_REPORT.md`](FPA_REPORT.md),
triggered by a review of currently **open** GitHub issues/PRs labeled
`Floats` on `Z3Prover/z3`. It extracts a precise correctness condition
for `fpa2bv_converter::mk_to_fp_real`'s symbolic (non-numeral) Real ->
FloatingPoint rounding encoding, and mechanically verifies (in F*,
see `Z3FpaRoundingAudit.fst`) that the **existing** (currently merged,
on `master`) encoding fails that condition, while the **new** encoding
proposed by two independent open PRs restores it.

**Status update (latest session, `master` at commit `57e1b5f93`):**
All five tracked issues are now **closed**. PR #10888 **merged**,
closing #10881/#9953/#10931. PR #11086 **merged**, closing #7431
(zero-sign fix). PR #11088 **merged**, closing #7842 (NaN cross-theory
congruence, `theory_fpa.cpp::relevant_eh`, see `Z3FpaNanWrap.fst`) and
#10176 (sign-of-`fp.to_real` nonlinear-arithmetic incompleteness,
`fpa2bv_converter.cpp::mk_to_real`, see `Z3FpaToRealSign.fst`) —
#10176 did not auto-close via the merge and was closed manually with
an explanatory comment. PR #10938 remains **closed, unmerged**
(superseded by #10888). Permanent regression tests for #7842/#10176
were added to `src/test/fpa.cpp` as part of #11088. No open
Floats-labeled issues remain from this audit as of this update.

## Issues (label `Floats`)

| # | Title | Status |
|---|---|---|
| [#10931](https://github.com/Z3Prover/z3/issues/10931) | Unsound unsat: `to_fp` from a symbolic Real loses the rounding carry into the next binade | **closed** (fixed by #10888, re-verified and closed this session) |
| [#10881](https://github.com/Z3Prover/z3/issues/10881) | False `unsat` for inexact symbolic Real-to-binary64 rounding | **closed** (fixed by merged PR #10888) |
| [#10176](https://github.com/Z3Prover/z3/issues/10176) | [Solution Soundness Bug] Incorrect SAT in Float32 FP/Real round-trip arithmetic | **closed** (fixed by #11088, merged; closed manually with explanatory comment) |
| [#9953](https://github.com/Z3Prover/z3/issues/9953) | [Refutational Soundness Bug] Incorrect UNSAT in Float32 FP/Real round-trip arithmetic | **closed** (fixed by #10888, verified and closed this session) |
| [#8052](https://github.com/Z3Prover/z3/issues/8052) | Unsat only with unnecessary asserts, else unknown | open (out of scope, not a soundness bug) |
| [#7842](https://github.com/Z3Prover/z3/issues/7842) | Incorrect model | **closed** (fixed by #11088, merged; auto-closed) |
| [#7431](https://github.com/Z3Prover/z3/issues/7431) | Invalid model issue on float formula | **closed** (fixed by #11086, merged; auto-closed) |

**#10931 and #10881 are the same root cause**: both trace to the single
exact round-trip equality `m.mk_eq(m_util.mk_to_real(result), x)` in
`fpa2bv_converter::mk_to_fp_real`'s symbolic branch (`fpa2bv_converter.cpp`,
~line 2949). #10881 exhibits it as a tie-break failure strictly inside a
binade; #10931 exhibits it at a power-of-two binade boundary (where the
rounding "carries" into the next exponent). #9953/#10176 are earlier
reports of what looks like the same class of Float32 round-trip
soundness bug (titles describe round-trip arithmetic unsoundness in
both directions); they were not independently re-triaged against the
current code as part of this audit. #8052/#7842/#7431 appear unrelated
to the rounding-encoding bug targeted here (no overlap with
`mk_to_fp_real`'s symbolic branch in their reports) and were not
further investigated.

## Open PRs (label `Floats`)

| # | Title | Fixes | CI |
|---|---|---|---|
| [#10888](https://github.com/Z3Prover/z3/pull/10888) | Fix false `unsat` for inexact symbolic Real-to-FloatingPoint rounding | #10881 | all green |
| [#10938](https://github.com/Z3Prover/z3/pull/10938) | Fix unsound `to_fp` rounding: symbolic Real→FP conversion lost carry into next binade | #10931 | CLA only (full CI not yet observed complete) |

**Both PRs touch the same line and the same function** (`mk_to_fp_real`'s
symbolic branch) but take **different, independent approaches**:

- **#10888** removes the exact-equality constraint and replaces it with
  an explicit midpoint/tie-break condition stated directly in terms of
  the *final* rounded result's bit-fields (`ulp`, `gap_up`/`gap_down`,
  `lower_mid`/`upper_mid`, `tie_lo`/`tie_hi`, `sig_is_even`), for all
  five rounding modes, plus directed-mode saturation at the largest
  finite value.
- **#10938** removes the same constraint but instead links the
  *pre-round*, extended-precision `(sgn, sig, exp)` triple to `x` via a
  guard/round/sticky ("GRS") bracketing (`sig_hi`/`sticky` bracket `|x|`
  against a grid point), plus a normalization side-condition, then lets
  the existing (unmodified) `round()` routine do the actual
  nearest/tie/renormalize/overflow logic.

Since both are open simultaneously and edit overlapping lines, **only
one can land as written** — merging both would conflict. Based on the
analysis below, #10888's encoding is self-contained and independently
checkable; #10938's correctness additionally depends on `round()`'s
(unaudited, bit-precise) renormalization behavior.

**Recommendation (confirmed after re-triage, see "Re-triage" section
below): merge #10888.** It is self-contained, its correctness condition
is fully mechanized end-to-end (`Z3FpaRoundingAudit.fst` +
`Z3FpaRoundingBits.fst`), and a direct inspection of its diff (`gh pr
diff 10888`) found no occurrence of `au.mk_power` and no division by a
term that can be zero or symbolically negative — every `au.mk_div` it
introduces divides by `sig_value` (a significand-with-hidden-bit real
expression, always in `[2^(sbits-1), 2^sbits - 1]`, i.e. provably
bounded away from zero) or by the literal constant `2`. This rules out
#10888 as a source of the kind of real-division/model-completion risk
suspected (see below) in issue #10176. #10938, by contrast, still
depends on the separate, unaudited `fpa2bv_converter.cpp` bit-vector
`round()` circuit (a different code path from `mpf.cpp`'s `round()`,
which *was* proved correct in `Z3MpfRound.fst`/`Z3MpfExact.fst` — that
proof does **not** transfer to this circuit).

## Correctness condition

The symbolic rounding encoding's job is: given rounding mode `rm`, input
real `x`, and a candidate result `r` (with real value `r.real` and
known gaps `gap_lo`/`gap_hi` to its predecessor/successor), decide
whether `r` is correctly `rm`-rounded from `x`. For round-to-nearest
modes this is the textbook definition:

```
round_nearest_even(r, gap_lo, gap_hi, is_even, x) :=
    let lower_mid = r - gap_lo/2 in
    let upper_mid = r + gap_hi/2 in
    lower_mid <= x <= upper_mid
    /\ (x = lower_mid \/ x = upper_mid  ==>  is_even)
```

(`is_even` = "r's significand is even", i.e. RNE's tie-break rule.)
This is a verbatim transcription of PR #10888's `nte_cond`.

The **old** (currently merged) encoding instead asserts:

```
exact_roundtrip(r, x) := (x = r.real)
```

## Mechanized result (`Z3FpaRoundingAudit.fst`)

Working in a small, self-contained exact-rational theory (`rat`, with
comparisons by cross-multiplication — no floating-point or real-number
axioms needed), the following are proved, with **no `admit`/`assume`**:

1. **`lemma_old_implies_new`** — `exact_roundtrip(r,x)` implies
   `round_nearest_even(r, gap_lo, gap_hi, is_even, x)` for any positive
   gaps. The old constraint's models are always valid rounding models
   (it was never *incorrect*, only *incomplete*).

2. **`lemma_new_not_implies_old`** — the converse fails: a concrete
   model (`r=0`, symmetric gap `2`, `x=1`, a tie broken by `is_even`)
   satisfies `round_nearest_even` but not `exact_roundtrip`. This is
   the mechanized witness that the old encoding is a **strict**,
   unsound restriction: there exist models of the true rounding
   relation that the old code's constraint rules out.

3. **`lemma_binade_carry_witness`** — the same strictness result,
   instantiated with the *literal* numbers from issue #10931
   (`(_ FloatingPoint 8 24)`, `r = 2.0`, `gap_lo = 2^-23`,
   `gap_hi = 2^-22`, `x = 2 - 2^-24`), confirming mechanically that the
   issue's claimed `sat` witness (`r ≈ 1.99999998` rounds to `2.0` under
   RNE) satisfies the correct rounding relation and is exactly the kind
   of model the old `exact_roundtrip` equality excludes (since
   `x ≠ r.real`), explaining the observed false `unsat`.

4. **`lemma_grs_satisfiable`** — PR #10938's alternative GRS bracketing
   (`grs_brackets`) is, in isolation, satisfiable for every `x` in a
   half-open grid interval (by choosing `sticky = (x ≠ grid_lo)`), the
   same completeness property as point 2 above, applied one layer
   earlier in the pipeline (to the pre-round significand/exponent
   rather than the final result).

**Conclusion: the existing (merged) encoding fails this correctness
condition — it is provably strictly incomplete (sound but not
complete) with respect to `round_nearest_even`. PR #10888's encoding
*is* `round_nearest_even`, transcribed directly, so it succeeds this
condition by construction, with the two theorems above as the formal
soundness/completeness argument.** PR #10938's `grs_brackets` layer
also succeeds this condition, but its overall correctness additionally
requires `round()`'s existing bit-precise renormalization to correctly
turn a GRS-bracketed intermediate value into the final nearest/tie/
overflow-adjusted result for every bit-vector instantiation — a
bit-precise circuit-correctness question this audit does not verify
(consistent with `unpack`/`round` being out of scope for the base FPA
audit; see [`FPA_REPORT.md`](FPA_REPORT.md)).

## Deeper layer: are the gap *formulas* themselves correct? (`Z3FpaRoundingBits.fst`)

`Z3FpaRoundingAudit.fst` treated `gap_lo`/`gap_hi` as *abstract* positive
rationals — it verified the logical schema (`exact_roundtrip` is
strictly weaker than `round_nearest_even`) but not PR #10888's actual
**formulas** for those gaps (`ulp = |r|/sig_value`, "the gap below a
power of two is half the gap above it", and the smallest-normal
exception). `Z3FpaRoundingBits.fst` closes that gap: it defines a
value semantics `val_of(cs, e, s) = s · 2^e / 2^cs` for a representable
magnitude at "format position" `(e, s)` (with `e = 1` uniformly
covering subnormals, zero, and the first normal binade — the single
modeling choice that makes the smallest-normal/largest-subnormal
boundary provably *not* special), and proves:

- **`lemma_gap_up_is_successor_distance`** — `gap_up(cs,e) = unit(cs,e)`
  is *exactly* `val_of(succ) - val_of(current)`, for every position
  (same-exponent step or binade-boundary step alike).
- **`lemma_gap_down_is_predecessor_distance`** — `gap_down(cs,sigbits,e,s)`
  is *exactly* `val_of(current) - val_of(pred)`, including at binade
  boundaries (where it is proved to equal `unit(cs,e)/2`, via
  `lemma_unit_doubles`: `unit` provably doubles with each exponent
  increment).
- **`lemma_smallest_normal_gap_not_halved`** — the smallest normal's gap
  to the largest subnormal is proved to equal the *unhalved* unit,
  confirming the code's explicit exception.

**A bug was caught and fixed during this derivation**: the first draft
of `gap_down` halved `unit(cs, e-1)` instead of `unit(cs, e)` — i.e. it
would have asserted a *predecessor* gap of `unit(cs,e)/4` relative to
the correct value, off by a factor of 2 — and F* correctly refused to
verify the successor/predecessor distance lemma until the definition
was corrected to match the algebra actually proved by
`lemma_succ_binade_boundary`/`lemma_unit_doubles`. This is a direct,
concrete illustration of the audit methodology catching an error before
it could be mistaken for a verified fact.

All lemmas in `Z3FpaRoundingBits.fst` are proved with no
`admit`/`assume`.

## What this audit does *not* establish

- A composed "capstone" theorem substituting the proved true
  predecessor/successor values directly into `round_nearest_even`'s
  midpoint formulas (i.e. restating `lower_mid`/`upper_mid` as
  `(pred+r)/2`/`(r+succ)/2` and re-deriving `round_nearest_even` from
  `round_nearest_true_neighbors`). The arithmetic identity is
  straightforward on paper (`r - gap_down/2 = r - (r-pred)/2 =
  (r+pred)/2`, using the distance lemmas above), but mechanizing it
  cleanly needs a handful of `rat_eq` congruence lemmas (`rat_eq`
  respects `rat_add`/`rat_sub`/`rat_half`) not yet added — a natural,
  bounded next step, not attempted here to avoid an open-ended
  nonlinear-arithmetic proof-engineering detour.
- That the directed-rounding (`RNA`/`RTP`/`RTN`/`RTZ`) and
  overflow-to-infinity/saturation branches of PR #10888 — only the
  nearest-even case was formalized here — correctly use these same
  gap values; by symmetry of construction they almost certainly do,
  but this was not separately checked.
- That either PR's C++ *implementation* is a byte-for-byte correct
  encoding of `round_nearest_even`/`grs_brackets` in SMT bit-vector
  arithmetic across every `(ebits, sbits)` combination, subnormal
  boundary, and directed-rounding mode — that would require extending
  `Z3FpaConverter.fst`'s bit-pattern theory to the `round()`/`unpack()`
  pipeline, explicitly flagged as a gap in `FPA_REPORT.md`.
- Any judgment on issues #10176/#9953/#8052/#7842/#7431 beyond noting
  their existence; they were not re-triaged in depth here.

## Re-triage of the remaining issues (this update)

Each of the five previously-unexamined issues was read in full and
checked against the current `master` code. Two led to new, mechanized
F* modules; the other three were resolved by inspection.

| # | Verdict | Detail |
|---|---|---|
| [#9953](https://github.com/Z3Prover/z3/issues/9953) | **Same root cause as #10881/#10931** | Repro is `fp.add RNE a t` vs. `to_fp 8 24 RNE (+ 1.0 (fp.to_real t))` — a compound real expression fed into the same `mk_to_fp_real` symbolic branch. Neither PR changes the entry point's structure, only the constraint on `x`, so both #10888 and #10938 fix this the same way they fix #10881/#10931. No new F* work needed; it is an instance of `Z3FpaRoundingAudit.fst`'s already-proved `exact_roundtrip`-vs-`round_nearest_even` gap. |
| [#10176](https://github.com/Z3Prover/z3/issues/10176) | **Likely same root cause, with an unexplained secondary artifact** | Repro uses `(_ to_fp 8 24) RTN (to_real F)` with `F` a free `Int`, also hitting `mk_to_fp_real`'s symbolic branch. The reported invalid model contains a spurious uninterpreted `/0` function over reals — a hallmark of `nlsat`/NRA real-algebraic model completion filling in witnesses for an under-constrained variable. Removing the old exact-equality constraint (both PRs do this) removes the specific equation whose root-isolation is the most likely source of that artifact. **Not independently re-verified** that the `/0` artifact disappears under either PR; checked instead (see PR recommendation above) that #10888 introduces no new division/power construct that could itself cause it. |
| [#8052](https://github.com/Z3Prover/z3/issues/8052) | **Out of scope — not a soundness bug** | "Unsat only with unnecessary asserts, else unknown" is a quantifier-instantiation/decision-procedure *completeness* issue (`unknown` vs. the "obviously implied" `unsat`), not an incorrect answer. There is no correctness property to state and falsify here (no wrong result is ever produced); it was not formalized. |
| [#7842](https://github.com/Z3Prover/z3/issues/7842) | **Distinct bug, formalized: `Z3FpaNanCongruence.fst`** | `(distinct x (Flt (_ NaN 8 24)))` with `(fp.isNaN (getFlt_1 x))` is reported `sat` with an invalid model `x = Flt(NaN)`. Root cause (per the issue's own investigation thread): the FP theory's `=` already collapses all NaN bit-patterns into one equivalence class, but the datatype theory's congruence closure — operating on the raw encoding once an FP value is nested inside a constructor — does not, so two differently-encoded NaNs (`0x7f800001` vs `0x7f800002`) end up in different congruence classes and `distinct` spuriously succeeds. See new section below. **Confirmed still unresolved/open design discussion** as of the last thread comment. |
| [#7431](https://github.com/Z3Prover/z3/issues/7431) | **Distinct bug, formalized: `Z3FpaZeroSign.fst`** | `(_ to_fp 2 6) RTZ v = (fp (_ bv1 1) (_ bv0 2) (_ bv0 5))` (i.e. "can some real round, under RTZ, to **negative** zero?") is reported `sat` with an invalid model. Root cause pinned down directly in `mk_to_fp_real`'s symbolic branch, **unaffected by either PR**: the line `// x = 0 -> result = +0/-0` asserts `x = 0 ==> (result = pzero \/ result = nzero)`, a disjunction that is actually *vacuous* given the only two zero-kinds the rest of the function already narrows `result` to. See new section below. |

## New finding: the "x = 0" sign bug (issue #7431, `Z3FpaZeroSign.fst`)

`mk_to_fp_real`'s symbolic branch ends with (current `master`,
`fpa2bv_converter.cpp`, unchanged by both open PRs):

```cpp
// x = 0 -> result = +0/-0
m_extra_assertions.push_back(m.mk_implies(m.mk_eq(x, zero),
    m.mk_or(m.mk_eq(result, pzero), m.mk_eq(result, nzero))));
```

But IEEE-754 conversion of the *mathematical real* `0` — which, unlike
a floating-point zero, carries no sign bit — must yield `+0` under
**every** rounding mode; there is nothing for the rounding mode to
decide. Restricted to the two-element domain `{pzero, nzero}` the rest
of the function has already narrowed `result` to in this case, the
quoted disjunction is **provably a tautology** (`lemma_old_constraint_
is_vacuous`), i.e. it rules out nothing at all — exactly reproducing
#7431's invalid model (`lemma_old_constraint_admits_invalid_model`).
`Z3FpaZeroSign.fst` proves the fix — replacing the disjunction with
the single equation `result = pzero`, unconditionally, for every
rounding mode — is sound, strictly stronger, still admits the correct
witness, and is in fact the *unique* minimal repair
(`lemma_fix_is_minimal_and_unique`). **This is a one-line fix, not yet
covered by #10888 or #10938, and not yet filed as a PR.**

## New finding: NaN cross-theory congruence (issue #7842, `Z3FpaNanCongruence.fst`)

`Z3FpaNanCongruence.fst` models two notions of FP-value equality: `fp_eq`
(the FP theory's own, NaN-payload-collapsing "="), and `raw_eq` (bit-exact,
distinguishing NaN payloads — what a datatype/UF congruence closure
effectively uses once an FP value is nested inside another theory's
term). It proves:

- `fp_eq` is an equivalence (`lemma_fp_eq_equivalence`), matching the
  issue thread's own claim ("SMT equality (=) on FP terms already
  handles the both-NaN case correctly").
- `raw_eq` refines `fp_eq` but not conversely (`lemma_raw_eq_refines_fp_eq`):
  two NaNs with different payloads are `fp_eq`-equal but not `raw_eq`-equal.
- Wrapping with `raw_eq` (`dt_eq_buggy`) is **not a congruence** of
  `fp_eq` for the datatype constructor (`lemma_dt_eq_buggy_is_not_a_congruence`),
  while wrapping with `fp_eq` directly (`dt_eq_correct`) trivially is
  (`lemma_dt_eq_correct_is_congruence`) — this is the precise formal
  shape of the bug.
- The exact reported invalid model is reproduced as a corollary
  (`lemma_reproduces_invalid_model`): `is_nan` holds, the FP values
  *are* `fp_eq`-equal, yet `dt_eq_buggy` reports them distinct.
- The fix direction floated in the issue thread by @wintersteiger
  (canonicalize every FP-sorted sub-term — `if is_nan(v) then NaN else v`
  — before it crosses into another theory) is proved **exactly
  equivalent** to using the correct equality directly
  (`lemma_fix_restores_congruence`), and closes the specific
  counterexample above (`lemma_fix_closes_the_gap`). This formally
  validates the maintainers' proposed repair direction, though the
  thread's own last comment notes the actual landed partial
  implementation does not yet canonicalize at *every* crossing point
  (raw `(fp ...)` terms reaching UF arguments directly still slip
  through) — **this issue remains open and unresolved in the codebase**,
  this audit only establishes that the proposed fix *shape* is correct.

## Fix implemented: NaN wrap canonicalization (issue #7842, `Z3FpaNanWrap.fst`)

Follow-up session: traced the exact mechanism in `theory_fpa.cpp::
relevant_eh` (the "general"/opaque-term branch: a non-FPA-family
relevant term `n`, e.g. a datatype selector result, gets a *fresh,
unconstrained* `(sgn,exp,sig)` triple via `convert(n)`, wrapped via
`m_converter.wrap(n)`; a literal `(_ NaN eb sb)` numeral instead gets
`mk_nan`'s single *fixed* bit pattern `sign=0, exponent=all-1s,
significand=1`). `theory_datatypes`' congruence closure then compares
these `wrap(...)` bit-vectors with ordinary, FP-oblivious equality —
exactly the gap `Z3FpaNanCongruence.fst` modeled abstractly.

`Z3FpaNanWrap.fst` refines that model to the concrete bit level
(`pow2`-based triples/`concat`), proving: (a) the defect concretely —
two distinct, both-valid-NaN triples yield different `concat`/wrap
values; (b) the fix — asserting `is_nan_triple t ==> t == canonical_nan`
once per relevant term — collapses every NaN triple's wrapped value to
one fixed bit pattern; (c) the fix is satisfiable (admits the canonical
witness); (d) the fix is conservative — leaves every non-NaN triple's
constraints untouched (`lemma_fix_is_conservative`), addressing the
thread's "pairwise-equality causes exponential blowup" concern by
construction: it is a *unary*, per-term canonicalization, not a
pairwise axiom.

**C++ fix** (`theory_fpa.cpp::relevant_eh`, general branch, after the
existing `wrap(n) = concat(...)` assertion): computes the is-NaN
condition directly from the already-extracted `(sgn,exp,sig)` bv
components (`exponent = all-1s /\ significand != 0`) and asserts

```cpp
assert_cnstr(m.mk_implies(is_nan_conv, m.mk_eq(wrapped, canon_nan_wrapped)));
```

where `canon_nan_wrapped` is built as a raw bv-numeral concatenation
matching `mk_nan`'s fixed choice (`sign=0, exponent=all-1s,
significand=1`) directly — *not* via a second `convert()`/`wrap()`
round-trip through `m_fpa_util.mk_is_nan`/`mk_nan`, which was tried
first and found to reintroduce a (non-deterministic, optimizer- and
instrumentation-sensitive) crash by re-entering the FPA-to-BV
conversion/caching machinery from inside `relevant_eh` itself; building
the canonical bits directly from already-computed BV terms avoids any
such re-entrancy.

**Verified**: both the datatype repro from the issue and the sibling
"raw FP result from a UF reaching another theory" variant the issue
thread flagged as *still broken* under a prior partial community fix
now both return `unsat` with `model_validate=true` clean (this fix, at
the general `relevant_eh` branch, covers both — a UF application's
result is likewise "non-FPA-family", so it takes the same code path).
Full `test-z3 /a` suite: 111/111 passing, no regressions. **Fixed,
merged in PR #11088** (combined with the #10176 fix below); issue
#7842 auto-closed on merge. Permanent regression test added in
`src/test/fpa.cpp`.

`fpa2bv_converter::mk_to_real` (the FP->Real direction, a different
function from the Real->FP rounding encoding audited above) computes
the float's real value as `(sgn=1 ? -1 : 1) * rsig * 2^exp2` (or its
reciprocal for negative `exp2`), using `m_arith_util.mk_power`/`mk_div`
over a symbolic exponent. `rsig` is always in `[1,2)`, so the result's
*sign* is already fully determined by `sgn` alone, for *any* positive
power-of-two factor — but only by re-deriving that fact through the
nonlinear `mk_power`/`mk_div` terms. The issue's repro composes this
`to_real` result through `fp.roundToIntegral` and (arithmetic) `to_int`
with a free `Int F <= 0`: the mathematical spec forces the whole
expression non-positive, yet Z3 answered `sat` with an invalid model
(`model_validate=true` rejected it) — the nonlinear-arithmetic core
failed to re-derive the sign fact through that composition.

`Z3FpaToRealSign.fst` proves, treating a symbolic power of two
abstractly as any strictly positive real (the only fact the argument
needs — it does not re-verify `mk_power`'s own bit-level correctness):
(1) `mk_to_real`'s result is sign-determined by `sgn` alone, for every
positive power-of-two factor (`lemma_to_real_sign_pos`/`_neg`); (2) that
sign-determinism composes soundly through any "never increases" pair of
maps (modeling RTN rounding and `to_int`'s floor) applied to a
non-positive input (`repro_is_unsat`), confirming the repro is
mathematically `unsat`, matching cvc5's verdict; (3) the proposed fix —
asserting the sign fact as a redundant linear implication — is a true,
non-restricting consequence of the existing encoding for every valid
`(sgn, rsig, pw)` (`fix_holds`), so it cannot shrink the solution space,
only give the arithmetic core a direct linear shortcut in place of the
nonlinear reasoning it was failing at.

**C++ fix** (`fpa2bv_converter.cpp::mk_to_real`, right after `result` is
assembled): mirrors the already-merged "rounding never changes the
sign" helper in the opposite-direction `mk_to_fp_real` (PR #10888) —

```cpp
m_extra_assertions.push_back(m.mk_implies(m.mk_and(not_special, sgn_is_1), m_arith_util.mk_lt(result, zero)));
m_extra_assertions.push_back(m.mk_implies(m.mk_and(not_special, m.mk_not(sgn_is_1)), m_arith_util.mk_gt(result, zero)));
```

**Verified**: the 6-line repro and both variants from the issue (pinned
rounding direction, integer form) now return `unsat` deterministically
in well under a second (previously a fast unsound `sat`, or — on
current `master`, after #10888 — a many-minutes-long non-termination).
Full `test-z3 /a` suite: 111/111 passing, no regressions. **Fixed,
merged in PR #11088** (combined with the #7842 fix above); issue
#10176 closed manually with an explanatory comment (did not
auto-close via the merge). Permanent regression test added in
`src/test/fpa.cpp`.


# Non-Linear Arithmetic Lemma Formalization Report

## Scope

This report documents an F* formalization ([`Z3NlArith.fst`](Z3NlArith.fst)) of the
mathematical tautologies underlying the lemma-generation code in Z3's
non-linear arithmetic (NLA) solver, located in `src/math/lp/nla_*.cpp`.

Each lemma generator in that code (`lemma_builder lemma(...)` with a
descriptive name/comment) emits a conflict or propagation clause whose
correctness depends on a fixed piece of elementary algebra: a sign fact,
a monotonicity fact, a McCormick envelope inequality, a power/exponent
fact, a division/modulo identity, or a classical real-analysis bound for
a transcendental function. The F* file states each of these facts as a
standalone lemma and has them **mechanically verified** by F*'s type
checker (which in turn discharges the proof obligations to Z3's own
theories of linear/non-linear real and integer arithmetic).

**Power-scope correction (#11180):** the statements in the original power
section use a shared natural exponent, not the live real exponent in the
emitted C++ clauses. They therefore did not validate those clauses; both
original bound clauses are unsound. The targeted
[`PR_11180_POWER_REPORT.md`](PR_11180_POWER_REPORT.md) gives checked
counterexamples, corrected variable-exponent clauses, and their proofs.
The rational-exponent lemma here merely restates its premise; the new audit
proves positive-root uniqueness and acceptance against actual real power.

## Method

- F* `2026.09.27` (Windows x86_64 release) and its bundled Z3 `4.15.3`
  were downloaded from the official `FStarLang/FStar` GitHub releases
  and used standalone (no project build system required).
- [`Z3NlArith.fst`](Z3NlArith.fst) was verified with:
  ```
  fstar.exe Z3NlArith.fst --z3rlimit 40
  ```
  Result: `Verified module: Z3NlArith — All verification conditions
  discharged successfully`, with **zero** `admit`/`sorry` in the proof
  bodies. The only `assume`s in the file are nine explicitly-labeled
  real-analysis axioms for the transcendental functions (see §5 below),
  which are standard textbook facts, not shortcuts around the lemmas
  being verified.
- Real-valued reasoning uses `FStar.Real` (an axiomatically/Dedekind
  constructed model of the reals, native to F*'s SMT encoding).
  Integer division/modulo reasoning uses F*'s built-in `int` with
  `FStar.Math.Lemmas`.

## Source-to-lemma correspondence

| C++ source | Lemma family | F* lemmas |
|---|---|---|
| `nla_basics_lemmas.cpp` | Sign & zero-propagation lemmas for products (monics) | `lemma_zero_forward`, `lemma_zero_converse`, `lemma_zero_converse_step`, `lemma_nonzero_product`, `lemma_sign_consistency`, `lemma_neutral_factor`, `lemma_proportion` |
| `nla_order_lemmas.cpp` | `a > b & c > 0 => ac > bc` and its variants (order lemmas on monic factorizations) | `lemma_order_strict_pos`, `lemma_order_strict_neg`, `lemma_order_nonstrict_pos`, `lemma_order_divide_common_factor`, `lemma_order_cancel_pos`, `lemma_order_cancel_neg`, `lemma_order_eq_cancel` |
| `nla_monotone_lemmas.cpp` | Bounding `|m|` by the product of bounds on its factors | `lemma_monotone_upper_nonneg`, `lemma_monotone_upper_abs`, `lemma_monotone_lower_abs` |
| `nla_tangent_lemmas.cpp` | McCormick tangent-plane relaxation of `z = xy` | `lemma_mccormick_lower`, `lemma_mccormick_lower2`, `lemma_mccormick_upper`, `lemma_mccormick_upper2`, `lemma_tangent_line` |
| `nla_powers.cpp` | Natural-exponent algebraic helpers only; not a validation of the original variable-exponent clauses (see the #11180 audit) | `lemma_pow_zero_exp`, `lemma_zero_pow`, `lemma_pow_pos`, `lemma_pow_gt_one`, `lemma_pow_le_one`, `lemma_pow_monotone`, `lemma_pow_monotone_le`, `lemma_pow_exact`, `lemma_pow_rational_exponent_check` |
| `nla_divisions.cpp` | Monotonicity of real division; Euclidean floor-division bounds; modulo congruence/linear-divisibility closure | `lemma_div_monotone1/2/3`, `lemma_bounded_division_upper`, `lemma_bounded_division_lower`, `lemma_mod_congruence`, `lemma_linear_divisibility` |
| `nla_transcendentals.cpp` | Linear majorants/minorants and sign/monotonicity facts for `exp`, `log`, `sin`, `cos`, `atan2` | `lemma_exp_lower_bound`, `lemma_exp_monotone`, `lemma_log_upper_bound`, `lemma_log_monotone`, `lemma_sin_pos`, `lemma_sin_neg`, `lemma_cos_pos`, `lemma_atan2_pos`, `lemma_atan2_neg` |

47 lemmas in total, all verified.

## What was verified (and what wasn't)

**Verified, from first principles (no axioms beyond the reals/integers
being an ordered field / Euclidean domain):**

1. **Zero-propagation and sign consistency** (§1 of the file). The
   monic/factor abstraction in `nla_basics_lemmas.cpp` is modeled as
   plain real multiplication; `lemma_zero_converse` (`xy = 0 => x = 0
   \/ y = 0`) is exactly the zero-divisor-free property of the reals,
   and `lemma_neutral_factor`/`lemma_proportion` are proved directly by
   Z3's quantifier-free non-linear real arithmetic (QF_NRA) decision
   procedure — the same engine, and the same style of degree-2 facts,
   that `nla_core.cpp` itself relies on at runtime.
2. **Order lemmas** (§2): `a > b & c > 0 => ac > bc` and all sibling
   variants (non-strict, negative multiplier, cancellation, equality)
   are proved directly; these are literally the invariant stated in
   the `nla_order_lemmas.cpp` header comment.
3. **Monotonicity lemmas** (§3) and **McCormick tangent-plane lemmas**
   (§4): the bilinear relaxation inequalities (e.g. `x*y >=
   yl*x + xl*y - xl*yl` whenever `(x-xl)*(y-yl) >= 0`) are proved by
   expanding the square `(x-xl)(y-yl) >= 0`, confirming that every
   plane `generate_plane` emits is a *sound* outer/inner approximation
   of the surface `z = xy`, not merely locally tangent at one point.
4. **Integer powers** (§5): `x^0 = 1`, `0^y = 0` (`y != 0`), `x > 0 =>
   x^y > 0`, `x > 1 => x^y > 1`, and both directions of monotonicity
   (`x >= x0 > 0 => x^n >= x0^n`, `0 < x <= x0 => x^n <= x0^n`) are
   proved by structural induction on a **shared** natural-number exponent.
   These do not justify clauses relating a live exponent `y` to a model
   numeral `n`. Also, this helper's `0^0 = 1` is not Z3's underspecified
   `0^0`; the source's zero-exponent axiom excludes base zero.
5. **Division and modulo** (§6): the three monotonicity schemas from
   `divisions::check`'s `monotonicity1/2/3` lambdas are proved directly
   over reals. The floor-division bound lemmas
   (`check_bounded_divisions`) and the modulo congruence identity
   (`check_mod_congruence`, which the C++ comment itself labels a
   "tautology...for every integer delta") are proved over `int` using
   `FStar.Math.Lemmas`' division lemmas, confirming the C++ comment's
   claim precisely: the clause is valid for *every* integer `delta`,
   `y`, independent of the model values used to instantiate it, so the
   solver's choice of a model-derived `delta` can never introduce
   unsoundness.

**Verified as logical consequences of stated axioms (not re-derived
from analysis):**

6. **Transcendental function lemmas** (§7): `exp`, `log`, `sin`, `cos`,
   `atan2` are not part of any decidable first-order theory, so (as
   Z3's own `nla_transcendentals.cpp` does internally) they are
   axiomatized: nine `assume`s state the exact real-analysis facts the
   C++ code relies on (`exp(t) >= 1+t`, `log(t) <= t-1` for `t>0`,
   monotonicity of `exp`/`log`, sign of `sin` on `(0,pi)`/`(-pi,0)`,
   sign of `cos` on `(-pi/2,pi/2)`, sign of `atan2` by the sign of its
   first argument). Given those axioms, each emitted lemma is then
   proved to be an exact instance — i.e., what is verified here is that
   the solver's clauses are *valid consequences* of the real-analysis
   facts it is implicitly trusting, with no additional slack or
   off-by-one errors in the inequalities as transcribed from the C++
   source.

**Modeling simplifications, stated explicitly:**

- Monics (`m = f_1 * f_2 * ... * f_k`) are mostly formalized via their
  pairwise/binary core case (two factors), since every n-ary lemma in
  the C++ code is itself derived by pairwise factorization
  (`factorization_factory_imp` splits a monic into exactly two
  factors before any lemma is generated). The one n-ary fact used
  directly (`lemma_zero_converse_step`) is shown to generalize to any
  number of factors by the same one-step peeling argument, noted in
  the comment at its definition.
- `fdiv`/`int` lemmas model Z3's **Euclidean `div`/`mod`** convention
  (non-negative remainder) using F*'s native truncating `/`, restricted
  to positive divisors `y > 0`, which is exactly the regime the two
  `check_bounded_divisions` branches operate in.
- Grobner-basis lemmas (`nla_grobner.cpp`) and interval-propagation
  machinery (`nla_intervals.cpp`) are *proof-search* components (they
  combine already-sound linear-arithmetic facts via Buchberger-style
  polynomial reduction and interval arithmetic) rather than additional
  independent mathematical tautologies; their soundness reduces to the
  basic polynomial-identity and interval facts already covered above,
  so no separate lemmas were added for them.

## Executable incremental-linearization certificates

`src/math/lp/nla_lemma.cpp` now captures an owned polynomial-refutation
certificate when arithmetic evidence is enabled. It snapshots the original
LP explanation facts, the negations of the actual conclusion literals,
and the frozen linear-variable and monomial definitions. The serialized
certificate includes these source facts, their premise/conclusion partition,
the expanded polynomial inputs, the derivation, and the contradictory root.
It remains usable after the originating LP solver is destroyed.

The independent replay kernel has five rules: input, product, multiplication
of an equality by an arbitrary polynomial, square nonnegativity, and a
weighted sum with a nonnegative constant offset. Inequality weights must be
nonnegative; equality weights may have either sign. A sum containing a
disequality may contain only one nonzero disequality contribution and
otherwise only equalities. All polynomial coefficients, certificate weights,
and offsets are integral after positive denominator clearing. Strictness is
reconstructed rather than supplied by the producer.

[`Z3NlaLemma.fst`](Z3NlaLemma.fst) supplies an executable counterpart and
proves `check_sound`: no real assignment can satisfy all of the supplied
polynomial input facts when the checker accepts the refutation. Its
polynomial-arithmetic dependency, `Z3LinearArithmeticTheory.fst`, was also
verified. These proofs add no axioms or admissions.
[`Z3NlaLemmaTests.fst`](Z3NlaLemmaTests.fst) exercises tangent-plane,
tangent-line, and square certificates and rejects invalid references,
negative inequality weights, and cancellation of two disequalities.

The C++ regressions exercise zero/nonzero products, sign, shared-factor
order, neutral factors, upper/lower monotonicity, repeated-factor squares,
and tangent lines/planes. They also obtain certificates from the actual
tangent and monotonicity generators, including non-strict box-corner
planes, check retained ownership, reject malformed certificates, and
exercise the proofs-disabled path. Certificate search is bounded and may
use a separate LP solve; neither replay kernel calls a solver. Search
failure is explicitly **unsupported**, not an assumed or checked lemma.

All three NLSAT production paths are separately marked **assumed**:
native theory proofs retain `arith assumed nlsat`, and SAT/EUF hints use
`nlsat-assumed`. The SAT/EUF log writes these clauses as `assume`, with
the origin hint retained in a preceding comment; its online proof checker
also treats them as assumptions instead of rerunning a solver on them.
Other hint categories do not acquire assumption status.
Native F* marshaling preserves the origin as
`Unverified "assumed:nlsat"`, so these leaves remain reported obligations.
They never acquire polynomial certificates merely because NLSAT produced
them.

**Remaining correspondence boundary:** the F* soundness theorem starts
from polynomial facts. The C++ kernel additionally expands frozen LP
definitions, but this source expansion is not yet formalized in F*.
The native F* marshaler does not decode the new certificate or prove that
its inputs are exactly the negation of the original native AST clause.
Consequently it must not treat the `arith nla` tag as a verified proof
rule; such native nodes still require obligations. The executable C++ and
F* kernels are corresponding implementations, not a verified compilation
of C++ into F*. Integer-only reasoning, variable-exponent identities,
division/modulo, and transcendental facts not derivable in this ordered-ring
calculus also remain unsupported by this new certificate path, irrespective
of whether a separate schema above has already been proved.

## Conclusion

All 47 cataloged lemmas type-check and are verified by F*/Z3 with no
unproved obligations beyond the nine explicitly-documented
transcendental-function axioms. This verifies the stated mathematical
lemmas, not every clause the C++ generators can emit. In particular the
original power-clause correspondence was too weak and missed the soundness
bug documented in [`PR_11180_POWER_REPORT.md`](PR_11180_POWER_REPORT.md).
That follow-up proves the corrected variable-exponent bounds and records
the remaining real-analysis obligation for the separate growth clause.

# Exponentiation NFV audit: #11180

## Result and audited revision

**Both original monotonicity clauses in `nla::powers::check` are unsound.**
For bases between zero and one, exponentiation decreases with the exponent.
There is a second issue even for an anchor base above one: the upper clause
needs a nonnegative live-exponent guard when the live base can cross below
one. Merely disabling refinement below base one does not fix that issue.

The audit covers master `916ff9feed8622e5c6ce5c5a7f7894c79d099ac6`.
At inspection, including a recheck after proof completion on October 15,
2026, #11180 was open with no changed files and only initial-plan commit
`1d567cba688a442ffa3119ed37f7614ee802b39e`. Thus there was no PR
implementation to validate. The correction audited below is the local
change in this worktree, not a claim about a subsequently updated PR.

Artifacts:

- [`Z3PowerPreprocessing.fst`](Z3PowerPreprocessing.fst): rewriting and
  theory-bridge identities, natural/real power correspondence.
- [`Z3PowerSaturation.fst`](Z3PowerSaturation.fst): literal-for-literal
  old/corrected bound clauses, concrete counterexamples, corrected-clause
  proofs, other saturation clauses and model-acceptance checks.
- `src/math/lp/nla_powers.cpp`: corrected bound generation.
- `src/test/smt_context.cpp`, `check_real_power_bounds`: incremental
  regressions for both reported queries over eight random seeds.

## Semantics and trust boundary

The new modules use `FStar.Math.Pow.pow` for **positive-base, real-exponent**
power. Its implementation constructs real powers using real completeness
and Archimedean reasoning; the audit does not replace exponentiation by an
uninterpreted function. Natural powers reuse the existing
`Z3ArithRewriterPower.ipow`. The checked `integer_bridge` connects them:

```text
pow(x, of_int(n)) = ipow(x, n),  x > 0, n : nat.
```

`ipow` also supplies ordinary natural-exponent identities for negative
bases. Separately, `zero_base_value` models Z3's `0^y = 0` for `y != 0`,
including negative exponents, while `zero_exponent_value` leaves `0^0`
arbitrary. `nonnegative_power` joins these cases to positive-base power.
**Z3's underspecified `0^0` is not silently assigned the helper's `ipow 0 0`.**

There are no `assume`, `admit`, `admit_smt_queries`, or lax-mode shortcuts
in the new modules. The proofs rely on F*, its standard real/integer model,
the checked standard power library and the SMT backend. They are
value-level mathematical proofs with a manually reviewed source
correspondence, not an extraction or mechanized semantics of the C++ AST,
numeric libraries, random branch selection or entire SMT solver.

The separate `x_ge_3` growth clause has an explicit remaining analysis
boundary, described below. No proof of a corrected bound or counterexample
uses that boundary. The audit deliberately avoids `FStar.Math.Exp`, whose
implementation contains admitted basic facts.

## Preprocessing and theory bridges

The relevant source is `arith_rewriter::mk_power_core` and `reduce_power`
in `src/ast/rewriter/arith_rewriter.cpp`.

| Source operation | Checked theorem(s) and scope |
|---|---|
| `1^y -> 1`, `x^1 -> x`, nonzero `x^0 -> 1` | `rewrite_base_one`, `rewrite_exponent_one`, `rewrite_exponent_zero` for positive real bases; existing integer identities for natural exponents |
| Zero base / `0^0` guard | `rewrite_zero_nonzero_exponent`, `rewrite_zero_natural`, `preserve_zero_zero`; arbitrary `0^0` preserved |
| Natural numeral folding and optional product expansion | `integer_bridge`, `rewrite_natural_expansion`, `fold_half_square`; mathematical evaluation, not numeral-manager implementation |
| Negative-integer numeral folding | `reciprocal_integer`, `rewrite_negative_integer`; nonzero reciprocal product identity also holds for negative bases |
| Nested powers with integer exponents | `rewrite_nested_natural`, `rewrite_nested_negative_integer`; all real bases for natural powers, nonzero bases for the reciprocal identity |
| Positive-base nested powers | `rewrite_nested_positive`, proving `(x^y)^z = x^(y*z)` |
| Exponent `-1` and negative real-exponent reciprocal rewrite | `rewrite_negative_real`, positive-base branch; zero branch modeled separately as zero rather than division by zero |
| Fractional split `x^(m/d) -> (x^(1/d))^m` | `rewrite_fractional_split`, positive base, `m >= 0`, `d > 0` |
| Rational/algebraic root fold | `rational_root_equation`, `rational_root_unique`, `fold_quarter_root`; positive candidate checked by its root equation |
| Power reduction in products compared with zero | `reduce_zero_equality`, `reduce_zero_order`; equality keeps one factor, inequalities preserve exponent parity, with arbitrary product-context coefficient |

The root axioms in `src/smt/theory_lra.cpp`, `mk_power_axiom`, and
`src/sat/smt/arith_axioms.cpp` are covered by `nonnegative_root_axiom`:

```text
x >= 0, m > 0, d > 0
  => ipow(nonnegative_power(opaque_0_0, x, m/d), d) = ipow(x, m).
```

The LRA reciprocal-root clause is its `m = 1` instance. The positive-base
positivity bridge is the standard power library's positive result.
The `power0` fallback remains underspecified rather than being assigned a
new negative-base real-power semantics.

**Not fully verified:** negative-base fractional/algebraic folding and
root-selection conventions; every zero/negative-base nested rewrite;
the implementations of rational/algebraic root extraction; AST traversal,
sort preservation, rewrite proof objects and configured expansion limits.
The existing natural-power lemmas were not sufficient to certify these
additional cases, and this audit does not claim otherwise.

## Exact failing saturation clauses

The affected code is the rational-model branch of `powers::check`,
under `xval > 0 && yval.is_unsigned()`. Let

```text
x0 = xval > 0, n = yval.get_unsigned(), C = ipow(x0,n).
```

Here `x0`, `n`, `C` become constants in a learned clause. **The live
variables `x`, `y`, `r` do not become constants.** In particular the test
that the current model's `yval` is natural does not restrict every future
interpretation of `y`.

At the audited base revision, the bound branches (approximately lines
189-203) emitted:

```text
lower_old = x < x0 OR y < n OR r >= C
upper_old = x <= 0 OR x > x0 OR y > n OR r <= C
```

`lower_old` and `upper_old` in the F* module reproduce those disjuncts.
Both are false under actual positive-real-power interpretations:

| Checked theorem | `x0`, `n` | Live `x`, `y`, actual `r = x^y` | False conclusion |
|---|---|---|---|
| `old_lower_counterexample` | `1/2`, `1` | `1/2`, `2`, `1/4` | `1/4 >= 1/2` |
| `old_upper_counterexample` | `1/4`, `1` | `1/4`, `1/2`, `1/2` | `1/2 <= 1/4` |
| `reported_upper_counterexample` | `1/2`, `1` | `1/2`, `1/2`, `sqrt(1/2) > 1/2` | `sqrt(1/2) <= 1/2` |
| `old_upper_negative_exponent_counterexample` | `2`, `1` | `1/4`, `-1`, `4` | `4 <= 2` |

The first and third witnesses directly establish satisfiability of the two
queries in #11179. The square-root inequality is derived from the checked
positive root equation; no irrational numeral or assumed root ordering is
needed. An independent `prove.py` run using only the polynomial identity
`r = x*x` also refutes the original lower clause with `x=1/2,y=2,r=1/4`.

There is an additional guard obligation when reversing the below-one
lower bound. `reversed_lower_without_nonnegative_guard` proves that
`x0=1/2,n=1,x=2,y=-2,r=1/4` refutes the proposed lower bound if it allows
all `y <= n`. The required `y >= 0` guard is therefore essential, not a
conservative heuristic.

## Corrected bounds and checked proofs

The local C++ correction splits on `increasing = xval >= 1` and emits the
following implications, represented exactly by `lower_fixed` and
`upper_fixed`:

| Anchor regime | Lower-bound antecedent (`r >= C`) | Upper-bound antecedent (`r <= C`) |
|---|---|---|
| `x0 >= 1` | `x >= x0`, `y >= n` | `0 < x <= x0`, `0 <= y <= n` |
| `0 < x0 < 1` | `x >= x0`, `0 <= y <= n` | `0 < x <= x0`, `y >= n` |

The clauses use the negations of these antecedents as disjuncts. Below
base one, the exponent disjunct changes direction. The below-one lower
bound and above-one upper bound also acquire `y < 0` disjuncts.
The emitted clauses still exclude the offending current model: its
`y = n` is nonnegative, so neither the reversed inequality nor the new
guard makes the clause vacuous at that model.

`lower_fixed_sound` and `upper_fixed_sound` prove these clauses for
**every real live exponent `y`**, all positive live/anchor bases and
every natural anchor exponent, including zero. `nonpositive_base_clauses`
proves the clauses trivially true when live `x <= 0`, without introducing
semantics for arbitrary negative-base real powers.

The proofs compare exponents at the **live** base using
`FStar.Math.Pow.pow_mono` / `pow_antitone`, and compare bases at the
**natural anchor exponent** using `integer_base_mono`. When the live base
crosses one they use the bound against `1`. Thus no additional assumed
general real-exponent base-monotonicity theorem is needed.

## Other LP rules and acceptance paths

| `powers::check` clause / path | F* correspondence |
|---|---|
| `x = 0 OR y != 0 OR r = 1` | `zero_exponent_clause`, `general_zero_exponent_clause`; no restriction on `0^0` |
| `x != 0 OR y = 0 OR r = 0` | `zero_base_clause`, Z3's zero-totalization |
| `x <= 0 OR r > 0` | `positive_result_clause` |
| `x <= 1 OR y >= 0 OR r < 1` | `negative_exponent_clause`, for real exponents |
| `x <= 1 OR y <= 0 OR r > 1` | `positive_exponent_clause`, for real exponents |
| Exact-point refinement `x != x0 OR y != n OR r = C` | `exact_point_clause` |
| Natural-exponent model acceptance | `natural_acceptance` |
| Positive fractional-exponent acceptance `r^d = x^m` | `rational_acceptance`; positivity plus `d > 0` gives the unique positive real power, in rational and algebraic model modes |
| `x < 3 OR y <= 0 OR r-y > 1` | `growth_clause`, conditional as described next |

The algebraic model branch reuses the same elementary clause builders and
root-equation acceptance; it does not contain a second copy of the faulty
monotonicity code. `nla::core::check_powers` clears state and removes
infinitesimals before checking powers; the rational path also explicitly
rejects infinitesimal model coordinates. These control/model mechanisms
were reviewed, not formally verified.

### Explicit remaining growth-analysis obligation

The actual `x_ge_3` disjuncts conclude `r > y+1`, regardless of the
builder's stronger-looking textual `ln(x)y+1` label. The proof
`growth_clause` takes an explicit `growth_analysis` record containing:

1. `pow(x,y) = exp(y*log(x))`;
2. `exp(t) >= 1+t`;
3. monotonicity of `log`;
4. `log(3) > 1`.

F* verifies that these imply the emitted clause for all positive bases
and real exponents. **No inhabitant of this record is constructed here.**
Consequently this is a checked conditional proof, not a completed
unconditional proof of the real-analysis prerequisites. The record fields
are not global axioms and do not strengthen the assumptions used by any
counterexample or corrected-bound theorem.

## Prior audit gap

`Z3NlArith.lemma_pow_monotone` and `_le` prove base monotonicity for a
**shared natural exponent**. The original C++ clauses relate **different
live and anchor exponents**. Replacing both by one `n` drops precisely the
condition that causes the reported bug. A model numeral cannot justify
that replacement.

Also, `lemma_pow_rational_exponent_check` proves only its premise again;
it does not establish root uniqueness. Finally its natural-power model
sets `0^0=1`, whereas the source preserves underspecification.
The existing module's comments and reports are corrected to expose these
scope gaps and point to the new proofs, rather than claiming that
successful verification of weaker statements certified the original code.

## Reproduction and verification

The new modules were checked with F* `2026.09.27`, commit
`7deb38a27c86990664c6b41e4b6093597acdebd4`, and the packaged Z3
`4.13.3`. Example PowerShell commands, with `$tools` pointing at the
installed F* distribution and `$cache` at a checked-module cache:

```powershell
& "$tools\bin\fstar.exe" --smt "$tools\lib\fstar\z3-4.13.3\bin\z3.exe" `
  --cache_checked_modules --cache_dir $cache --include C:\z3\fstar `
  --z3rlimit 20 C:\z3\fstar\Z3PowerPreprocessing.fst
& "$tools\bin\fstar.exe" --smt "$tools\lib\fstar\z3-4.13.3\bin\z3.exe" `
  --cache_checked_modules --cache_dir $cache --include C:\z3\fstar `
  --z3rlimit 20 C:\z3\fstar\Z3PowerSaturation.fst
```

Both modules report **all verification conditions discharged successfully**.
An expected-failure negative control attempting to prove the original lower
clause at its concrete counterexample was rejected by F* with the intended
proof error; it is not part of the repository's normal verification inputs.
The native solver/tests were rebuilt with Clang-CL 22.1.3, and all
**115 standard unit tests passed**, including the new eight-seed
incremental regressions.

The baseline executable returned `unsat` on both reported incremental
queries. The corrected executable returns **`unknown`**, not `unsat`.
This is an intentional soundness regression criterion: the formal witnesses
prove both queries satisfiable, but general real powers need not be decided
by the implementation. The correction does not claim to make transcendental
arithmetic complete. Pinning the exponents to the witnesses `2` and `1/2`
respectively gives `sat` for both queries. Reciprocal/zero-base smoke checks
also give `sat`, including `(1/4)^(-1) = 4` and Z3's `0^(-1) = 0`.

# zwine integer exponentiation NFV soundness audit

## Result: five verified modules, scoped mathematical soundness

**All five current proof modules verified successfully from a new, empty,
isolated cache with `--z3refresh`, with every verification condition
discharged and exit code 0.** Each root's checked-cache absence was
asserted before execution, and actual query statistics were observed;
this was genuine query replay, not cache-only acceptance. Verification was
executed by the parent session on October 17, 2026, using WSL F*
nightly-2026-09-04, commit
`52f17ab8fdea379708a659a1b02c8f8b47f877fa`, and independent stock Z3
4.13.3. The actual verifier logs were also inspected in this proof-editing
session. The executable paths were:

```text
F*: /root/.local/fstar/bin/fstar.exe
Z3: /root/.local/fstar/lib/fstar/z3-4.13.3/bin/z3
```

The documented Windows F*/Z3 paths were absent in this environment;
no Windows verification success is claimed. No binary built from zwine
was used to verify its proofs. **Global**
`--smtencoding.nl_arith_repr native` was passed for every module, including
dependencies, and rlimit remained at most 10 throughout.

The checked results cover integer absolute-exponent semantics, rewrite
identities, all six guarded refinement formula schemas, the mathematical
acceptance kernel, and private-phasing preservation principles. The prime
formula is checked for ordinary prime divisors; primality of the C++
routine's generated numeral remains a separately reviewed source invariant.
**This is not a machine-checked refinement of the C++ implementation or a
proof of the whole SMT solver's soundness.** Explicit boundaries appear
throughout and are consolidated below.

The work is restricted to `fstar/Z3Swine*.fst`, this report, and its index
entry. No C++, benchmark, test, or existing power proof was modified.
No commit was made.
Unrelated user-owned changes in `src/ast/rewriter/recfun_rewriter.h`,
`src/sat/smt/q_mbi.cpp`, and `ff_dumps` are explicitly excluded.

### Revision and source-map qualification

Inspection found `.git/HEAD` selecting `refs/heads/zwine`, whose loose ref
contained `f9e0081d41bec4c5683e246a3bd632551cd3edb3`. The audit concerns
the **working tree**, including uncommitted changes, not just that commit.
The parent froze the final C++ candidate on October 17, 2026. Source ranges
below were refreshed against that working-tree snapshot and are identified
primarily by function name. They do not cover future edits or unrelated
working-tree changes.

The parent subsequently implemented integer rewrites for `(-1)^y`,
`0^y`, and eager expansion of nonnegative numeral exponents up to 10,
respecting the maximum degree. These branches were reinspected in
`mk_power_core:1854-1888` and match the checked identities. The initial
and reset exponent box now use bound 1 (`theory_lra.cpp:87,4020`).
`arith_swine::check:347-362` now gives bounding priority over pairwise
monotonicity. Both use valid formula schemas, so this selection-order
change does not change the mathematical obligations. The adjacent-only
induction experiment was reverted: `induction:212-253` still considers
all eligible pairs and retains the symbolic-delta/specialization guards.
No other helper/formula edits were retained. This is the final source
delta supplied by the parent and reinspected for this report.

## Artifacts and checked coverage

| Module | Implemented obligations | Checked status |
|---|---|---|
| [`Z3SwinePower.fst`](Z3SwinePower.fst) | Integer absolute-exponent semantics; product/addition/nesting laws; sign/parity; base/exponent monotonicity; growth; rewriter identities; resource-bounded repeated-squaring model | PASS, all VCs discharged |
| [`Z3SwineRefinements.fst`](Z3SwineRefinements.fst) | Exact symmetry, strict pairwise monotonicity, all six bounding branches, symbolic/specialized delta recurrence; prime formula and guard counterexamples | PASS, all VCs discharged |
| [`Z3SwineInterpolation.fst`](Z3SwineInterpolation.fst) | Discrete convexity, denominator-cleared bilinear upper bound, unit-cell lower extrapolation with actual `x>=1` guard | PASS, all VCs discharged |
| [`Z3SwineSearch.fst`](Z3SwineSearch.fst) | Private Boolean erasure, valid-lemma preservation, private-phase blocking, distinction between bounded UNSAT and original UNSAT | PASS, all VCs discharged |
| [`Z3SwinePrime.fst`](Z3SwinePrime.fst) | Prime-divisibility biconditional for signed bases/exponents using standard Euclid's theorem | PASS, all VCs discharged |

All modules use rlimit 10 or less and contain no `admit`, `assume`,
`admit_smt_queries`, or lax-mode directive. Native nonlinear encoding is
an ordinary SMT representation choice, not an axiom or proof bypass.
Its global use is necessary for the recorded reproducible verification
configuration; a module-local override alone was not sufficient in the
fresh-cache experiments.

The existing `Z3ArithRewriterPower.ipow`, `Z3PowerPreprocessing`, and
`Z3PowerSaturation` were inspected before development. Their principal
representation is real-valued natural power or positive-base real power.
The new integer-valued recurrence is needed to state integer remainder
and divisibility formulas without inventing a real-to-integer conversion.
The new modules do not import `FStar.Math.Exp` or posit analytic axioms.
The parent supplied the actual WSL standard-library sources for
`FStar.Math.Euclid.fsti/.fst`, `FStar.Math.Lemmas.fst`, and
`FStar.Math.Lib.fst`. Their signatures and implementations were inspected
before writing the prime proof. No admit/assume/lax markers were found in
the supplied files.

## Semantics: Int is not Real

The specification is:

```text
magnitude(y) = if y<0 then -y else y
power(x,0) = 1
power(x,n+1) = x*power(x,n)
exp(x,y) = power(x,magnitude(y))
```

Every base, exponent, and result is an unbounded mathematical integer.
Thus `exp(2,-3)=8`, not `1/8`, and `exp(0,0)=1`.
No semantic change to real exponentiation is intended or certified here.
In particular, the old report's underspecified real `0^0` must not be
silently identified with the new integer operation.

Checked `magnitude_product` establishes
`abs(y*z)=abs(y)*abs(z)` by sign cases, enabling the all-sign nesting law.
`magnitude_parity` establishes `abs(y) mod 2 = y mod 2`, including negative
exponents using Euclidean modulo. `power_sign` then gives the sign of a
negative base without a reciprocal convention.

Mathematical trust boundary: F*'s
kernel/typechecker and VC generator, SMT backend, standard integer model,
and any imported checked library dependencies. The present files do not
constitute a formal semantics, extraction, or refinement proof of C++,
the AST manager, rational arithmetic, enodes, proof logging, or SAT/LRA/NLA
integration.

## Exact refinement families

Here `E(x,y)` abbreviates `exp(x,y)`. The result term in C++ is interpreted
as that mathematical value; candidate model observations are **not**
assumed to hold under every valuation satisfying a learned lemma.

### 1. Symmetry

Source: `arith_swine::symmetry`, `arith_swine.cpp:69-101`.

Each negative observed coordinate selects a syntactic negation and
contributes a live `<0` guard. If a negative base was selected, the RHS is
an ITE over **the original exponent's** remainder modulo 2:

```text
(selected-negative-base -> x<0)
AND (selected-negative-exponent -> y<0)
  ->
E(x,y) =
  if selected-negative-base AND mod(y,2)=1
  then -E(normalized_x,normalized_y)
  else  E(normalized_x,normalized_y)
```

`normalized_x` and `normalized_y` negate exactly the selected coordinates.
`symmetry_clause` reproduces this branch-dependent guarded formula.
`symmetry_sound` uses negative-exponent invariance and signed parity.
No guard is inferred from an unselected positive model observation.

### 2. Strict pairwise monotonicity

Source: `arith_swine::monotonicity`, `arith_swine.cpp:103-126`.
Checked theorem: `monotonicity_sound`.

```text
x>1 AND y>0 AND z>=x AND w>=y AND (z>x OR w>y)
  -> E(z,w)>E(x,y)
```

The strictness disjunction is necessary: identical base/exponent pairs do
not have strictly different powers. `y>0` is essential for strict base
monotonicity, and `x>1` for strict exponent monotonicity. The proof
separates non-strict comparison from each strict case.
Observations used to decide whether to emit a clause are not additional
logical premises.

### 3. Bounding

Source: `arith_swine::bounding`, `arith_swine.cpp:128-172`.
Checked theorem: `bounding_sound`.

The exact emitted implications/biconditional are:

```text
y=0 -> E(x,y)=1
y=1 -> E(x,y)=x
(x=0 AND y!=0) <-> E(x,y)=0
x=1 -> E(x,y)=1
x>0 -> E(x,y)>=1
x>1 AND y>1 AND x+y>4 -> E(x,y)>x*y+1
```

The zero-result branch is a **biconditional**, not merely a forward
implication. Nonzero integer bases have nonzero natural powers; `0^0=1`
supplies the exceptional zero-base case.
In the growth branch, the integer guard excludes `(x,y)=(2,2)`, which
would otherwise refute the inequality (`4` is not greater than `5`).
The theorem proves the `y=2`, `y=3`, and inductive larger-exponent cases
separately; it uses no real exponential growth assumption.

### 4. Prime divisibility — checked schema, manual witness correspondence

Source: `arith_swine::prime`, `arith_swine.cpp:174-210`.
`prime_clause` records:

```text
mod(E(x,y),d)=0 <-> (mod(x,d)=0 AND y!=0)
```

This requires **a prime integer `d>1`**. It is valid for negative bases and
negative exponents under absolute-exponent semantics, not just the
positive current observations used by C++ to search for a witness.

`Z3SwinePrime.prime_power` inducts the checked library's `euclid_prime`
through the natural-power recurrence. Its zero-exponent branch uses
`divides_1` to exclude a prime dividing 1. The forward direction for a
divisible base uses the library's divisibility/product and modulo bridges.
`prime_clause_sound` then instantiates the recurrence at `magnitude(y)`,
explicitly connecting `magnitude(y)>0` with `y!=0`.
The primality premise is the library's ordinary `is_prime`, defined by
the integer divisor characterization, not a postulated product law.
The parent reports the new module PASS, all VCs discharged.

Still not mechanized:

1. Prove the C++ search really selects a prime witness: previously tested
   shared prime factors have been completely stripped, so a composite
   trial divisor cannot become a first witness, and the terminal residual
   selected after the square-root test is prime.
2. Connect Euclidean integer `%` to the C++ rational `mod` for integer
   arguments and a positive divisor.

The current source has no emitted primality guard; primality must be a
fact about the generated numeral, not an assumed property of live `x`.
The precise **source-review invariant** at trial divisor `k` is:
both residuals are positive integers, and no prime smaller than `k`
divides either residual. It holds vacuously at `k=2`. When divisibility
differs, `k` divides one residual; a composite `k` would have a smaller
prime divisor of that residual, contradicting the invariant. When
divisibility agrees, complete stripping of `k` removes it from both
residuals and division cannot introduce any smaller prime factor.
Moving from 2 to 3, and then across the skipped even numbers, skips no
prime. At the terminal square-root test, a residual greater than 1 must
be prime: any composite residual would have a prime divisor at most its
square root, which is smaller than `k`. This argument explains why
testing odd composite divisors in the loop does not emit a composite
witness. The invariant and its preservation are **not mechanized over
the C++ loop**, and the source correspondence remains an explicit
manual audit boundary.

The nonzero-exponent conjunct is essential because `E(x,0)=1`.
`prime_zero_exponent_guard_needed` is a checked concrete refutation of
the formula with that conjunct omitted.

### 5. Induction / constant delta recurrence

Source: `arith_swine::induction`, `arith_swine.cpp:212-253`.
Checked theorems: `induction_sound`, `specialized_induction_sound`.

```text
x=z AND y>=0 AND w-y=delta
  -> E(z,w)=E(x,y)*power(x,delta),   delta>0 a fixed numeral
```

The model's equal bases are retained as live equality. Nonnegative
**smaller** exponent plus positive constant delta ensures both
exponents have ordinary natural-power semantics. A checked
counterexample in `induction_nonnegative_guard_needed` shows why crossing
zero cannot use the same unguarded recurrence.

The final inspected source uses:

* A numeral factor for a syntactically numeral base.
* A polynomial product of `delta` copies of the symbolic base for
  `delta<=64`.
* For larger deltas, a numeral factor **and** the additional live guard
  `base=observed_base`.

The specialized theorem retains that extra guard. Merely knowing a base's
current value would not justify using the same constant factor in all
future models. The numeral-base branch instead fixes the base by syntax.
The arbitrary-delta theorem covers the mathematical product independently
of either unrolling threshold.

### 6. Denominator-cleared bilinear interpolation

Source: `interpolant` / `interpolation`,
`arith_swine.cpp:255-345`. Checked theorems: `upper_sound`, `lower_sound`.

For positive integer corner coordinates `a<=b`, `c<=d`, define:

```text
dx = if a=b then 1 else b-a
dy = if c=d then 1 else d-c
L = dx*E(a,c) + (E(b,c)-E(a,c))*(x-a)
U = dx*E(a,d) + (E(b,d)-E(a,d))*(x-a)
N = dy*L + (U-L)*(y-c)
```

`numerator` reproduces exactly this cleared expression, including the
degenerate-width convention. The upper formula is:

```text
a<=x<=b AND c<=y<=d -> dx*dy*E(x,y)<=N
```

Both widths are positive, so clearing the denominator does not reverse
the bound. The proof applies one-dimensional discrete secant
upper bounds twice with nonnegative weights; equal-coordinate cases are
separated rather than dividing by zero.

The lower formula uses only a unit cell `b=a+1,d=c+1`:

```text
x>=1 AND y>=c -> E(x,y)>=N
```

**There is no `x>=a` guard in the source or in the checked theorem.**
The argument therefore handles `1<=x<a`, not just northeast extrapolation.
With `t=y-c>=0`, first lower-bound in the exponent to obtain:

```text
H(x)=x^c * (1+t*(x-1)).
```

Then prove `H` discretely convex for integer `x>=1`, using

```text
Delta H(x) = t*x^c + (1+t*x)*Delta(x^c).
```

All factors needed for monotonicity are nonnegative on that domain.
A unit secant of a discretely convex integer function is a lower bound on
both sides of its anchor: no integer lies strictly between `a` and `a+1`.
This gives the actual lower formula. Independently lower-bounding
`(1-t)*x^c` and `t*x^(c+1)` would be an invalid proof when `t>1`; the
proof deliberately does not take that shortcut.

Remaining C++ correspondence obligations include preservation of positive
integer anchors in `m_points`, reset/reuse bookkeeping, exact computation
of all four corner constants, and handling of failed computations.
Fallback anchor selection changes coefficients only; it does not supply
any unexpressed guard on live variables.

## Rewriter, declaration, and purification correspondence

Refreshed source anchors:

| Source | Candidate / manual boundary |
|---|---|
| `arith_decl_plugin.cpp:200-202`, `OP_POWER` selection near 386 | Inspected `Int*Int -> Int` declaration, separate Real declaration. Sort implementation is not mechanized. |
| `arith_decl_plugin.cpp:902-907` | Inspected zero-zero uninterpreted special-case restricted to Real base. Integer `0^0=1` is deliberate. |
| `arith_rewriter.cpp:1826-1889`, integer `mk_power_core` branch | `rewrite_zero`, `rewrite_one`, `rewrite_one_base`, `rewrite_neg_exponent`, `rewrite_nested`, `rewrite_nonnegative_numeral`; numeral engine and AST transformations are not verified. |
| `arith_rewriter.cpp:1098-1119`, shared-exponent multiplication | `rewrite_common_exponent`, valid for any signed integer exponent and bases, including zero. |
| `arith_rewriter.cpp:1675-1692`, power/type helpers | Manual-only type-preservation correspondence; helper code is not modeled. |
| `purify_arith_tactic.cpp`, `process_power` beginning near 441 | Integer-power skip is a manually inspected dispatch obligation, not a theorem about the tactic pipeline. |
| `arith_rewriter.cpp:1854-1868`, new symbolic-exponent `-1` branch | `rewrite_minus_one_base`: ITE on `mod(y,2)=0`, signed parity included. |
| `arith_rewriter.cpp:1854-1868`, new symbolic-exponent `0` branch | `rewrite_zero_base`: ITE on `y=0`, integer `0^0=1`. |
| `arith_rewriter.cpp:1880-1887`, eager small numeral expansion | `rewrite_nonnegative_numeral`: all nonnegative exponents, where `power` is the recursive product of exactly that many factors. Threshold/maxdegree policy is not proved. |

The nested identity is `(x^y)^z=x^(y*z)` because
`abs(y*z)=abs(y)*abs(z)`. It does not rely on real-power identities for
negative bases. No purported equality of Int negative exponents with
reciprocals is used.

## Candidate evaluation, resource limits, and acceptance

Source: `compute_power` / `check_model`,
`arith_swine.cpp:24-67`; `get_power_value` /
`check_integer_powers`, `theory_lra.cpp:1779-1840`.

`get_power_value` requires integer rational values; in algebraic-model
mode it rejects non-rational algebraic values. The model check normalizes
the exponent by absolute value, checks every collected relevant power,
and can return true only when every successful exact value agrees.
The bitsize precheck can reject a candidate without materializing a huge
power. That rejection must never be confused with an original-formula
UNSAT proof.

`square_budget` models repeated squaring with explicit `None` on resource
exhaustion; its refinement claims correctness only for `Some`. Checked
`checked_acceptance` connects successful equality checking to `exp`.
This is a mathematical kernel model, **not** a proof that the C++ loop,
resource counter, bit cap, or rational arithmetic refines it.

Manual inspection found:

* The helper can stop at its coefficient-size or resource cap.
* `check_model` remembers incomplete evaluations and does not convert them
  to `l_true`.
* `arith_swine::check` returns acceptance immediately only on `l_true`.
* A remaining mismatch/incomplete result either produces refinement or
  returns unknown; the caller returns `FC_GIVEUP` for the latter.
* The final-check dispatcher invokes `check_integer_powers`; the integer
  `eval_unsupported` shortcut is not independently an acceptance proof.

Still unproved: the bitsize lower-bound optimization, exact C++ repeated
squaring, all relevant-term collection/internalization, LP/NLA candidate
coherence, model construction, and absence of other bypasses elsewhere in
the solver. The supplied passing tests are supporting integration
evidence, not replacements for these obligations.

## Private-assumption bounded/unbounded phasing

Source: `theory_lra.cpp`:
`add_theory_assumptions:1596-1616`,
`should_research:1618-1627`,
`check_integer_powers:1818-1823`.

Let `F(v)` be the original input and `B(v)` a finite exponent box.
The private extension is:

```text
F(v) AND (phase -> B(v)).
```

It has exactly the original models **after existentially forgetting the
fresh private Boolean**, because `phase=false` is always available.
Checking under assumption `phase=true` instead checks `F AND B`.
UNSAT of that bounded problem cannot imply UNSAT of `F`:
`n=11` with box `[-10,10]` is a checked concrete counterexample.

`global_lemma_preserves` / `unsat_after_valid_lemma` express the separate
principle that adding a globally valid arithmetic lemma preserves
original models and supports UNSAT transfer.

The initial/reset bound's change from 2 to 1 changes search policy only;
the existential-erasure argument is independent of the box size. The
parent explicitly declined to port reference-code acceptance by
reevaluating original assertions while power interpretations were
inconsistent; no such model-lifting argument is used in these proofs.

The inspected unbounded mismatch path asserts `not phase`. That formula
is **not a globally valid arithmetic lemma**. `block_private_phase`
justifies it only at the level of existentially erased private extensions.
It may reject the whole current private phase; a core containing the
positive private assumption must restart rather than report final UNSAT.
A rejected candidate by itself proves neither `not F` nor a generally
valid arithmetic clause.

`private_independent_core` states the alternative soundness premise:
an unsatisfiable core permits final UNSAT if all its constraints follow
from the original input, independently of private assumptions.

Manual source correspondence reviewed (not a mechanized control-flow proof):

1. `add_theory_assumptions:1596-1616` uses a fresh Boolean and appends it
   to the search assumptions; only guarded box clauses are added.
2. `should_research:1618-1627` recognizes that phase in the returned core,
   alternates bounded/unbounded mode, and doubles the box after an
   unbounded rejection.
3. `src/smt/smt_context.cpp:3577-3612` reconstructs assumption expressions
   in the core. `context::should_research:3565-3574` calls the theories.
   The search loop at `3833-3871` initializes the combined assumptions,
   searches, makes a core, checks for research, and repeats before final
   return. This supports the intended private-core interception argument.
4. Reset reinitializes phase and bound (`theory_lra.cpp:4018-4022`);
   push/pop, cancellation, and reuse tests supply integration evidence.
   Correctness of every trail, core, and lifetime operation remains trusted
   implementation machinery, not a theorem of these pure modules.
5. If powers are discovered too late for an initial box, absence of a
   private phase does not authorize candidate-based UNSAT:
   `check_integer_powers` uses the private rejection path only when the
   phase exists and otherwise checks/learns arithmetic refinements.
   Discovery timing and completeness of term enumeration remain unproved.
6. The acceptance/unknown paths described above remain an essential source
   correspondence obligation; the context and numeric implementations
   themselves are not machine-checked here.

The logical modules do not mechanize SMT context control flow, prove
termination, or establish completeness of alternating bounded/unbounded
search.

## Tests, observations, and findings

`src/test/arith_rewriter.cpp:52-98` samples emitted formulas over bases
including negative values and zero, and exponents including negative,
zero, and positive values. `src/test/smt_context.cpp:139-216` contains the
nine supplied integer-power cases, push/pop/reuse checks, a user-assumption
core check, and resource-limit cancellation/reuse checks.
The parent reports those tests pass; this session did not execute them.

The earlier observation of repeated symmetry lemmas on `-1` bases was a
performance/model-integration issue, not a mathematical counterexample
to a guarded formula. Performance measurements are not used as formal
proof evidence.

**No concrete soundness bug was found in the audited final changes.**
The important guard obligations identified above are retained in the
final inspected source. The report does not infer universal guards
from current-model observations. All six mathematical schemas are checked
within their stated domains, including prime-divisor primality. This does
not prove every generated C++ instance meets those domains, prove the
implementation as a whole, or turn any integration test into a proof.

## Remaining manual/trusted C++ boundary

The following are genuinely **not mechanized** by the five modules:

* Correct translation of C++ ASTs/sorts/guards and learned formulas to the
  mathematical statements, including preservation by rewriting and
  correct `mk_axiom`/internalization/proof-object behavior.
* Arbitrary-precision numeral arithmetic and `%`, exact corner/factor
  computation, the C++ repeated-squaring loop, and bitsize/resource
  calculations. Resource exhaustion is not permitted to imply acceptance;
  the inspected source respects that separation.
* The prime-witness selection loop and the interpolation-anchor cache
  invariants. Their source arguments are documented above rather than
  silently encoded as F* axioms.
* Relevant-term discovery, coherence of rational LP/NLA candidate values,
  SAT/core correctness, trails, push/pop/reset/cancellation lifetimes, and
  full model construction. No original-assertion model-lifting shortcut
  was ported or proved.
* A C++ operational semantics, extraction/refinement theorem, solver
  completeness/termination, performance guarantee, or proof of unrelated
  Real-power cases.

These boundaries limit the audit's claim, not the checked universal
integer theorems themselves.

## Verification commands and actual outcome

The documented Windows installation was absent. The successful hardened
run used the WSL nightly, independent bundled Z3 4.13.3, global native
nonlinear encoding, query statistics, `--z3refresh`, and a new
session-isolated cache.
The five separate invocations have the following PowerShell form
(variables abbreviate the actual paths):

```powershell
$fst = '/root/.local/fstar/bin/fstar.exe'
$smt = '/root/.local/fstar/lib/fstar/z3-4.13.3/bin/z3'
$inc = '/mnt/c/z3/fstar'
$session = '/mnt/c/Users/nbjorner/.copilot/session-state/6f6eaa9f-07df-448a-82bb-5abce03559fe/files'
$cache = "$session/zwine-fstar-hardened-cache"
wsl.exe -e $fst --smt $smt --smtencoding.nl_arith_repr native --include $inc --cache_dir $cache --cache_checked_modules --query_stats --z3refresh /mnt/c/z3/fstar/Z3SwinePower.fst
wsl.exe -e $fst --smt $smt --smtencoding.nl_arith_repr native --include $inc --cache_dir $cache --cache_checked_modules --query_stats --z3refresh /mnt/c/z3/fstar/Z3SwineRefinements.fst
wsl.exe -e $fst --smt $smt --smtencoding.nl_arith_repr native --include $inc --cache_dir $cache --cache_checked_modules --query_stats --z3refresh /mnt/c/z3/fstar/Z3SwinePrime.fst
wsl.exe -e $fst --smt $smt --smtencoding.nl_arith_repr native --include $inc --cache_dir $cache --cache_checked_modules --query_stats --z3refresh /mnt/c/z3/fstar/Z3SwineInterpolation.fst
wsl.exe -e $fst --smt $smt --smtencoding.nl_arith_repr native --include $inc --cache_dir $cache --cache_checked_modules --query_stats --z3refresh /mnt/c/z3/fstar/Z3SwineSearch.fst
```

All five completed successfully in the parent's actual hardened run.
The raw logs are in the same session directory, named
`Z3SwinePower.hardened.verify.log`, `Z3SwineRefinements.hardened.verify.log`,
`Z3SwinePrime.hardened.verify.log`, `Z3SwineInterpolation.hardened.verify.log`,
and `Z3SwineSearch.hardened.verify.log`. Each log includes actual root
query statistics and the pinned Z3 process identity, and finishes with:

```text
Verified module: <module name>
All verification conditions discharged successfully
```

Parent-reported elapsed times for that run:

| Module | Elapsed | Outcome |
|---|---:|---|
| Power | 4.915 s | PASS, exit 0 |
| Refinements | 1.166 s | PASS, exit 0 |
| Prime | 0.857 s | PASS, exit 0 |
| Interpolation | 21.420 s | PASS, exit 0 |
| Search | 0.746 s | PASS, exit 0 |

No failed or canceled queries were reported. There are no new `.fsti`
interfaces; each `.fst` was verified separately. For reproduction, use a
new empty cache and assert each root's `.checked` file is absent before
its invocation. A quick `--z3refresh` run that merely reloads an already
checked root is **not** the replay recorded here.

The proofs use explicit power unfolding, factored polynomial/transfer
lemmas, standard distributivity/associativity, and checked
`Canon.canon()` calculations. No rlimit was increased and no obligations
were admitted. Native encoding is pinned globally for all five invocations,
including imported dependencies. The frozen proof sources were not edited
after the final successful hardened run; only this report and the audit
index were finalized.

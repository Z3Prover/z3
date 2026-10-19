# Checked arithmetic certificates: 2026-10-15

This report preserves the arithmetic-integration evaluation. The subsequent
[SMT-LIB cross-cut](SMTLIB_CROSSCUT_REPORT.md) records both the native-only
baseline and the later coverage extensions on the same 900 inputs. The
native-only baseline retains the arithmetic rules evaluated here; the
later extension adds checked comparison/integer rewrites and typed
observational equality, but no new arithmetic producer evidence.

## Native proof-regression extension: 2026-10-17

The following is a later, separate extension, not a reevaluation of the
historical 900-input sample below. Workflow run `39021665839` tested all
17 SMT-LIB inputs at z3test commit
`b8d11d8edb5ebf7d8693fc58b875c6f90720c6c9`: eight were `ACCEPT`, eight
were `PARTIAL`, and the larger `lean/real/lra_lassoranker.smt2` exhausted
its 10-second solver timeout (`UNKNOWN`, no proof available to check).

The missing support in the partial inputs was:

| Input below `regressions/proofs` | Required checker support |
|---|---|
| `canaries/real_numeral_farkas.smt2` | Real subtraction and exact rational term normalization |
| `lean/lra_boolean_structure.smt2` | Supplied `arith/bound` coefficients and rational normalization |
| `lean/lra_distinct.smt2` | Numeric equality decomposition and triangle-equality clauses |
| `lean/lra_equality.smt2` | Affine equality normalization, equality decomposition, and real addition normalization |
| `lean/lra_farkas.smt2` | Real constant multiplication and subtraction normalization |
| `lean/lra_fractions.smt2` | Real subtraction and exact rational term normalization |
| `lean/lra_implied_equality.smt2` | Numeric equality decomposition |
| `lean/lra_unary_minus.smt2` | Real unary minus and rational normalization |

The rebuilt native checker replays the same pinned corpus with **16 ACCEPT,
0 PARTIAL, 1 UNKNOWN**, under the same 10-second solver, 60-second case,
and 2-GiB process limits. All eight formerly partial proofs are now
obligation-free; LassoRanker still times out before supplying a proof.
These are local native replay results; workflow artifacts independently
record their own producer/corpus commits, outcomes, and timings.

These checks reuse exact polynomial linearization and cancellation.
`arith/bound` now reaches the existing Farkas checker with its original
coefficients, rather than becoming trusted evidence by tag. Equality
decomposition checks both non-strict inequalities; a triangle-equality
clause checks the same algebraic relation independently of its hint.
Wrong coefficients, wrong constants, mismatched bounds, and unsupported
NLSAT assumptions remain obligations.

Real term equality needs a value-level bridge beyond equal numeric
projections. `numeric_model` now explicitly includes equality reflection
for Real-sorted terms. This is an additional standard-value semantic
premise, not a proved consequence of the previous operator-only
projection contract. The pre-existing untyped-environment foundation gap
documented below remains; these are conditional semantic theorems, not
an unconditional SMT-LIB soundness result.

## Result

Arithmetic Farkas certificates now pass through the full proof exporter,
JSON decoder, unified proof kernel, and extracted native checker. The
AST-to-linear-polynomial semantic bridge and certificate soundness theorem
are proved in F*. Checking uses exact integers and rationals, not machine
integer arithmetic or an external arithmetic solver.

A fresh run of the existing **900-input, nine-logic SMT-LIB sample** checked
**6,660 Z3-supplied Farkas certificates in 144 valid derivations**. Every
supplied Farkas certificate encountered in those completed valid derivations
checked. This does not establish validity of certificates in timed-out,
unexported, or structurally rejected proofs.

Full-proof coverage is **193 ACCEPT, 321 PARTIAL, 127 REJECT**, with 252
phase timeouts and seven export exceptions. A partial derivation is not a
certified UNSAT result. None of the 144 derivations containing checked
Farkas nodes is obligation-free: other arithmetic rewrites or theory
steps still block certification.

The principal producer gap is **missing compositional evidence**, not an
observed invalid Farkas certificate in this sample. Bare `arith`,
`assign-bounds`, and `triangle-eq` account for **44,051 remaining arithmetic
obligations**. General integer rounding and Gomory/GMI cuts need separate
checkable rules; a rational Farkas combination alone is insufficient.
No C++ proof producer was changed by this integration.

## Checked fragment and trust boundary

The new modules have distinct responsibilities:

| Module | Responsibility |
|---|---|
| `Z3LinearArithmeticTheory.fst` | Exact polynomial operations, positive combinations, cancellation, and the contradiction theorem `lemma_accepts_sound` |
| `Z3LinearArithmeticAst.fst` | Typed operator recognition, AST linearization, literal polarity, coefficient alignment, and executable certificate checking |
| `Z3LinearArithmeticEmbed.fst` | Semantic AST bridge, integer strict-bound strengthening, and `lemma_check_sound` |
| `Z3UnifiedProof.fst` | `ArithmeticFarkas` nodes with checked premises and preserved hypothesis scopes |
| `Z3ResolutionProofJson.fst` | Validated coefficient decoding and dispatch into the same unified kernel |

For a polynomial `p` obtained by linearizing expression `e`, the proved
invariant is

```text
p.denom * numeric_value(eval(e)) = p.cst + sum(c * numeric_value(eval(atom)))
```

`p.denom` is positive. Integer numerator arithmetic stays executable;
the real-valued semantic projection is ghost-only. The model contract
specifies ordinary typed arithmetic operations, comparison meanings,
and integer-valuedness. It does **not** assume a supplied certificate or
the result of linearization is valid.

**Remaining formal-foundation gap:** these are conditional semantic
theorems, not a completed end-to-end SMT-LIB soundness theorem. The
project's existing `boolean_model` and the arithmetic integer-valuedness
contract quantify over untyped environments. Taken literally for all
expressions/environments, a Boolean variable evaluated in an environment
returning `VInt` already contradicts `boolean_model`. Thus this global
model contract is not inhabitable as currently stated. A meaningful
end-to-end theorem must restrict expressions and environments using a
well-sorted valuation relation and supply a model/interpretation bridge.
This integration proves the polynomial/certificate mathematics and wires
the executable checks, but does not repair that pre-existing global
semantic-model issue or establish an inhabitance theorem for the new
combined model contract.

Supported expression bridges include exact integer/rational numerals,
n-ary addition and multiplication by constants, unary/n-ary subtraction,
real division by a nonzero recognized constant, and `to_real`. Other
numeric expressions, including nonlinear products, may be treated as
opaque atoms keyed by the complete AST, not by printed names. This is a
sound abstraction, not support for nonlinear arithmetic reasoning.

The checker combines true premises followed by the negations of the
conclusion's disjuncts, in their original order. Coefficient counts must
match exactly. Equality coefficients may be signed; inequality weights
use their absolute values, matching Z3's convention. Nonzero weights on
negated equalities are unsupported. Zero weights contribute neither a
constraint nor a strictness flag.

For integer expressions, strict inequalities are strengthened using the
proved rule `a < b => a + 1 <= b`. The same strengthening is not applied
to reals. Acceptance requires all variable coefficients to cancel and
the remaining constant/strictness to contradict the combined inequality.
The checker does not merely recognize an `arith` hint.

The exporter retains raw `theory_params` and, for authentic
`arith/farkas` parameters, emits:

```json
{
  "arithmetic_certificate": {
    "kind": "farkas",
    "origin": "z3",
    "coefficients": [[1, 1], [-2, 3]]
  }
}
```

Numerals have `op_num_rational` with exact `[numerator, denominator]`
parameters. Arithmetic operator tags come from Z3 declaration kinds;
uninterpreted lookalikes are not promoted by name. The `origin` field
is provenance, not authority: the native kernel checks the numbers
against the decoded expressions and premises.

Malformed known certificate encodings are rejected. A well-formed but
unsupported or unsuccessful certificate remains one explicit obligation.
Missing certificates and unknown cut hints remain partial. No certificate
reconstruction, trusted re-solving, or acceptance of bare theory tags was
added.

### Exact extracted arithmetic

The previous 63-bit `Prims.int` shim was unsuitable for unrestricted
arithmetic certificates and decoded large references. It has been replaced
with Zarith `Z.t`, including arithmetic/comparison operators, Euclidean
division and remainder, and fixed-width integer operations. The native
build links with `ocamlfind ocamlopt -package zarith -linkpkg`.

Characters and the character-facing `UInt32` representation remain
native OCaml integers because extracted character patterns use raw integer
literals; their projections to F* integers convert to `Z.t`. List/string
lengths and indexing bridges are consistent with the exact integer type.
There is no numeric wraparound fallback. Resource limits still apply:
arbitrary precision does not imply unlimited allocation, depth, or runtime.
The handwritten runtime and extraction/compiler stack remain part of the
trust boundary; the shim itself is not formally verified.

## SMT-LIB coverage

The sample is unchanged from the pre-arithmetic cross-cut (preserved in Git
at `6e2bed21a`; the [cross-cut report](SMTLIB_CROSSCUT_REPORT.md) now contains
the latest reevaluation):
100 seed-42, UNSAT-annotated inputs per logic from the locally available
official SMT-LIB 2025 non-incremental archives. Every selected input's
SHA-256 was checked. This is a stratified cross-cut, not a population-weighted
estimate, and covers neither SAT/model certification nor undownloaded
bit-vector, floating-point, string, or datatype collections.

Proofs were regenerated with the installed **Z3 Python API 5.1.0.0** and
Python 3.14.7. Native checking used the newly verified OCaml checker in
WSL. Each phase had up to 32 workers, with external limits of 10 seconds
for proving (including startup/parsing), 60 seconds for export, and 10
seconds for native checking. Proving also had a 10-second solver timeout.

Each row contains 100 selected inputs. Export T/F means timeout/exception;
check timeouts are separate from exports that never reached checking.

| Logic | Proved UNSAT | Proof timeout | Exported | Export T/F | ACCEPT | PARTIAL | REJECT | Check timeout |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 7 | 56 | 37 / 0 | 54 | 0 | 0 | 2 |
| QF_AX | 100 | 0 | 98 | 2 / 0 | 79 | 3 | 0 | 16 |
| QF_LIA | 79 | 21 | 69 | 7 / 3 | 12 | 51 | 0 | 6 |
| QF_LRA | 59 | 41 | 55 | 4 / 0 | 3 | 52 | 0 | 0 |
| QF_IDL | 48 | 52 | 23 | 21 / 4 | 2 | 19 | 0 | 2 |
| QF_UFLIA | 97 | 3 | 95 | 2 / 0 | 3 | 92 | 0 | 0 |
| QF_AUFLIA | 100 | 0 | 100 | 0 / 0 | 32 | 62 | 0 | 6 |
| AUFLIA | 91 | 9 | 91 | 0 / 0 | 3 | 13 | 75 | 0 |
| UFLIA | 86 | 14 | 86 | 0 / 0 | 5 | 29 | 52 | 0 |
| **Total** | **753** | **147** | **673** | **73 / 7** | **193** | **321** | **127** | **32** |

The 514 valid derivations contain **2,299,701 proof nodes**. A supplemental
native audit categorized every checked node and matched all 514 timed
native obligation totals. It also confirmed the first failing stage for
all 127 rejected exports: 119 at expression well-formedness, seven at
`proof-bind`, and one at an asserted node. These are not arithmetic
certificate failures.

The following counts are restricted to those 514 valid derivations:

| Logic | Supplied Farkas: checked | Bare `arith`: pending | `assign-bounds`: pending | `triangle-eq`: pending |
|---|---:|---:|---:|---:|
| QF_LIA | 85 | 1,220 | 0 | 0 |
| QF_LRA | 210 | 11,297 | 0 | 0 |
| QF_IDL | 3,269 | 0 | 9,343 | 0 |
| QF_UFLIA | 3,063 | 18,548 | 0 | 3,602 |
| QF_AUFLIA | 26 | 1 | 0 | 0 |
| AUFLIA | 4 | 1 | 0 | 0 |
| UFLIA | 3 | 14 | 0 | 25 |
| **Total** | **6,660** | **31,081** | **9,343** | **3,627** |

Thus 13.1% of the 50,711 encountered arithmetic theory nodes have a supplied
certificate checked by this fragment. The other 86.9% lack such evidence;
they were not mislabeled as invalid Farkas combinations.

Remaining obligations are **30,559 rewrites, 44,051 theory lemmas, and one
`sk` step**. Of 321 partial proofs, 172 need only rewrites, 142 need both
rewrites and theory lemmas, six need only theory lemmas, and one needs
rewrites plus `sk`. Fifty-three of the rewrite-only proofs contain newly
checked Farkas nodes.

Compared with the previous fresh run, ACCEPT changes from 192 to 193.
That extra proof, `QF_AUFLIA_025`, previously hit the native watchdog and
contains no arithmetic certificate. Two heavy QF_IDL exports now hit the
export watchdog. **Do not attribute the extra full acceptance, or the entire
change in aggregate obligation counts, to arithmetic support.** The direct
extension gain is the 6,660 independently checked nodes.

## Performance

The timed pipeline took **341.85 seconds elapsed**: 311.92 seconds for the
proof-generation/export batch and 29.73 seconds for the native batch.

| Completed phase | Count | Median | p95 | Sum of per-job times |
|---|---:|---:|---:|---:|
| Proof generation | 753 | 223.3 ms | 2,362.9 ms | 425.01 s |
| Export | 673 | 560.9 ms | 18,479.8 ms | 2,448.42 s |
| Native checking, ACCEPT/PARTIAL | 514 | 123.9 ms | 4,467.6 ms | 375.99 s |

These are wall-clock latencies under concurrency, not isolated CPU
microbenchmarks. Timeouts are censored observations and are excluded from
the completed distributions above. All-attempted phase totals, including
timeouts/failures/rejections where applicable, are 1,901.95 / 6,880.24 /
706.29 seconds respectively; parallel sums are not elapsed pipeline time.
The supplemental native classification audit took another 16.69 seconds
and is not included in the timed pipeline.

The preceding run's native median/p95 were 125.4/4,097.6 ms and its total
pipeline time was 344.18 seconds. These similar overall measurements are
not a controlled arithmetic-overhead comparison: exported populations,
watchdog outcomes, exact integer representation, and concurrent scheduling
differ. Export remains the main pipeline bottleneck.

## Producer gaps: bound explanations and integer cuts

Source references below refer to repository commit
`11306ced808398e9b03686f096c63771dee8ba82`; the C++ worktree was unchanged.
They identify missing proof evidence, not an unsoundness claim about the
solver's SAT/UNSAT decisions.

| Producer boundary | Evidence lost or missing | Consequence for independent checking |
|---|---|---|
| `src\math\lp\bound_analyzer_on_row.h:298-332` | The weighted row explanation computes local `abs(a_k/a_j)` factors, but the unweighted explanation joins dependencies without factors | A dependency set is not the linear combination that derived the bound |
| `src\math\lp\lar_solver.h:222-227` | `explain_implied_bound` applies one outer coefficient to every leaf of a flattened dependency | Inner derivations' different weights cannot be composed from this representation |
| `src\math\lp\lar_solver.cpp:990-1026` | `check_fixed` turns an infeasibility explanation into joins of constraint indices, discarding weights | Later use of the fixed bound cannot recover that certificate from the joined leaves alone |
| `src\smt\theory_lra.cpp:2467-2470,2589-2613,3758-3762,3827-3842` | `consume` records weights in `m_explanation`, while propagation/conflict paths collect Boolean/equality evidence and transmit reset/empty `m_params` | LP-backed proof nodes commonly expose only `arith`, not the available internal numerical derivation |
| `src\math\lp\lar_solver.cpp:2304-2331` | `adjust_bound_for_int` strengthens a rational bound while retaining the dependency without a rounding proof node | The rounded bound is generally not a rational linear consequence of the original bound |
| `src\math\lp\gomory.cpp:55-86` and `src\smt\theory_lra.cpp:2131-2153` | Bound dependencies are flattened into indices; the piecewise fractional cut computation and subsequent cut assignment do not carry its full derivation | A GMI/Gomory cut requires more than a vector of raw Farkas coefficients |

For example, from `x = 2y`, `y = 3z`, `z >= 1`, and `x <= 5`, coefficients
`[-1,-2,6,1]` in that stated fact order give a contradiction. Replacing
composed inner weights by unit weights does not cancel the variables.
Both cases are native regressions: the composed witness checks and the
flattened-weight candidate remains partial. This example demonstrates the
representation requirement; it does not claim those exact incorrect
coefficients were emitted by Z3.

Concrete producer probes preserve both arithmetic solver configurations'
actual proofs. For the same composed-bound problem, API Z3 5.1 with
`arith.solver=2` emits a Farkas vector (in its own premise order), while
`arith.solver=6` emits bare `arith`. The separate local CLI 5.3 build also
emits bare `arith`. Its build hash is
`6b4041653aaa08e7a14d9398ea37907c15262b9b`, not the audited source HEAD;
it was not rebuilt or used for the 900 proof-generation jobs.

### Are integer certificates checkable?

**Some are, but general cuts need an explicit integer rule.** Strict
integer comparisons are already handled by the proved unit-step
strengthening. Ordinary Farkas certificates over their resulting facts
remain checkable.

In contrast, the integer premises `2x >= 1` and `2x <= 1` have a real
solution `x = 1/2`. No rational Farkas refutation of those raw premises can
exist. An integer-tightening proof can derive `x >= 1` and `x <= 0`, after
which a Farkas refutation is valid.

The captured Z3 proof of this example does exactly that tightening in
`rewrite` steps and then emits a **valid** `farkas 1 1` lemma over the
rounded facts. The current checker still needs those arithmetic rewrite
rules to certify the entire proof. Presenting `farkas 1 1` directly over
the unrounded premises remains partial, as the regression requires.
This distinction prevents incorrectly blaming a valid final Farkas vector
for missing earlier integer reasoning.

General CG/Gomory/GMI certificates should expose the source row, exact
bound derivations and orientations, integer-variable side conditions,
rounding/fractional-part operations, and the resulting cut. Those steps
can be checked by dedicated proved rules. Merely attaching the LP's
current flattened explanation coefficients is not a sufficient repair.

Z3's in-tree `src\ast\proofs\proof_checker.cpp:1434-1461` returns success for
bare arithmetic tags and non-Farkas hints without independently checking
them. The F* checker deliberately does not inherit that policy. Its
coefficient alignment and zero-weight/negated-equality handling also do
not rely on that checker's permissive branches.

The next producer work should therefore preserve a **weighted derivation
DAG**, or compose exact weights when expanding its edges; represent
integer tightening/cuts as separate proof steps; and transport the ordered
evidence into proof parameters. Arithmetic normalization/rounding rewrite
support is the complementary checker work with the largest immediate
full-proof coverage impact.

## Validation and reproducibility

The bottom-up F* verification, extraction, and Zarith-linked native build
completed successfully. The full 67-test exporter/native suite passed,
followed by focused passing tests for the two subsequently added
composed-weight/authentic-certificate cases and the extended integer-cut
case. Regressions cover rational and huge arithmetic, typed operator
bridges, signed equalities, malformed or missing coefficients, polarity,
zero-weight strictness, uninterpreted lookalikes, and local hypothesis
discharge. A large-reference test prevents integer decoding from wrapping
an oversized reference into an existing node.

Persistent artifacts:

```text
C:\smtlib-benchmarks\proof_check_arithmetic_20261015\full
  manifest.json, run_metadata.json, working_tree.patch
  results.json, outcomes.csv, summary.json, z3agent.db
  native_arithmetic_audit.json, supplemental_provenance.json
  arith-integration-build.log, arith-regression-tests.log
  tools\checker, tools\run_crosscut.py, tools\extract_z3_proof.py
  tools\arithmetic_audit, tools\arithmetic_audit.ml, tools\audit_arithmetic.py
  tools\*.fst, tools\*.ml, tools\build_ocaml_checker.ps1
  <benchmark id>\prove.json, extract.json, proof.json, worker logs
C:\smtlib-benchmarks\proof_check_arithmetic_20261015\producer_probes
  arith_producer_probes.py, results.json, *.smt2, *.proof
```

The frozen native checker SHA-256 is
`00b3bd7affabbf89bedbe46c05a7d8f8861e15af530cd0f5dc04caeb976acd0f`.
The main metadata records input/tool hashes and the source worktree patch;
the supplemental provenance hashes the subsequent audit tools, extracted
modules, proof documents, and producer evidence separately.

A fresh replay using the archived tools and the same available inputs is:

```powershell
python C:\smtlib-benchmarks\proof_check_arithmetic_20261015\full\tools\run_crosscut.py `
  --out C:\smtlib-benchmarks\proof_check_arithmetic_replay `
  --tool-snapshot C:\smtlib-benchmarks\proof_check_arithmetic_20261015\full\tools
```

Replays use a new output directory and retain the same limits, manifests,
input-hash checks, and frozen checker hash. Wall-clock censoring can change
which inputs complete. `native_arithmetic_audit.json` is supplemental
classification from the actual extracted functions, not a Python mirror
or a substitute for the native ACCEPT/PARTIAL/REJECT outcomes.

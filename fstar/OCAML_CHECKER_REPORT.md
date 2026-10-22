# Standalone OCaml proof-checker executable

## QF_BV rewrite identities (2026-10-21)

The 25 QF_BV inputs from workflow run `39507298591` were replayed locally
with the existing 10-second solver, 60-second case, and 4 GiB memory limits.
All input hashes match the workflow selection. Exact native expressions
from the five completed partial proofs identify several recurring rewrite
families; the first additions to the production checker are:

* Total unsigned division/remainder: `bvudiv(x, 0) = all_ones`,
  `bvurem(x, 0) = x`, `bvudiv(x, 1) = x`, `bvurem(x, 1) = 0`,
  and exact numeral folding.
* Binary commutativity for `bvand`, `bvor`, `bvxor`, `bvadd`, and `bvmul`.
* Comparisons of BV-valued conditionals with distinct numeral branches:
  `(ite c a b) = a` becomes `c`, and `(ite c a b) = b` becomes `not c`.
  The numeral may appear on either side of the equality.

Recognition uses official native operator kinds, checked arities, sorts,
and numeric widths, not declaration names. The new rules have F* soundness
proofs against the existing conditional BV semantic model; conditional
comparison additionally uses the existing term-ITE semantics. This does
not construct a concrete arbitrary-width BV model for all binder
environments, or add general bit-blast certificate checking.

The full local cohort changes from **0 ACCEPT, 5 PARTIAL, 11 UNKNOWN,
9 TIMEOUT** to **1 ACCEPT, 4 PARTIAL, 11 UNKNOWN, 9 TIMEOUT**.
Paired checks of the five completed proofs remove **182 pending obligations**:

| Input | Previous pending | New pending | New verdict |
|---|---:|---:|---|
| `division_by_zero0.smt2` | 1 | 0 | ACCEPT |
| `QF_BV_bv_bv_h_TicTacToe_cc_reg_max.smt2` | 222 | 45 | PARTIAL |
| `distrib32.sf.smt2` | 10 | 6 | PARTIAL |
| `bitops3.smt2` | 25 | 25 | PARTIAL |
| `rand_40_200_1235844018_0_k=4_unsat.gph.smt2` | 325 | 325 | PARTIAL |

The next priorities are one-bit BV/Boolean identities, modular polynomial
normalization, and extract/concat identities, followed by checked
word-to-bit and carry-circuit certificates. For example, TicTacToe still
needs `(bvnot x = #b1) = (x = #b0)` and
`ite(x = #b0, #b1, #b0) = bvnot x` for one-bit `x`. The distributivity
input needs a modular distributivity identity; the graph input repeatedly
needs addition isolation, like-term cancellation, word/bit equality,
and incrementer circuits. Binary commutativity alone does not establish
these associative, polynomial, or circuit identities.

The 11 solver-unknown and nine case-timeout outcomes do not change in
this replay. These remain completion/resource barriers, separate from the
pending identities in completed proofs.

The broader standalone `Z3BvTheory`/`Z3BvRewriter` library is not a list
of production-supported native rewrites. Before integrating arithmetic
right shift or sign extension, their standalone definitions also need
correction for nonnegative operands: the current complement-based formulas
always fill the new high bits with ones. For example, the standalone
definitions give `bvashr(8, 1, 1) = 128` instead of zero and
`bv_sign_extend(8, 1, 1) = 257` instead of one. These operations remain
outside the production BV fragment extended here.

### Follow-up: BV1, modular arithmetic, and extract/concat

The next checked families add one-bit value/equality encodings, including
`ite(x = #b0, #b1, #b0) = bvnot x` and the equivalence between BV1
equality and equality of the corresponding Boolean tests. Complement
comparisons work at arbitrary supported widths:
`bvnot(x) = n` becomes `x = bvnot(n)`. Complement also folds through
conditionals whose branches are numerals.

Modular replay now checks binary distributivity
`x * (y + z) = x * y + x * z`, normalizes subtraction to addition with an
all-ones coefficient, and handles left-hand zero/one arithmetic identities.
Distributivity is checked against the two endpoints without expanding
arbitrary products into potentially exponential polynomial trees. This
is not yet a general polynomial normalizer or n-ary multiplication checker.

The native bridge now recognizes official extract/concat operator kinds.
Extract declarations preserve `[source_width; high; low]`, and concat
declarations preserve operand widths. The verified recognizers check
arity, sorts, bounds, and result widths before using primitive slice/word
semantics. Replay handles constant and full-width extracts, extraction
of either whole operand from a binary concat, and equality of binary
concats with the same left operand. It does not yet handle arbitrary
partial slices, n-ary concat associativity, or `mkbv` circuits.

The full 25-input replay at the same limits now gives **2 ACCEPT,
3 PARTIAL, 11 UNKNOWN, 9 TIMEOUT**, with no outcome regressions.
Compared with the first BV pass, another **123 obligations** disappear:

| Input | First-pass pending | Follow-up pending | Follow-up verdict |
|---|---:|---:|---|
| `distrib32.sf.smt2` | 6 | 0 | ACCEPT |
| TicTacToe | 45 | 11 | PARTIAL |
| `bitops3.smt2` | 25 | 21 | PARTIAL |
| Graph | 325 | 246 | PARTIAL |

The division-by-zero proof remains ACCEPT. Remaining recurring algebraic
gaps include equality isolation and flattened multiplication/coefficient
cancellation. The other major barrier is checked word/bit reconstruction,
equality, unsigned comparison, and carry circuits. In particular, native
rewrites from an original BV constant to `mkbv` over fresh Boolean
constants are not unconditional identities over independent atoms.
The bit blaster creates these fresh constants in
`src/ast/rewriter/bit_blaster/bit_blaster_rewriter.cpp`'s `mk_const`.
Their integration requires checked fresh definitions/projections and
model extension, rather than accepting the displayed rewrite as an axiom.

### Follow-up: checked modular cancellation and word operations

Modular replay now reassociates native n-ary addition/multiplication into
binary trees, merges nested constant coefficients modulo `2^width`, and
isolates binary sums in equalities:
`x + y = z` becomes `x = z + all_ones * y`. These rules have checked
soundness proofs; this is still not general modular linear collection.

`Z3BvWord.fst` derives numeral/word equivalence, bitwise word equality,
arbitrary in-bounds slices of explicit words, and binary concatenation
of words. Numerals can supply constant bits without globally replacing
BV literals, so existing numeric rewrite recognition is preserved.
The proofs establish bounds and injectivity of little-endian bit-list
encoding, numeral decomposition, and split/append arithmetic. They use
primitive `mkbv` semantics in the existing conditional BV model, not the
target rewrite identities as axioms.

The native API now exposes `Z3_OP_MKBV`, appended to the BV declaration
kinds without renumbering existing entries. Previously these declarations
were reported only as `Z3_OP_INTERNAL`. The bridge recognizes the new
official kind and preserves the numeric result width; it does not trust
the printed name `mkbv`. Word recognition checks a positive width up to
4096, exact bit count, Boolean domains/arguments, and the BV result sort.
Native regressions reject malformed metadata, missing operator identity,
non-Boolean bits, and an arbitrary variable-to-word rewrite.

The strict F*/Pulse verification, extraction, native tests (45 groups),
and CLI tests (26) pass. All 25 BV samples were replayed at the unchanged
10-second solver, 60-second case, and 4-GiB limits. Outcomes remain
**2 ACCEPT, 3 PARTIAL, 11 UNKNOWN, 9 TIMEOUT**, with no outcome regressions.
Another **145 obligations** are discharged, reducing pending obligations
in the completed proofs from **278 to 133**:

| Input | Previous pending | New pending | Verdict |
|---|---:|---:|---|
| TicTacToe | 11 | 4 | PARTIAL |
| `bitops3.smt2` | 21 | 9 | PARTIAL |
| Graph | 246 | 120 | PARTIAL |

These are coverage gains, not new fully certified benchmarks. In the
paired single-run measurements, the graph's end-to-end time rises from
10.41 to 10.97 seconds and checker time from 4.91 to 5.22 seconds.
TicTacToe changes from 0.53 to 0.58 seconds end-to-end, and bitops from
0.18 to 0.23 seconds. These observations are not controlled timing
microbenchmarks.

Exact remaining native obligations identify the next work:

* **Fresh-bit definitions/model extension:** 40 graph rewrites and three
  bitops rewrites, plus one TicTacToe rewrite, reconstruct original BV
  variables from fresh Boolean atoms. They remain unsupported; accepting
  these equalities without verified freshness and projection definitions
  would be unsound.
* **Carry circuits and Boolean equality normalization:** the graph retains
  39 incrementer rewrites and 39 equalities between word/circuit
  representations. Bitops also retains two adder rewrites.
* **Unsigned comparisons:** TicTacToe retains strict/non-strict duality
  and a word comparison; the graph retains a word comparison and a
  comparison split across slices. TicTacToe additionally needs a
  numeral-branch ITE comparison with a non-numeral other branch.
* **Structural/algebraic rewrites:** bitops retains complement over concat,
  native n-ary concat/reassociation, and a modular linear-collection
  equality beyond binary isolation.

The 11 UNKNOWN and nine TIMEOUT cases still require producer/resource
work rather than acceptance of additional unchecked identities.

### Follow-up: carry circuits and complemented Boolean equality

Explicit-word addition now has a checked ripple-carry implementation.
Each sum bit is `(a xor b) xor carry`; the next carry is
`ite(a = b, a, carry)`. The proof separately connects these Boolean
expressions to a pure bit-list adder and proves its exact numeric value,
including the outgoing carry. Discarding that carry then establishes
addition modulo `2^width` using the existing primitive addition semantics.
This adds no new BV model axioms and does not assume an incrementer
identity or a variable-to-fresh-word equality.

Word endpoint comparison checks corresponding bit formulas independently,
reusing structural Boolean equivalence and its bounded eight-atom
truth-table fallback per bit. Numerals can provide constant bit lists.
This avoids requiring a truth table over all variables of an entire
word while retaining the existing operator, width, sort, and scope guards.

The shared Boolean normal form now reuses its checked equality constructor
during normalization as well as contextual specialization. It handles
one or both complemented operands, including
`p = not q` versus `not (p = q)`, structurally. This discharges word/circuit
equality steps that previously exceeded the whole-formula Boolean bound.
Native regressions cover wide complemented equality, general two-word
addition, carry propagation, discarded overflow, a three-bit incrementer,
and rejection of a circuit missing its carry.

At the unchanged BV replay limits, another **80 obligations** disappear:

| Input | Previous pending | New pending | Verdict |
|---|---:|---:|---|
| TicTacToe | 4 | 4 | PARTIAL |
| `bitops3.smt2` | 9 | 7 | PARTIAL |
| Graph | 120 | 42 | PARTIAL |

The total decreases from **133 to 53**. All 39 graph incrementers and all
39 graph word/circuit equalities now check, together with both remaining
bitops additions. The full 25-input cohort remains **2 ACCEPT, 3 PARTIAL,
11 UNKNOWN, 9 TIMEOUT**, with identical per-input outcomes.
The graph's single-run wall time changes from 10.97 to 10.56 seconds and
checker time from 5.22 to 4.93 seconds; these are not controlled
microbenchmarks.

The strict F*/Pulse, extraction, native (45 groups), and CLI (26 tests)
pipeline passes. Because Boolean normalization is shared, a paired
25-input QF_DT retention replay also checks the previous and new binaries:
both give **9 ACCEPT, 2 PARTIAL, 13 UNKNOWN, 1 TIMEOUT**, with identical
per-input verdicts and pending counts.

Of the 53 remaining BV obligations, **44 concern fresh-bit reconstruction**
and still require checked definitions/projections and model extension.
The remaining nine are unsigned comparisons and comparison/slice
splitting, a mixed numeral/non-numeral ITE comparison, complement over
concat, n-ary concat/reassociation, and general modular linear collection.

### Follow-up: unsigned order and remaining structural identities

`Z3BvOrder.fst` now checks unsigned strict/non-strict duality,
`bvult(a, b) = not bvule(b, a)`, and reversed non-strict comparison,
`bvuge(a, b) = bvule(b, a)`. Explicit-word non-strict comparison is derived
from a little-endian Boolean comparator: each more-significant bit pair
selects the lower-bit result when equal, or `not a` otherwise.
Numerals can supply their checked constant bits. A zero lower bound
simplifies to true.

Small numeral lower bounds can split across slices. If `n < 2^m` and
`m < width`, `bvule(n, x)` becomes
`upper(x) != 0 or bvule(n, lower(x))`, with exact high/low bounds and
widths. The proof derives this from quotient/remainder arithmetic and
the existing primitive extract semantics. BV-valued ITE equality also
handles one numeral branch and one arbitrary same-width branch, for
either branch orientation and either equality endpoint.

Word replay additionally checks native ternary concat by reassociating
it into binary concat, and distributes complement over binary concat.
Modular replay checks `(x + y) = 2*x` iff `x = y` by additive
cancellation, not division by two. This is a targeted cancellation
family, not a general modular linear normalizer.

The native bridge preserves official unsigned comparison kinds and
derives their numeric width from the operand sort, not the Boolean
result sort. Recognition checks operator identity, arity, domains,
argument/result sorts, and supported widths. The conditional BV model
now includes primitive numeric unsigned comparisons and ternary concat;
the target rewrites are proved from these semantics rather than assumed.
It still does not supply a concrete combined arbitrary-width model or
the fresh-bit model-extension theorem.

The full strict F*/Pulse verification, extraction, native regression
suite (45 groups), and CLI suite (26 tests) pass. Added native cases
exercise the new families, incorrect polarity/boundaries, missing
operator identity, and malformed comparison/ternary-concat signatures.
All 25 BV samples were replayed at the unchanged 10-second solver,
60-second case, and 4-GiB limits, with identical per-input outcomes:
**2 ACCEPT, 3 PARTIAL, 11 UNKNOWN, 9 TIMEOUT**.

All nine ordinary rewrites left by the carry pass now check:

| Input | Previous pending | New pending | Verdict |
|---|---:|---:|---|
| TicTacToe | 4 | 1 | PARTIAL |
| `bitops3.smt2` | 7 | 3 | PARTIAL |
| Graph | 42 | 40 | PARTIAL |

Pending obligations decrease from **53 to 44**. Exact native probes
confirm that all 44 remaining obligations reconstruct original BV
variables from fresh Boolean words. These are not identities under
independent interpretations. The next required work is checked fresh-bit
projection definitions, reconstruction, and model extension; matching
printed names or admitting the reconstruction equality as a rewrite
would not be sound.

The graph's single-run wall time changes from 10.56 to 10.51 seconds,
and checker time from 4.93 to 4.95 seconds. TicTacToe remains about
0.58 seconds and bitops about 0.23 seconds end-to-end. These are not
controlled microbenchmarks. The 11 UNKNOWN and nine TIMEOUT cases remain
separate producer/resource barriers.

### Follow-up: fresh-bit interpretation extension

`Z3BvFresh.fst` gives a first checked extension condition and an explicit
interpretation constructor for a single original-word reconstruction.
The executable condition requires:

* An uninterpreted nullary original BV constant, width 1..4096.
* An official `mkbv` constructor with checked arity, domains, numeric
  width, and result sort.
* Exactly that many distinct, uninterpreted nullary Boolean constants,
  without declaration parameters, in little-endian order.
* Absence of all these Boolean declarations from every original input,
  including occurrences inside quantifiers. Neither a fresh-name prefix
  nor a printed operator name establishes this condition.

Given the existing conditional BV and Boolean semantics for a base
interpretation `i`, `extend` assigns each fresh Boolean the corresponding
bit of the original constant's numeric projection. It changes only
nullary applications of those declarations. All interpreted operators,
the quantifier interpretation, and other uninterpreted applications are
unchanged.

The verified `lemma_model_extension` establishes, for any environment:

* Preservation of the values of all fresh original inputs, reusing
  `Z3Skolemization`'s structural freshness lemma and quantifier
  extensionality.
* Truth of the reconstruction equality in the extended interpretation,
  for either equality orientation.
* Preservation of quantifier extensionality and of both interpreted
  interpretation fields.

The reconstruction proof does **not** assume `bv_model` for the extended
interpretation. Instead, the fresh word evaluates to the same value as
a word of Boolean literals in the base interpretation. Existing numeric
word semantics and projection injectivity then identify that value with
the original constant. No reconstruction identity is added as an axiom.

The full strict verification/extraction/build pipeline passes, including
46 native test groups and 26 CLI tests. New native cases cover correct
bit order and reconstruction at widths 1, 3, and 8, preservation of other
symbols and non-nullary applications, reversed equality, and rejection
of duplicate bits, input-visible bits (also under binders), malformed
declarations, and missing operator identity. The existing unconditional
rewrite checker still rejects an arbitrary variable-to-fresh-word
equality.

Re-diagnosing the three completed partial BV proofs gives:

| Input | Pending | Passing single-word extension conditions |
|---|---:|---:|
| TicTacToe | 1 | 1 |
| `bitops3.smt2` | 3 | 3 |
| Graph | 40 | 40 |

The bit sets are also pairwise disjoint within each of these documents.
This is **44 matching extension conditions, not 44 discharged proof
obligations**: acceptance remains unchanged.

Two proof obligations still gate document-level integration. First,
compose the single-word construction into one interpretation satisfying
all reconstructions, with checked global disjointness/freshness.
Second, establish the full checker's semantic-model assumptions for that
interpretation, including the BV clauses for terms mentioning the new
bits. Preserving the interpreted function fields alone does not establish
these term-level assumptions. The new theorem proves reconstruction and
input preservation, but deliberately does not claim this model closure
or a concrete arbitrary-width combined model.

### Follow-up: simultaneous extension and BV/Boolean model preservation

`Z3BvFresh` now checks a whole reconstruction context and constructs one
interpretation satisfying it. Each word retains the single-word shape
checks; its fresh bits must also be absent from every other reconstruction
and all original inputs. The extension composes tail-first, preserving
already established equations and the original constants' values.

The new `Z3BvFreshModel` module supplies a semantic-model guard and a
literal-retraction proof: evaluation after a single extension equals
evaluation in the base interpretation after replacing the assigned fresh
nullary atoms with Boolean literals. Retraction preserves sorts, scoping,
operator declarations, and binder indices; it also works under quantifiers
using the existing quantifier-extensionality assumption.

This proves preservation of **all nine clauses of `Z3BvLemma.bv_model`**,
including operations on terms containing the new bits. The primitive BV
closure proof, including its simultaneous-context version, requires only
the base BV model, true/false semantics, and quantifier extensionality; it
does not assume the extended BV model or the broad Boolean-value model.
Separate lemmas transfer the existing Boolean rewrite model, covering
Boolean values, literals, negation, conjunction, disjunction, implication,
equality, Boolean ITE, and XOR.

The combined `lemma_context_extension` establishes preservation of original
input values, truth of every supplied reconstruction (including reversed
equalities), and preservation of BV/Boolean models and quantifier
extensionality. It uses the same numeric projection throughout.

The model-safety guard additionally excludes fresh declarations named
`true`, `false`, `and`, or `or`. The legacy Boolean semantic predicates
constrain these names even for nullary uninterpreted declarations, so
overriding them could violate an existing model assumption. This is a
conservative compatibility restriction, not name-based evidence of
freshness or operator identity.

Strict F*/Pulse verification, extraction, native compilation, all 47
native test groups, and all 26 CLI tests pass. The new native group checks
simultaneous reconstruction, reversed equality, global bit collisions,
input freshness under binders, reserved-name rejection, and literal
retraction/evaluation correspondence.

The actual partial proofs pass the complete, model-safe context guard:

| Input | Pending | Passing simultaneous context |
|---|---:|---|
| TicTacToe | 1 | Yes |
| `bitops3.smt2` | 3 | Yes |
| Graph | 40 | Yes |

**Acceptance is still unchanged: three PARTIAL certificates and 44 pending
obligations.** The next integration gate is preservation of the full
`Z3UnifiedProof.model_sound`, which also contains arithmetic, array,
definition, quantifier, lambda, and normalization assumptions. BV/Boolean
closure alone must not be used as a substitute for that theorem.

The combined theorem remains conditional on the existing Boolean model.
Its Boolean-value predicate quantifies over arbitrary expressions and
environments, including unscoped variables; a typed/scoped treatment is
needed before claiming a concrete model satisfying all these assumptions.
The primitive BV closure result is independent of that broad predicate.
No reconstruction axiom or unconditional rewrite acceptance was added.

### Follow-up: removing impossible environment assumptions

The legacy model issue is now a verified counterexample, not merely a
typing concern. `Z3ScopedModelTests.fst` proves:

* No interpretation satisfies `Z3ObservationalEquality.boolean_model`:
  evaluate `Var 0 Bool` in an environment returning `VInt 0`.
* No interpretation satisfies `Z3LinearArithmeticEmbed.numeric_model`:
  evaluate `Var 0 Int` in an environment returning `VBool false`.
* No interpretation satisfies `Z3ArrayLemma.array_model`: a recognized
  select on an array-sorted variable requires its value to be `VArr`,
  even in an environment returning `VBool false`.

These legacy contracts quantify over these unscoped expressions and
arbitrary environments. Consequently, the existing full
`Z3UnifiedProof.model_sound` has no witness. Its conditional soundness
theorems cannot establish a concrete-model guarantee as currently stated.
These negative regression proofs are test-only and are not imported by
the production model-extension proofs.

`Z3ScopedModel.fst` introduces a replacement scalar-typing contract:
an expression must be well-scoped in an explicit sort context, and each
environment value in that context must have the corresponding Bool/Int
constructor. Other sorts retain their separate theory contracts. The
module proves evaluation typing from application/quantifier typing and
provides a concrete witness for scoped scalar typing, official Boolean
literals, equality reflexivity, and quantifier extensionality. This is
**not** a witness for the full BV/arithmetic/array model; the witness
only establishes that these replacement prerequisites are satisfiable.
Generic `eval` is unchanged: ill-typed environments are excluded by the
contract, not silently coerced or assigned fallback semantics.

The fresh-bit proofs no longer need the impossible Boolean model.
Word/numeral-bit helpers and reconstruction-value proofs now require
only the official interpreted true/false literal semantics. All nine BV
closure clauses likewise use these literal semantics, rather than the
legacy name-wide `true_sound`/`false_sound` contracts.

The new `lemma_scoped_context_extension` combines:

* Original-input value preservation and simultaneous reconstruction,
  including reversed equalities.
* Preservation of the nine-clause BV model with the same projection.
* Preservation of scoped Bool/Int evaluation typing, official literal
  semantics, equality reflexivity, and quantifier extensionality.

Its prerequisites contain neither legacy `boolean_model` nor legacy
`numeric_model`. Reconstruction is proved as value equality for every
member of the context; the proof does not infer value equality by
inverting a merely reflexive equality operator.

The scoped theorem uses the structural `Z3BvFresh.check_context`.
Fresh uninterpreted atoms named `true`, `false`, `and`, or `or` are safe
under these prerequisites: they remain distinct from the interpreted
operators. The earlier reserved-name guard remains only for the legacy
Boolean-model transfer helper. Native regressions deliberately assign
false to an uninterpreted atom named `true`, and true to one named
`false`, while preserving both official literals.

Strict verification (including all three legacy-contract counterexamples),
extraction, all 48 native test groups, and all 26 CLI tests pass. The
three partial benchmark documents still have 1/3/40 pending obligations;
all original assertions and pending formulas are well-scoped, and all
three pass both the structural scoped-context check and the older
model-safe guard.

**Document acceptance remains unchanged.** The next gate is migration of
the existing Boolean, arithmetic, and array replay lemmas, then the unified
document soundness theorem, to scoped/typed semantic contracts. The new
theorem does not claim preservation of the complete Boolean rewrite
laws or the full unified model, and it does not provide a concrete
combined theory model. Simply proving closure of the old full model
would be vacuous and would not discharge this gate.

### Upstream merge compatibility: datatype exclusions

Rebuilding against the updated solver exposed a direct datatype consequence
in the sorted-kernel regressions: infer the remaining constructor recognizer
from negated alternative recognizers. `Z3SortedDatatype.exhaustiveness_from`
checks that the conclusion and excluded alternatives cover every constructor
of the same subject, reusing the existing concrete-model exhaustiveness
theorem. Native cases cover two and three constructors and reject missing
exclusions and exclusions for a different subject. Strict verification, all
48 native groups, all 26 CLI tests, and all 116 solver unit groups pass.

### Equality-aware datatype consequences (2026-10-22)

The remaining QF_DT obligations came from
`theory_datatype::propagate_recognizer` (38 propagations) and
`theory_datatype::sign_recognizer_conflict` (one conflict). Every propagation
had premises `not (is-stack y)` and `x = y`, concluding `is-empty x`.
The conflict combined `not (is-stack t)` with
`stack (top t) (rest t) = t`.

`Z3SortedDatatype.transport_exclusion` now derives a negative recognizer on
the other side of an actual equality premise, checking canonical equality,
official negation, registered recognizer metadata, and closed typed scope.
Its concrete-model soundness theorem proves that the derived fact is true.
The derived exclusions supplement the original premises for the existing
verified exhaustiveness and normalization checks. Both equality orientations
and either premise order are supported; this is one-step transport, not a
general equality-closure procedure.

Strict verification/extraction, all 48 native groups, and all 26 CLI tests
pass. Formal document regressions cover propagation, a non-nullary
constructor conflict, and a missing equality remaining pending. Native
mutations additionally reject unrelated or uninterpreted equality,
uninterpreted negation, incomplete constructor exclusions, and conflicts
with the wrong constructor.

A fresh replay of the same 25 workflow QF_DT inputs at the unchanged
10-second producer, 60-second case, and 4-GiB limits gives **11 ACCEPT,
13 UNKNOWN (producer timeout), 1 TIMEOUT, zero PARTIAL, zero ERROR**.
The two blocksworld proofs move from 2/37 pending obligations to ACCEPT,
discharging all 39 remaining obligations; their proof sizes remain
7,200 and 147,909 nodes. All nine previously accepted inputs remain accepted.
This certifies every completed UNSAT proof in this cohort, not every QF_DT
benchmark or every datatype proof shape.

## Diagnostic-driven equality coverage (2026-10-20)

The regression workflow now separately replays partial and rejected proofs
with diagnostics, without changing coverage budgets or measured case times.
Its statistics parser recognizes the native semantic-path suffix instead
of discarding otherwise valid phase timings.

Replaying the October 19 workflow's 13 partial QF_UFLIA inputs reproduced
all verdicts and pending counts. Their 2,028 obligations were discharged
by checked arithmetic equality propagation and both orientations of
triangle-equality clauses. Equality propagation synthesizes bounded exact
Farkas candidates, independently checks both non-strict bounds against the
actual premises, and applies the proved equality-to-bounds equivalence.
Existing theory checks remain ahead of synthesis on the production path.

The unchanged 25-input QF_UFLIA cohort now gives **25 ACCEPT**, versus
12 ACCEPT and 13 PARTIAL in that workflow. A local full replay of the
225-input sample at z3test `df80f8ce4f6965c2a340806068790c76f6612880`
gives **180 ACCEPT, 5 PARTIAL, 33 UNKNOWN, 6 TIMEOUT, and 1 ERROR**.
Fifteen former partials certify, including one AUFLIA and one UFLIA proof.
The five completed partials retain 32 obligations: arithmetic contradiction
and cut lemmas, plus two large Boolean rewrites.

Two previously accepted workflow inputs hit resource limits locally;
both losses also reproduce with the baseline executable on this machine.
The formerly partial `dlx-regfile.smt2` likewise times out with both
executables. A subsequent replay of all 188 inputs previously completed
by the workflow retains these local outcomes after prioritizing established
checks over synthesis. The native assertion-time OOM remains an explicit
error. These are local measurements, not a new GitHub workflow result.

The opt-in `--sorted-core` mode also makes the existing inhabited,
sort-indexed kernel available to non-datatype documents, in batch and
interactive sessions, without a legacy fallback. Empty-schema model
construction and refutation soundness are checked in
`Z3SortedProofTests.fst`. This is a bounded migration step: it does not
repair the legacy combined model or add concrete arithmetic/array semantics
to the typed kernel.

## Direct native Z3 integration (2026-10-16)

The executable now accepts **SMT-LIB only**:

```powershell
.\fstar\tools\build_ocaml_checker.ps1 -RunTests
'(declare-const p Bool)(assert p)(assert (not p))' |
  wsl -e bash -c '~/z3checker/checker --stats'
```

`checker [--stats] [--diagnostics] [--timeout-ms N] [input.smt2]` reads a file or
stdin, parses/solves using its linked Z3, marshals the original assertions
and proof directly into algebraic datatypes, and invokes the extracted
checker. No Python, JSON construction/parsing, subprocess solver, or
runtime F* invocation is used. The Python exporter, JSON parser/decoders,
compatibility CLI, exporter tests/harness, and generated F* proof snapshots
have been removed. Neither JSON input nor the former `--smt2` and
`--check-original-assertions` switches are supported.

| Component | Responsibility |
|---|---|
| `Z3Native.fsti` | Abstract native AST/sort handles and effectful foreign API declarations |
| `ocaml_runtime/Z3Native.ml` | Mechanical views over the official Z3 OCaml/C API, solver invocation, exact rational decoding, and native ownership |
| `Z3NativeProof.fst` | Operator tagging, direct algebraic AST construction, memoized worklist traversal, and original proof-parameter marshaling |
| `Z3ProofIndex.fst` | Shared persistent numeric caches and verified lookup/update property |
| `Z3ProofDocument.fst` | Transport-independent definition/scoping/input validation and topological checking through `Z3UnifiedProof` |
| `ocaml_runtime/Z3NativeMain.ml` | Direct CLI and optional phase/node statistics |

### Interactive certifying SMT-LIB session

`checker --interactive [--stats] [--diagnostics] [--timeout-ms N]` reads
SMT-LIB commands from stdin and evaluates each complete command through
`Z3_eval_smtlib2_string` on one persistent, proof-enabled context. Commands
may span lines or share a line. Framing respects comments, quoted symbols,
and SMT-LIB strings with doubled quotes. Responses are flushed after each
command, without waiting for EOF. `(exit)` ends the session; a file argument
other than `-` is not accepted in this mode.

```smt2
(declare-const p Bool)
(assert p)
(check-sat)
; sat
(check-sat-assuming ((not p)))
; unsat
; proof-check ACCEPT
(push)
(assert (not p))
(check-sat)
; unsat
; proof-check ACCEPT
(pop)
(check-sat)
; sat
(exit)
```

The runtime registers the extracted F* document checker with
`Z3_set_proof_check_callback`, using the official OCaml binding's native AST
and assertion-vector handles. Each UNSAT callback creates a fresh marshaling
state and runs the same document checker as batch mode. Caches do not span
checks, including after `pop` or `reset`. Named assertions include their
guarded formulas and tracking literals, as used in the proof premises.
`check-sat-using` is also checked; model and unsat-core queries remain available.

Solver replies remain ordinary SMT-LIB. The callback report is emitted as an
SMT-LIB comment: `; proof-check ACCEPT`, `; proof-check PARTIAL n`, or
`; proof-check REJECT`. **Only ACCEPT certifies an UNSAT proof under the
existing checker/trust assumptions.** A preceding `unsat` alone is still the
producer's answer. NLSAT assumptions and other unsupported leaves remain
explicit pending obligations, never successful certificates. SAT models are
not certified.

Each interactive proof check also emits a `; proof-stats` comment by default.
It reports unique proof-DAG nodes (`proof_nodes`), premise edges
(`proof_edges`), effective input assertions/assumptions (`assertions`),
unique marshaled expressions and declarations, pending obligations, and
solve/marshal/check milliseconds. Counts are per check, not cumulative.
`proof_nodes` and `proof_edges` count the outer document DAG.
`binder_nodes` and `binder_edges` separately count the checked DAGs hidden
inside proof binders, including each certificate's root. These counts are
per certificate; a certificate root also occurs in the outer DAG.
Rejected documents report `pending=unknown`, not a misleading zero.
`--stats` additionally writes the existing batch-compatible timing/size line
to stderr; `--diagnostics` continues to report typed obligations there.

Proof generation is enabled at startup and restored after `(reset)`, together
with the command-line timeout. An attempt to disable proof generation reports
an error and restores it before further commands. Ordinary command errors are
reported as SMT-LIB errors and the session continues; malformed or truncated
command framing and resource failures end the session with an error.

At EOF or `(exit)`, exit status is 2 if any command/checker error occurred,
otherwise 1 if any proof was rejected, otherwise 3 if any proof was partial,
otherwise 0. SAT and UNKNOWN are normal interactive answers and do not
themselves make the process fail. These session-wide statuses differ from
the single-solve batch statuses below.

The OCaml raw API exposes `set_proof_check_callback` returning an opaque
`proof_check_callback` registration and `clear_proof_check_callback`.
Callers must keep the registration alive while evaluating commands.
Replacement/clearing releases the old closure; collecting a registration
unregisters it if still current. This ownership avoids rooting cycles when
callbacks capture their context. Borrowed input handles are wrapped with
the usual OCaml native reference counting and may be retained after return.
The bridge catches callback exceptions, including input-wrapper allocation
failures, before unwinding the C++ stack, and re-raises them only after
`Z3_eval_smtlib2_string` returns. Registrations and contexts must not be used
concurrently across OCaml domains; recursive evaluation on the same context
from its callback is not supported.

The foreign implementation never constructs a checker AST or a checked
fact. F* code assigns recognized operator tags from actual native operator
kinds, not user-supplied printed names. Opaque declarations and nominal
sorts carry native identity in their names to avoid conflating overloaded
or parameterized symbols. Exact numerals and Z3's original `arith/farkas`
parameters are preserved. The additional unit-weight arithmetic candidate
described below is checked independently against the actual formulas; it
is not presented as an original native certificate.

NLSAT-origin theory lemmas carry the explicit native parameters
`arith assumed nlsat`. The foreign view preserves this origin, and the
typed marshaler records `Unverified "assumed:nlsat"` rather than silently
classifying it as a generic theory lemma. These nodes retain an obligation
and cannot establish an obligation-free `ACCEPT`.

The build also extracts the standalone ordered-ring replay kernel
`Z3NlaLemma`. It does **not** yet connect the serialized `arith nla`
certificates to native AST clauses. Such nodes remain unverified in this
document checker; see `NL_ARITH_REPORT.md` for the exact source-expansion
and clause-correspondence boundaries.

### Native LP Gomory cuts (2026-10-18)

`Z3LpGomory.fst` checks `arith/lp-gomory` using an integer split.
For an integer-valued term `t` and integer threshold `k`, either
`t <= k` or `t >= k + 1`. Both branches must independently imply the
actual conclusion, using the actual proof premises and the existing exact
Farkas checker. F* proves split exhaustiveness and the two-branch inference
under the existing numeric model; no additional semantic premise is added.

The native LP context supplies candidate terms, thresholds, and weights.
The generator handles lower/upper shifts, fixed columns, integral row
coefficients, fractional integer coefficients, continuous columns, and
the producer's denominator-clearing convention. Neither a row identity
nor the correspondence of a recorded bound or variable definition to its
AST is trusted: an incorrect candidate cannot bypass either branch check.
Malformed or unsupported candidates retain an explicit obligation.

Focused regressions cover both bound directions, negative shifts,
fractional coefficient selection, continuous columns, missing premises,
non-integer split terms, unchecked branches, changed conclusions, and
an authentic native Gomory proof. The previously pending cut in
`QF_LIA_092` is discharged: its seven obligations become six, all remaining
ones being `th-lemma`. The unchanged 710-input replay retains all
648 accepted proofs and 62 partial proofs, with identical proof-node
counts and no other changed pending counts. Frozen evidence is under
`C:\smtlib-benchmarks\proof_gomory_20261018\final`.

### QF_DT benchmark coverage (2026-10-18)

A fixed 100-input QF_DT sample comes from the SMT-LIB 2025 archive
([source](https://zenodo.org/records/15493090)), stratified with seed 42:
34 inputs from `20172804-Barrett`, 33 from `20210312-Bouvier`, and 33 from
`20230720-blocksworld`. The frozen manifest records archive and input
SHA-256 hashes. Both evaluations use eight workers, a 30-second solver
timeout, a 120-second end-to-end deadline, and a 4-GiB child address-space
limit.

The sample exposed a normalization gap: constructor injectivity generates
a conjunction of field equalities, but the old normalizer finished after
that single root rewrite. `Z3TheoryNormalize.normalize` now normalizes
changed root results recursively with strictly decreasing fuel. Its proof
composes the existing root-soundness lemma with the recursive
normalization lemma. This closes nested constructor disjointness and
injectivity without adding a datatype model assumption or trusting a
native rewrite verdict. Exhausted fuel still leaves the step unchecked.
Focused regressions include nested head/tail conflicts, nested
injectivity with symbolic fields, and an invalid nested equality.

| Outcome | Before | After |
|---|---:|---:|
| `ACCEPT` | 15 | 16 |
| `PARTIAL` | 18 | 18 |
| `SAT` | 21 | 21 |
| Solver `UNKNOWN` (timeout) | 46 | 45 |

`QF_DT_079` changes from four pending rewrites to `ACCEPT`; all previous
accepts are retained. Fifteen other original partial proofs have fewer
obligations. `QF_DT_071` changes from a solver timeout to `PARTIAL`, so
the unchanged total of partial proofs does not mean no proof completed.
Supplemental diagnostics remove all **878 rewrite obligations** from the
16 previously profiled partial proofs. The remaining 15 profiled partials
contain **2219 `th-lemma` obligations**, including constructor
reconstruction, recognizer propagation, and theory conflicts. This is not
complete datatype-theory certification: acyclicity, exhaustiveness, and
general selector/constructor reconstruction remain unsupported.
Diagnostic replays of `QF_DT_034`, `QF_DT_036`, and the newly partial
`QF_DT_071` exceed the end-to-end deadline and are excluded from these
diagnostic counts.

The full strict F*/Pulse, extraction, native bridge (38 groups), and CLI
(21 tests) pipeline passes. A separate unchanged 710-input replay retains
all **648 `ACCEPT` and 62 `PARTIAL`** results, with identical pending and
proof-node counts. Sample manifests, checker snapshots, raw outputs,
diagnostics, and SQLite audit records are frozen under
`C:\smtlib-benchmarks\proof_qf_dt_20261018`, in `baseline`, `normalized`,
`baseline-obligations`, `normalized-obligations`, and `retention`.

#### Constructor-equality propagation

A subsequent pass handles datatype theory consequences whose actual
premises identify an unknown term with a constructor. The checker orients
that equality toward the constructor, substitutes in the remaining facts
and conclusion, and retries normalization. For example,
`x = stack(a, tail)` together with `not (is-stack x)` now proves a
conflict; matching field selections and recognizers also propagate
through chains of constructor equalities.

F* proves that the selected equality follows from the supplied premises,
that substitution preserves evaluation, and that the bounded recursive
consequence check is sound. No new semantic assumption is introduced.
Substitution does not descend into binders: a premise true in the
current environment cannot be applied to a variable rebound by an inner
quantifier. Self-containing replacements are rejected, and propagation
is bounded to eight substitutions; unsupported cases remain obligations.
Regressions cover constructor conflicts, recognizers, selectors, chained
equalities, missing premises, incorrect/unmatched selectors, cyclic
equalities, and an adversarial nested-binder example with actual
de Bruijn variables.

On the same fixed 100-input sample, the result is now **17 `ACCEPT`,
16 `PARTIAL`, 21 `SAT`, and 46 solver `UNKNOWN`**. `QF_DT_093` changes
from one remaining obligation to `ACCEPT`, and all 16 previous accepts
are retained. `QF_DT_071` returns to a solver timeout; its earlier
timeout-to-partial change was not a certification improvement.
Across the previously profiled proofs, **1195 additional `th-lemma`
obligations are discharged**, reducing 2219 to 1024. The remaining 14
profiled partials contain only `th-lemma` obligations; diagnostic runs of
`QF_DT_034` and `QF_DT_036` still exceed the deadline.

The remaining cases include exhaustive recognizer splits and
recognizer-guarded constructor reconstruction. The current primitive
tag/field interpretation contracts do not establish that every typed
value has a constructor representation or that those projections
uniquely determine it. These cases therefore stay unverified rather than
being added as trusted rules. The strict verification/extraction/native
and CLI pipeline passes, and a fresh 710-input replay retains all 648
accepts and 62 partials with identical pending and proof-node counts.
Frozen evidence is in `propagated`, `propagated-obligations`, and
`propagated-retention` beside the earlier QF_DT results.

### Concrete sort-indexed datatype semantics

`Z3DatatypeValue.fst` provides the contextual kernel's concrete datatype carrier:
finite constructor trees refined by an explicit signature, constructor
arity, and the declared sort of every field. Non-datatype leaves use a
generic `sort -> Type0` carrier family; they are not restricted to the
legacy shared `value` representation. Mutually recursive datatype sorts
share the same tree representation and sorting predicate. A scalar
cannot masquerade as a datatype value.

Constructor disjointness and injectivity, exhaustive constructor
membership, recognizer-guarded reconstruction, and reconstruction from
the complete matching-selector tuple are proved from this representation.
A strict size decrease along every nonempty field path proves
acyclicity. These are derived properties, not additional datatype model
axioms. Selectors project matching constructor fields; on other
constructors they call an arbitrary total function of the entire input
value, preserving the SMT-LIB freedom to return different values on
different wrong-constructor arguments.

The module also supplies sort-indexed environments and an evaluator for
the existing expression AST, with a proof-checked result sort.
Quantifiers receive only correctly sorted bound-value tuples, in
reversed declaration order for de Bruijn indexing. Their actual truth
interpretation remains a supplied parameter; this development does not
construct a combined quantifier, arithmetic, or array model.

`Z3DatatypeSignature.fst` checks constructor ownership and identity,
tester signatures, accessor order and field sorts, distinct constructors,
and productivity. An executable finite witness search establishes
nonempty carriers for accepted schemas when the base carriers are
nonempty. Nested datatype fields beneath array sorts are rejected;
the native adapter also rejects datatype-containing sequence fields,
which the shared sort syntax cannot represent structurally.
Non-datatype result sorts, including arrays whose domains or ranges
contain datatypes, retain abstract scalar carriers. This distinction
keeps the total interpretation inhabited without claiming array laws or
accepting unsupported nested datatype constructor fields.
`Z3Native.view_datatypes` collects every constructor, tester, and accessor
of reachable native datatype sorts, including mutually recursive and
otherwise unreferenced constructor alternatives. The extracted schema
validator checks this metadata; the foreign API's completeness and
identity correspondence remain part of the native trust boundary.

The checked schema builds a typed interpretation with canonical
constructor, recognizer, and selector application dispatch. Recognizer
results use an explicit Boolean-carrier isomorphism, which has a concrete
witness for the primitive Boolean carrier. Other operations, quantifier
interpretations, and wrong-constructor selector results are supplied by
the surrounding interpretation.

**Production integration:** `Z3SortedSemantics.fst` supplies canonical
Boolean operations, polymorphic equality and conditionals over the typed
carrier. Scalar equality is supplied with a correctness proof; recursive
datatype equality is derived. `Z3SortedDatatype.fst` derives constructor
rewrites, exhaustive recognizer splits, and recognizer-guarded selector
reconstruction from the actual checked schema. Equality commutativity,
constant-branch conditionals, direct modus ponens, and literal resolution
also have proofs in this interpretation. Bounded Boolean reflection
preserves shared expression boundaries instead of expanding every nested
conditional. Constructor-equality propagation uses the derived laws,
not assumed legacy datatype axioms.

`Z3SortedProof.fst` checks raw proof DAGs against their **original
assertions** using topological premise lookup, checked declaration
membership, closed well-sorted facts, hypothesis inheritance/discharge,
and explicit pending counts. Its `lemma_check_document` proves that a
zero-obligation result rules out any typed interpretation satisfying the
original assertions. A concrete total interpretation witness ensures
that the interpretation type itself is inhabited; the theorem does not
assume the legacy `model_sound` or global all-environments contracts.
The diagnostic checker is proved to agree with the acceptance checker.
The cache invariant includes context validity as well as truth: checked
premises and their hypothesis lists need not be revalidated at every
successor. `lemma_check_node_context` proves context preservation, and
the empty-cache induction establishes the invariant from the original
document. The standalone node-checking wrapper still validates supplied
premises. Hypothesis discharge checks canonical negations and handles
both clause literals and the complement of the whole conclusion.

The native CLI selects this kernel whenever marshaling finds datatype
metadata. It never falls back to the legacy checker on this path.
Documents without datatypes retain the existing unified checker.
This is not a migration of every theory: arithmetic, arrays, bit-vectors,
and quantifier truth remain abstract unless handled by the typed core.
Definition expansion, Skolemization, and quantifier-specific proof
semantics are not imported from the legacy model; unsupported steps
remain obligations. The native API's correspondence to checked metadata
and original assertions remains in the foreign trust boundary.

The strict F*/Pulse, OCaml extraction, native bridge (40 groups), and CLI
(23 tests) checks pass. Regressions include heterogeneous fields,
mutual recursion, nonproductive or malformed schemas, matching and
argument-dependent wrong-constructor selectors, canonical native
dispatch, typed AST evaluation, quantifier binding order, and invalid
accessor indices and recognizer result sorts. Contextual proof regressions
certify native exhaustiveness, reconstruction, injectivity, and
disjointness, conditional branches, and equality symmetry, while rejecting
missing original inputs, open roots,
incomplete referenced signatures, and fabricated contradiction leaves.
Formal regressions also cover shared formulas beyond the truth-table
atom bound, wrong resolution units, and spoofed negations.
CLI regressions exercise both batch and interactive contextual checking,
and require mixed datatype/arithmetic proofs to retain obligations
rather than falling back to the legacy arithmetic contracts.

The frozen 100-input QF_DT replay uses the existing manifests and driver,
eight workers, a 30-second producer timeout, a 120-second end-to-end
deadline, and a 4-GiB address-space limit:

| Checker | ACCEPT | PARTIAL | SAT | UNKNOWN | Wall deadline |
|---|---:|---:|---:|---:|---:|
| Previous legacy route | 17 | 16 | 21 | 46 | 0 |
| Contextual typed route | 20 | 13 | 21 | 45 | 1 |

All 17 previously accepted inputs remain accepted. `QF_DT_082`,
`QF_DT_090`, and `QF_DT_096` now certify, and every input partial in both
runs has fewer obligations. `QF_DT_071`, previously a producer timeout,
hits the external end-to-end deadline in the new run; this is not a
checked result. The separate 710-input retention replay remains
648 accepts and 62 partials, with identical status, pending count, and
proof-node count for every input.

This is not a performance-neutral migration. For example, the
66,106-node `QF_DT_076` checks in 3.30 seconds versus 1.14 seconds on the
legacy route; the 953,813-node `QF_DT_036` takes 60.79 versus 56.95 seconds.
These are frozen-run observations, not controlled microbenchmarks.
The typed route initially exceeded several wall deadlines; direct
inference checks and the proved context-cache invariant removed those
regressions on previously partial inputs. The complete QF_DT batch took
261.72 seconds versus 231.73 seconds for the earlier run. Evidence,
binary hashes, input hashes, raw diagnostics, and benchmark database
entries are frozen under
`C:\smtlib-benchmarks\proof_qf_dt_20261018\contextual-v4`;
the non-datatype retention evidence is in `contextual-v3-retention`.
The strict final toolchain log is
`build_extract\sorted-contextual-symmetry-toolchain.log`.

### Binder and quantifier proof support

Native `proof-bind` nodes contain a lambda whose body is a **proof**, not an
ordinary formula. The foreign view exposes its bound sorts and original
body proof. `Z3NativeProof.fst` traverses that hidden proof DAG with a
memoized worklist and constructs a typed binder certificate; it does not
marshal proof-valued lambdas as object-language assertions.

The unified kernel checks every certificate entry against already checked
premises. Its soundness invariant is validity under **every environment**,
not merely the current environment. Supported steps establish this
invariant from checked premises. A closed asserted formula may also be
used if it exactly matches an original input judgment: the existing
closed-expression theorem makes its truth independent of the environment.
Open or unrelated assertions, hypotheses, assumed theory lemmas, unknown
rules, and unsupported rewrites cannot be generalized.
Quantifier introduction requires matching quantifier kinds, matching bound
sorts, and an actual checked relation between the two bodies. This covers
`forall`, `exists`, and term-valued `lambda` congruence, including nested
binders and observational equality. The congruence-shaped `nnf-pos` case
uses the same checks. Negative NNF and compositional Boolean NNF are
checked as described below. A failed certificate leaves an explicit obligation
on its outer proof step; it never becomes `ACCEPT`.

`Z3BinderSubstitution.fst` supplies capture-avoiding simultaneous
substitution beneath quantifiers and lambdas. Its environment theorem also
supports arbitrary unused-binder thinning: retained variables are
reindexed, ambient variables shift down, and nested binder cutoffs are
respected. `elim-unused` no longer only handles constant Boolean bodies.
Removing every binding reduces a Boolean quantifier to its body; lambda
argument lists are not thinned, since that would change the array sort.

`Z3QuantifierInstantiation.fst` checks native `quant-inst` clauses using
Z3's original AST-valued substitution parameters. It validates binding
arity, sorts, closed arguments, de Bruijn order, and the exact resulting
body. Its substitution theorem covers nested `forall`, `exists`, and
`lambda` bodies using the shared `Z3BinderSubstitution.fst` foundation.
Binder-aware lifting preserves inner bound variables and prevents capture
of the outer substitution arguments. Supplied arguments must still be closed.
Multi-variable, mixed-sort instantiations are supported.

The targeted 2026-10-18 replay discharges all **58 formerly unchecked
`quant-inst` steps across 34 proofs**, with unchanged proof-node counts.
Their total remaining obligations decrease from 312 to 254. These proofs
remain partial because of other rule families; all 540 previously accepted
proofs remain accepted. The 574-input replay uses eight workers, a
30-second solver timeout, a 120-second process watchdog, and 4 GiB per child.
All 34 diagnostic replays reproduce the new pending counts exactly.
Frozen results and comparisons are under
`C:\smtlib-benchmarks\proof_quant_inst_20261018`.

The semantic model premises now explicitly include quantifier
extensionality, preservation of constant Boolean bodies, universal
quantifier elimination, and Boolean quantifier truth semantics, in addition
to the existing universal-introduction premise. F* verifies certificate
traversal, congruence lifting, substitution, quantifier duality, and the
integrated node soundness theorems under these premises. These are
not an unconditional theorem connecting native SMT-LIB quantification to
the abstract interpretation.

Native and interactive regressions cover arithmetic and Boolean rewrites
under binders, nested mixed-sort quantifiers, lambda congruence, and genuine
quantifier instances. Mutations exercise invalid premise/root indices,
missing or reordered bindings, escaping variables, incorrect instances,
bound-sort mismatches, and attempted generalization of open/unrelated
assertions or hypothetical leaves. The pinned 17-file `regressions/proofs` corpus retains
16 `ACCEPT` results and one solver `UNKNOWN` at the 10-second timeout.

Remaining quantifier-related limits include Skolemization outside the
fresh, acyclic, variable-dependency fragment described below,
pulling outside the supported Boolean fragment, instantiation with open
substitution arguments, and transformations exceeding the bounded
normalization budgets. The abstract quantifier
semantics still ranges over arity-correct value lists rather than verified
sort-indexed SMT-LIB domains. NLSAT and other previously unsupported theory
rules remain partial.

#### Destructive equality resolution and input-aware binders (2026-10-18)

`Z3QuantifierDer.fst` certifies `der` using guarded variable elimination,
including the following schemas and their symmetric equality orientations:

```text
exists x. (x = t and P(x)) = P(t)
forall x. (x != t or P(x)) = P(t)
```

The witness must have the eliminated variable's sort and must not contain
that variable. A verified lowering operation checks the occurs condition
and adjusts remaining de Bruijn indices. Substitution lifts the witness
beneath nested binders and preserves their local variables. Other variables
in the same binding block and ambient dependencies are retained. The
Boolean checker verifies the guard's semantic role rather than accepting
an equality anywhere in the body. Boolean literal guards, partial binding
block elimination, and nested congruence are supported. The proof derives
elimination by inserting/removing assignments under the existing
quantifier semantics; no new axiom or model premise is added.
Unsupported shapes or exhausted 64-step fuel remain obligations.

Inspection of hidden certificates identified 316 first-failing asserted
leaves that were both closed and exact original inputs. Input-aware
binder checking now admits those facts with a proof of environment
independence, while rejecting missing, open, or unrelated assertions.
Definition expansion also applies to every hidden certificate formula,
not just its parent conclusion and the original inputs. Failed expansion
rejects; an expanded certificate still has to pass all ordinary checks.
This fixes two otherwise checked negative-NNF certificates whose roots
previously differed from their definition-expanded parent conclusions.

A frozen 710-input replay covers all 540 previous accepts and the 170
remaining partials. It yields **563 `ACCEPT` and 147 `PARTIAL`**, retaining
all 540 accepts and gaining 23, with unchanged outer proof-DAG sizes.
No `quant-intro`, `der`, or `quant-inst` obligations remain in this cohort.
All 147 supplemental diagnostic runs reproduce the primary pending counts.
The replay uses eight workers, a 30-second solver timeout, a 120-second
process watchdog, and 4 GiB per child; batch elapsed time was 225.6 seconds.
Frozen binaries, source hashes, outcomes, comparisons, diagnostics, and
SQLite audit records are under
`C:\smtlib-benchmarks\proof_quantifier_rules_20261018`.

Strict installed-Z3 F*/Pulse verification and extraction pass, together
with 31 native bridge groups and 20 CLI tests. Focused regressions cover
mixed-sort elimination, open dependent witnesses, nested binders, Boolean
guards, reversed equalities, cyclic witnesses, wrong polarity, captured
variables, incorrect instances, input binding, and definition expansion.

At this stage, diagnostics reported 117 outer `sk` obligations across 68
proofs, 38 `nnf-neg` across 35 proofs, and 49 `nnf-pos` across 39 proofs.
Those obligations are discharged by the subsequent extension below.

#### Hilbert-choice Skolemization (2026-10-18)

`Z3Skolemization.fst` represents a block's Skolem functions by coordinates
of **one joint choice tuple**, parameterized by the free-variable values:

```text
tuple(y) = epsilon xs. P(xs, y)
sk_j(y) = tuple(y)[j]
```

The `hilbert_choice` semantic parameter supplies a tuple of the required
length and satisfies Hilbert's law: if any tuple satisfies the predicate,
the selected tuple does too. Negative universal Skolemization chooses a
counterexample tuple, using `not P` as the predicate. All coordinates use
the same tuple, which is essential for constraints relating multiple bound
variables; independently chosen coordinates would be unsound.
Choice is not evaluated by the native checker, and no individual `sk`
conclusion is assumed as an axiom.

The executable infers the native substitution from the original ASTs and
requires an exact capture-safe instance. It checks binding order and sorts,
consistent repeated occurrences, distinct fresh component symbols, and
one shared variable-dependency vector covering all free variables.
Sparse ambient indices, unused variables in a binding block, mixed sorts,
and substitution beneath nested binders are supported. Negative universal
endpoints include the native double-negation simplification.
The dedicated rule accepts observational judgments only, not ordinary
equality, and rejects unexpected premises.

The document checker collects choice definitions from both outer proof
steps and hidden binder DAGs after ordinary definition expansion. Identical
reuse is allowed; incompatible definitions sharing a symbol are rejected.
It orders the definitions by dependency, rejects cycles and self-reference,
and checks freshness against both original and expanded inputs.
`skolem-collection`, `skolem-cycle`, and `skolem-freshness` diagnostics
identify these failures. Unrecognized Skolem shapes remain obligations.

F* proves that successive choice interpretation extensions preserve earlier
witness properties and original-input evaluations. Interpreted-operation
and quantifier fields are unchanged. The extended binder invariant still
holds in every environment, now in the globally chosen interpretation.
`lemma_choice_obligation_free_node_sound` derives the choice-context
contract from this construction before applying the unified node theorem.
This is not a claim that Skolemization preserves arbitrary same-model
equalities: `exists x:Int. x = 0` is true while `sk = 0` is false when
`sk = 1`; the fresh symbol's interpretation must be chosen appropriately.

**Formal boundary:** Hilbert choice is an explicit semantic parameter.
The node theorem also retains `model_sound` for the constructed
interpretation. The construction does not prove closure of every legacy
model predicate under interpretation extension or repair the documented
semantic-model contract inhabitance gap. These are conditional semantic
theorems, not an unconditional end-to-end SMT-LIB soundness result.

Dependent NNF certificates also need both polarities of a premise. For
example, positive existential replacement may use `P(sk(y), y)` while the
negative occurrence uses `forall xs. not P(xs, y)`. Forward replacement
alone can lose that relationship. The Boolean NNF checker now also tries
replacing target subexpressions with reversed checked premise relations.
F* proves symmetry and replacement soundness without strengthening an
observational premise to equality. The existing Boolean budgets are
unchanged. After integration with the shared quantifier checker,
replacement may descend beneath quantifiers using the all-environments
premise invariant, as described below.

The final frozen 710-input replay yields **648 `ACCEPT` and 62 `PARTIAL`**,
retaining all 563 prior accepts and gaining **85**, with unchanged outer
proof-DAG sizes. All 117 outer `sk`, 49 `nnf-pos`, and 38 `nnf-neg`
obligations from the preceding baseline disappear. No `quant-intro`,
`der`, or `quant-inst` obligations remain either. All 62 supplemental
diagnostic runs reproduce the primary pending counts. Remaining leaves
are 5,018 theory lemmas across 58 proofs, six rewrites across six proofs,
and one LP Gomory step. These proof sets overlap.
Eight workers, a 30-second solver timeout, a 120-second process watchdog,
and 4 GiB per child give 220.8 seconds of batch elapsed time.
Frozen binaries, source hashes, comparisons, diagnostic outputs, and
SQLite audit records are under
`C:\smtlib-benchmarks\proof_skolem_choice_20261018`.

Strict installed-Z3 F*/Pulse verification and extraction pass with
32 native bridge groups and 20 CLI tests. Focused regressions cover joint
and mixed-sort witnesses, sparse dependencies, unused bound variables,
nested capture avoidance, negative universal normalization, actual native
Skolem proofs, signed NNF composition, missing premises/dependencies,
inconsistent occurrences, aliased components, input freshness,
self-reference, conflicting definitions, cycles, acyclic reordering,
wrong polarity, and attempted conversion to ordinary equality.

#### Negative NNF checking and evaluation

`Z3QuantifierNnf.fst` defines universal truth and classical existential
truth over the abstract bound-value environments. From these semantics and
Boolean negation, it proves both quantifier dualities:

```text
not (forall xs. body) = exists xs. not body
not (exists xs. body) = forall xs. not body
```

The executable does not assume an individual `nnf-neg` step. It checks
the flipped quantifier kind, unchanged bound sorts, and the supplied
all-environments proof of the negated body relation. Verified Boolean
equivalence handles normalized endpoints, including double-negation
elimination in Z3's XOR-body proofs. Observational premises remain
observational and cannot establish an ordinary equality.

Boolean `nnf-pos` and `nnf-neg` steps compose their checked premise
relations through application arguments and nested quantifier bodies,
including negative occurrences. Descending through a binder is justified
only because every supplied fact already holds under **every environment**;
hypotheses are never generalized. Endpoint comparison combines Boolean
equivalence, unused-binder elimination, quantifier pulling, and the
compositional normalization described below. Direct quantified NNF steps
still require their explicit binder metadata and checked body premise.
Boolean comparison also tries reversed-premise replacement on the target,
as described in the Skolemization extension.
Unsupported steps or exhausted budgets retain obligations.

The 2026-10-17 local evaluation used eight native negative-NNF examples:
plain existential negation, conjunction, disjunction, a Boolean context,
mixed-sort bindings, implication, XOR, and ITE bodies. All eight returned
`ACCEPT` in batch and interactive mode. A single timed batch evaluation
took 539 ms of process wall time in total; the kernel checks summed to
1.121 ms, with median kernel time 0.131 ms. These are illustrative local
measurements, not a performance guarantee.

All F*/Pulse verification succeeded with warnings treated as errors;
26 native bridge test groups and 20 CLI tests passed. Native mutations
cover wrong polarity/kinds/sorts, missing binders or premises, invalid
body certificates, hypothesis generalization, and illicit conversion
from observational relations to ordinary equality. Synthetic certificates
exercise both dualities and positive/negative Boolean composition.
The pinned z3test proof corpus remains 16 `ACCEPT` and one solver
`UNKNOWN` at 10 seconds, with no checker errors. The nested-existential
example that was then `PARTIAL` solely for `pull-quant` is certified by
the subsequent implementation below.

#### Quantifier pulling

`Z3QuantifierPull.fst` verifies `pull-quant` by normalizing both endpoints
and comparing the resulting expressions. Supported transformations are
adjacent same-kind `forall`/`exists` flattening, quantifier negation, and
pulling quantifiers through n-ary `and`/`or`. Multiple quantified operands
are pulled right-to-left, matching native binder-block order without
reversing declaration order within a block. Flattening retains the exact
concatenated sort vector and body.

The semantic proof derives flattening from the existing Boolean quantifier
truth model, list splitting, and composition of de Bruijn environments.
Boolean pulling uses a structural proof of the existing
`Z3Definitions.lift`, including adjusted cutoffs beneath nested quantifiers
and lambdas. Thus sibling expressions retain their ambient dependencies
without capturing newly bound variables. Quantifier negation reuses the
proved duality. No individual pulling step is assumed as an axiom, and no
additional semantic model premise is introduced.

The dedicated unified rule is also available inside hidden binder
certificates, where it must hold in every environment. Unsupported shapes
and normalization exceeding the 64-step recursion budget leave explicit
obligations; unexpected premises are rejected. `Z3QuantifierReduce.fst`
additionally compares normalized binder bodies and removes unused
bindings. The unified rule can use compositional normalization to handle
pulling nested inside applications and negative Boolean contexts.
Pulling through implication, XOR, or ITE is not implemented as a general
rule. Lambda rewriting and nested instantiation use separate checkers.

The four native nested-quantifier examples (existential, universal,
mixed-sort, and three binder blocks) all return `ACCEPT` in batch and
interactive mode. The former nested-existential `PARTIAL` target is among
them. A local timed batch run took 253 ms in total, with 0.367 ms summed
kernel checking and 0.081 ms median kernel checking. These are illustrative
local measurements, not performance guarantees.

F*/Pulse verification and extraction pass with warnings treated as errors;
27 native bridge groups and 20 CLI tests pass. Synthetic cases additionally
cover all four connective/quantifier combinations, multiple multi-variable
mixed-sort blocks, open ambient variables, nested sibling lambdas, and
mixed-kind quantifiers without merging them. Adversarial cases cover
changed kinds/sorts, swapped variables or binder blocks, captured or dropped
dependencies, altered bodies, forward/missing or unexpected premises, and
exhausted normalization fuel. The pinned 17-file proof corpus remains
16 `ACCEPT` and one solver `UNKNOWN` at 10 seconds, with no checker errors.

#### Distribution, destructive equality, and lambda rewriting

`Z3QuantifierReduce.fst` checks `push-quant` in the two valid distribution
directions: `forall` over conjunction and `exists` over disjunction.
Each distributed body is compared after unused-variable elimination and
binder-aware normalization. The opposite distribution directions are not
accepted.

`Z3DestructiveEquality.fst` replays `der` one definition at a time.
Universal disjunctions use a disequality guard; existential conjunctions
use an equality guard. Both equality orientations and Boolean
literal/equality forms are supported. Conjunctions/disjunctions are
flattened with the existing verified connective lemmas. Each step checks
the binding range, sorts, and occurs condition, substitutes without
capture, and removes its defining literal. Dependent definitions can be
replayed in sequence; cyclic/self-referential substitutions do not bypass
the occurs check. The intermediate binder vector is retained, matching
the producer, and final comparison can remove unused bindings.

`Z3LambdaRewrite.fst` checks lambda extensionality, constant-array/lambda
equalities, lambda-to-constant-array views, and beta reduction for typed
single- or multi-index selection. Ambient terms are lifted beneath the
new binder; beta substitution reverses declaration order and remains
capture-safe beneath nested binders. Selecting a constant array uses the
same proved lambda view.

These rules are semantic checkers, not endorsements of the native proof
tag. Unsupported instances remain obligations. Lambda support introduces
an explicit `lambda_model` contract: lambda denotation equality reflects
pointwise body equality, selecting a lambda evaluates its body, and a
constant array denotes the corresponding constant lambda. These are
primitive interpretation assumptions, **not** a proved concrete native
array/function model or an assumption that an individual rewrite is valid.

### Additional theory lemmas and definition axioms

`Z3TheoryNormalize.fst` performs bounded, bottom-up normalization with
proved local rewrites and congruence, including beneath binders. It is
shared by ordinary rewrites, NNF/pulling endpoint comparisons,
`def-axiom`, and generic `th-lemma` checking. For theory lemmas with
premises, it checks the implication from the actual premise propositions
to the conclusion, not the conclusion alone. The existing propositional,
distinctness, guarded-definition, and array/arithmetic checks remain
available. The same independently checked consequences are available in
hidden binder certificates when all their premises satisfy the
all-environments invariant; assumed-origin leaves remain excluded.

| Theory | Additional integrated coverage |
|---|---|
| Arithmetic | Independently checked unit-weight Farkas candidates, reflexive/constant linear constraints, and arithmetic normalization inside clauses and definitions. Existing exact native coefficient checks remain unchanged. |
| Arrays | Existing read/store contraction, overwrite/redundancy, and guarded read-over-write rewrites inside larger clauses and definitions; constant-array reads use the lambda view. The pre-existing array model remains specialized to its documented sorts. |
| Bit-vectors | Exact native numeral values and widths; unary `bvnot`/`bvneg`, binary bitwise/modular arithmetic constant folding, idempotence, self-cancellation, selected neutral/absorbing elements, and double negation. |
| Datatypes | Constructor disjointness/injectivity, matching/mismatching recognizers, and matching-constructor field selection inside clauses, implications, and definition axioms. |

Bit-vector recognition uses native operator kinds and numeric width/value
parameters. The semantic bridge uses a width-indexed numeric projection
with primitive modular/bitwise interpretation and equality-reflection
contracts. It currently requires closed terms and widths from 1 through
4096; it does not impose bit-vector typing on arbitrary bound-variable
environments. This does not enlarge the shared `value` datatype into a
concrete arbitrary-width native bit-vector interpretation. General
bit-blasting certificates, extracts/extensions/shifts, and unsupported
arithmetic rewrites remain obligations.

Datatype metadata records the owning sort, constructor identity, arity,
and field index using the official declaration/datatype APIs. Names alone
never identify constructors, testers, or accessors. Its semantic bridge
assumes primitive tag/field projections for constructor, recognizer, and
accessor interpretation; constructor equality laws are then derived.
Datatype acyclicity, exhaustiveness, update-field, and unmatched
selector/constructor schemas are not generically certified.

No rule is discharged solely because its hint says `th-lemma` or
`def-axiom`. Assumed NLSAT evidence, unsupported nonlinear replay, and
other unimplemented theory instances still retain explicit obligations.
The overall theorem remains conditional on the documented interpretation
contracts and trust boundaries, including the existing semantic-model
inhabitance gap.

The integrated verification/extraction passes with warnings treated as
errors. The merged native suite has 37 groups, including contextual Boolean
rewrites, unused-quantifier rewrites, positive and adversarial
quantifier/DER/lambda/Skolem cases, nested NNF replacement, theory consequences,
lookalike uninterpreted names, and malformed bit-vector widths. All 21 CLI
tests pass, including 11 new examples in both batch and interactive modes.
The pinned 17-file corpus still gives 16 `ACCEPT` and one solver `UNKNOWN`
at 10 seconds.

The 2026-10-18 integration with Hilbert-choice Skolemization retains both
guarded DER checkers and the forward/reversed Boolean NNF paths alongside
shared quantifier/theory normalization. Reversed-premise replacement
preserves the all-environments invariant even beneath nested binders.
The merged 710-input replay retains all **648 `ACCEPT` and 62 `PARTIAL`**
results, with no increased pending counts or changed proof-node counts.
Its frozen replay and comparison are under
`C:\smtlib-benchmarks\proof_skolem_merge_20261018\final`.
The rebuilt Z3 unit suite passes all 116 tests; solver, Python-binding,
and command-line-help smoke checks also pass.

The subsequent assertion-indexing/profiling merge threads the same Skolem
context and original input judgments through both linear and indexed
checking, including definition-expanded hidden binder certificates.
F* verifies equality of indexed and linear document-checking results
with these contexts. Production and opt-in instrumented builds both pass
all 37 bridge groups and 21 CLI tests; profile accounting and exception
handling also pass. The production replay again retains all 648 accepts
and 62 partials without increased pending counts or changed proof-node
counts. Frozen evidence is under
`C:\smtlib-benchmarks\proof_skolem_merge_20261018\profiling-merge`.

### Sharing and ownership

One conversion state is created per solve/context. Expression caches are
keyed by native AST ID, sorts by native sort ID, declarations by native
declaration ID **and application arity**, and proofs by native proof ID.
Each expression is constructed once and reused by physical reference,
including sharing between original assertions and proof conclusions.
Native owners are retained while these caches exist: otherwise Z3 could
collect a native object and recycle its numeric ID. Caches never span
independent contexts.

Explicit worklists process dependencies before parents, avoiding recursive
unfolding of expression/proof DAGs. Proof entries retain premise indices;
the checker caches each checked fact rather than rechecking shared
premises. Definition expansion is still a separate checked transformation.
Kernel equality/rewriting can inspect recursive expression contents;
this change is not a constant-time-identity optimization of every kernel
operation.

### Profiling and checked fast paths (2026-10-18)

The native entry point now uses `check_document_indexed` and
`diagnose_document_indexed`. `Z3ProofSet.fst` builds a tail-recursive,
persistent hash-bucket index of the expanded input judgments. Every
bucket lookup still checks structural membership: hash collisions never
establish equality. The membership theorem holds for every pure
`judgment -> nat` hash, including a constant hash. The native adapter uses
OCaml's bounded `Hashtbl.hash`; no new semantic or per-proof axiom is
introduced. `lemma_check_document_indexed` proves equality with the
linear document checker, including rejection and pending-obligation
counts. The original standalone interfaces remain available.

Index construction is skipped when there are at most 16 inputs or at
most 16 asserted proof entries. This avoids paying setup costs for a
small proof using only a few of a larger assertion set. The index belongs
to one document and is never reused across contexts.

Congruence checking first tries matching non-reflexive argument pairs
against premises in order. A successful ordered match implies the
original arbitrary-premise match; unsuccessful attempts retain that
original fallback. `lemma_fast_arguments_match` proves exact Boolean
equivalence, so reordered premises and previously supported proof shapes
remain accepted. This removes repeated scans and temporary edge-pair
allocation on wide producer congruences.

Three alternating before/after runs against baseline `434601e51`, using
uninstrumented binaries on the same inputs, gave these median kernel
`check_ms` measurements:

| Input | Proof nodes | Before | After | Speedup |
|---|---:|---:|---:|---:|
| Generated 1,500-literal clause and negated units | 3,008 | 81.529 ms | 11.294 ms | 7.22x |
| Generated 6,000-literal clause and negated units | 12,008 | 1,226.374 ms | 46.470 ms | 26.39x |
| Generated 800-link UF equality chain | 3,211 | 13.969 ms | 7.290 ms | 1.92x |
| Generated 3,200-link UF equality chain | 12,811 | 164.353 ms | 33.511 ms | 4.90x |
| Generated 500-link real inequality chain | 1,507 | 23.672 ms | 20.386 ms | 1.16x |
| Generated 2,000-link real inequality chain | 6,007 | 285.217 ms | 221.167 ms | 1.29x |
| Pinned z3test `regressions/smt2/3209.smt2` | 16 | 0.211 ms | 0.218 ms | approximately unchanged |

These exclude solving, marshaling, and process startup. All verdicts and
proof-node counts matched; five other pinned public regression inputs
were SAT in both binaries and are not checker-speed measurements. The
public inputs use z3test commit
`b8d11d8edb5ebf7d8693fc58b875c6f90720c6c9`. The generated workloads are
scaling probes, not a substitute for the previously archived SMT-LIB
certificates, which were unavailable on this host. Raw per-run timings,
input/binary hashes, and profiles are retained as session artifacts.
An instrumented allocation comparison on the 1,500-literal probe reduced
checking allocation from about 100.0 MB to 11.4 MB; its congruence node
dropped from 90.2 MB to 0.217 MB. These are cumulative allocation samples,
not peak-memory measurements. After the changes, marshaling dominates
the UF/Boolean probes, while polynomial/Farkas checking dominates the
larger real-arithmetic probe.

For function/rule profiling, add `-ProfileChecker` to the build command
and select a separate `-WslBuildDir`, then run that executable with
`Z3_FSTAR_PROFILE=1`. Only this optional build instruments the copied
extracted OCaml sources; normal builds do not link the profiling runtime.
It emits stderr lines starting with `profile` and a JSON object recording
the rule/function name, call count, inclusive and exclusive milliseconds,
and allocated bytes. Selected recursive functions also report visit
counts. Counters accumulate per process. Allocation is cumulative, not
peak resident memory; time/allocation include instrumentation overhead,
so these profiles locate hot paths rather than establish speedups.
Without the environment variable the profiling build remains silent.

Formal verification/extraction and the 34 native bridge groups and 21 CLI
tests pass. New mutations cover constant/large hashes, colliding keys,
duplicate and missing assertions, unchanged pending obligations and
diagnostics, reordered congruence premises, and missing/reversed
argument evidence. Profiling-runtime tests check nested accounting,
return values, exception propagation, and JSON escaping.
The 23 targeted rule/pulling/negative-NNF examples still all `ACCEPT`.
The pinned 17-file corpus remains 16 `ACCEPT` and one solver `UNKNOWN`
(`lra_lassoranker.smt2` at 10 seconds), with no partials or errors.

### Definition-expansion memory diagnostics (2026-10-18)

The first complete local replay of the published 225-input sample retained
all stdout/stderr and classified 131 `ACCEPT`, 48 `PARTIAL`, 33 `UNKNOWN`,
10 `TIMEOUT`, one `ERROR`, and two `CRASH`. The failures were reproduced
under the same 4 GiB address-space limit with phase logs, GNU time resource
measurements, and GDB backtraces.

The two allocation aborts, on QF_AUFLIA `dlx-regfile.smt2` and QF_IDL
`ckt_PROP1_tf_10.smt2`, occur after solving and marshaling: recursive
definition expansion duplicates shared expression DAGs into trees.
`Z3Definitions` now provides a memoized expander whose F* refinement proves
the exact result of the original expander, including insufficient fuel
and failed substitutions. Buckets check the complete source expression
and fuel; hashing only selects a bucket. Each invocation fixes its
definition context and starts with a fresh cache. A proved unchanged
witness permits reuse of original expressions and argument lists without
another recursive comparison. Production indexed checking and diagnostics
use this expander while the linear APIs remain reference implementations.

The native hash classifier inspects up to 64 meaningful objects with a
256-node budget, so common connective declarations do not hide their
different arguments. An initial implementation using OCaml's default
hash budget made `plan-21.cvc.smt2` slower: profiling recorded
702,447,479 bucket probes for 7,121,508 expansion visits. With the larger
budget its kernel time is 19.4 seconds, versus 79.4 seconds with the initial
cache and 28.8 seconds in the reference executable, with the same 57,797
proof nodes. Native tests exercise the actual CLI classifier, including
diversity below a shared connective, by linking its support module without
the command-line entry point. Exact collision checks remain mandatory.

The handwritten OCaml `Prims` equality implementation also uses zero
total comparison instead of polymorphic equality. Total comparison skips
physically shared subtrees inside distinct wrappers, whereas polymorphic
equality repeatedly unfolds them. These operations agree on the closed
algebraic values, strings, and exact integers used by extracted checker
equality types; OCaml floats and functional values are not in that domain.
This implementation remains part of the existing runtime trust boundary,
not an additional F* hashing or equality axiom.

Normal and profiling builds verify/extract successfully, pass 35 native
bridge groups and 21 CLI tests, and retain profiling accounting tests.
Adversarial tests cover constant and colliding hashes, fuel-key separation,
cycles, malformed substitutions, capture avoidance, and 30-level shared
DAGs with unchanged and substituted leaves. The profiling build instruments
39 functions, including the production expansion/preparation paths.

With a separate 90-second diagnostic budget, the initial sharing-preserving
build completes `dlx-regfile.smt2` as `PARTIAL 6` in 70.7 seconds with
409,392 KiB peak RSS, versus the original abort near 3.7 GiB of resident
memory. `ckt_PROP1_tf_10.smt2` reaches the watchdog without an allocation
abort; GDB samples locate remaining CPU work in Boolean cutting and
normal-form specialization. This diagnostic does not establish completion
within the workflow's unchanged 60-second case budget.

The third failure, QF_IDL `PO4-10-PO4.smt2`, is separate and remains an
explicit out-of-memory error. Its backtrace enters `bool_rewriter` while
`Z3_solver_assert` eagerly rewrites the input, before `solver_check` starts
applying its 10-second timeout. It is not an extracted-kernel allocation
failure, and this change neither hides it nor changes the input assertion
basis or solver parameters.

The final replay attempts all 225 identical inputs under the original
budgets: **137 `ACCEPT`, 48 `PARTIAL`, 33 `UNKNOWN`, six `TIMEOUT`, one
`ERROR`, and no `CRASH`, `REJECT`, protocol errors, or unattempted inputs**.
Six former timeouts now certify. All 179 previously completed proofs
retain their verdict, pending count, and proof-node count. Both former
allocation aborts now hit the case timeout rather than crashing. The
native assertion-time OOM still causes the regression runner to fail;
it is not waived by the optimization.

The 17 harness tests, 116 current-source Linux C++ groups, and native SMT,
matching source-built Python bindings, and command-line help checks also
pass. Retained local artifacts include both complete replay results,
per-input logs, manifests, source/binary hashes, the uncommitted source
snapshot, resource measurements, and GDB traces.

### Skolem-context integration (2026-10-19)

The DAG-preserving expander is integrated with the Hilbert-choice Skolem
context and input-aware binder checker. Indexed checking and diagnostics
retain Skolem collection, dependency ordering, and freshness against both
original and expanded assertions. Binder certificates and Skolem collection
also use the refined expander, rather than reverting to tree-building
expansion. Preparation and diagnostics are separated into validation stages
to keep F* normalization tractable without increasing proof budgets.

The merged normal and profiling builds verify/extract successfully and
pass 38 native bridge groups and 21 CLI tests each, plus profiling accounting
checks. Regressions cover deep shared binder formulas and indexed/reference
agreement for genuine Skolem proofs and original-input freshness rejection,
including constant hashes. All 17 harness tests, 116 Linux C++ groups, and
source-matched Python/SMT/help smoke checks pass. The 225-input replay totals
above describe the pre-integration executable, not this merged revision;
the native assertion-time OOM remains unfixed.

### Build, status, and trust boundary

Every invocation first uses CMake to **build and install Windows Z3 from
this checkout**. The default build directory is `build`, with a local
installation in `build\install`; override with `-Z3WindowsBuildDir` and
`-Z3InstallDir`. All F*/Pulse verification, tests, and extraction explicitly
select that installation's `bin\z3.exe`. The script reports its path and
version, passing F*'s documented `--z3version` option rather than disabling
the version check. No downloaded historical solver or incidental `PATH`
entry selects the verifier. Run in a Windows C++20 developer PowerShell
with CMake and Python available.

In WSL, the script builds and installs **static `libz3`, Z3's executable,
and its official OCaml bindings from the same checkout**. The default
build directory is `~/z3-native-ffi-build` (`-Z3BuildDir`), with installation
in its `install` subdirectory. Compilation selects the installed OCaml
module directory and puts the installed library directory first for native
linking. The installed WSL solver's version is also printed.
`-WslBuildDir` selects the checker output directory. WSL requires the
OCaml/opam toolchain, Zarith, CMake, Python 3 for code generation, and a
C++20 compiler; no preinstalled OCaml Z3 package is used.

For a build with a fresh proof cache:

```powershell
.\fstar\tools\build_ocaml_checker.ps1 `
  -CacheDir 'C:\z3fstar\fstar\build_cache_pr11208_current_z3' `
  -WslBuildDir '~/z3checker-pr11208-latest' -RunTests
```

Use a fresh cache when measuring verification with a different SMT version;
otherwise unchanged modules may reuse previously checked artifacts. On
PR #11208 plus the current master fixes, the complete native pipeline and
proof regressions verify with the installed, source-built Z3 5.3.1.
`-RunTests` also verifies the resolution and polynomial-certificate
regressions and the in-memory Pulse equality, justification, and Farkas
checkers and tests before running native bridge and CLI tests.
Explicit integer-to-real identities and polynomial row/cross
proof steps make the arithmetic lemmas robust to the current solver's
automation, without changing their specifications or runtime rules.

The PR's new producer-side Farkas validation initially returned `UNKNOWN`
when rational weights were applied to integer premises. Validation now
clears all denominators with one positive common scale, matching the
legacy proof checker's treatment of integer coefficients. Exported weights
and checker acceptance rules are unchanged. A native regression exercises
the affected integer search; the frozen pre-fix executable returns
`UNKNOWN`, while the corrected producer returns `SAT`. The current
[cross-cut results](SMTLIB_CROSSCUT_REPORT.md) retain both producer runs.

Extraction has the roots `Z3NativeProof.fst` and `Z3NlaLemma.fst`, and
writes to `build_extract/native/`. Compilation copies only the explicitly
ordered live modules, not globbed outputs from earlier JSON builds. The
independent in-memory Pulse checkers are verified by `-RunTests` but are
not linked into this executable.

The resulting executable has no dynamic Z3-library dependency; ordinary
system C/C++/GMP libraries remain dependencies. Direct execution was also
checked with an empty environment and a `PATH` containing no tools.

| Exit | Direct-mode output | Meaning |
|---|---|---|
| 0 | `ACCEPT` | Obligation-free closed false root |
| 1 | `REJECT` | Unsupported or invalid certificate shape/inference |
| 2 | `ERROR ...` on stderr, or argument diagnostic | Input/foreign/resource error |
| 3 | `PARTIAL n` | Valid derivation with explicit pending leaves, not certified UNSAT |
| 4 | `SAT` | Solver reports satisfiable; no refutation checked |
| 5 | `UNKNOWN reason` | Solver did not decide, including timeout |

`--timeout-ms` bounds solving only; zero means unlimited. It does not bound
marshaling/checking or guarantee a process-wide memory/time limit.
`--stats` writes solve/marshal/check milliseconds and unique expression,
declaration, and proof-node counts to stderr, without proof artifacts.
`checker --version` reports the linked producer version.

`--diagnostics` adds an optional second checking pass and writes typed
unmet obligations to stderr, without changing stdout, exit status, or the
default fast path. Each `obligation` TSV row contains the rule, count, first
proof-node index, and a bounded sort-aware expression fingerprint; a
`diagnostic` row records the pending total or the rejection stage. Fingerprint
keys preserve operator structure, operand sorts, and small exact rationals,
while alpha-aliasing opaque declarations. They are coarse diagnostic
groupings, not semantic-equivalence tests or proof evidence. Counts sum to
the same pending total as the ordinary checker.

### Coverage extensions (2026-10-16)

`Z3ArithmeticRewrite.fst` checks integer affine normalization and numeric
comparison rewrites: reflexive/constant comparisons, inequality duality,
strict-comparison negation, and equivalent affine differences. It reuses
exact polynomial linearization and cancellation rather than trusting
printed rewrite names. Comparisons retain strictness; malformed operators,
division by zero, and unrelated nonlinear atoms do not become evidence.
At this baseline, real-valued term equality was deliberately not inferred
from equality of the numeric projection; the following extension adds the
necessary explicit model law.

The new arithmetic semantic lemmas use `numeric_operators` and local
value-typing premises for the actual operands. Unlike the older global
typing contract, these premises do not require every untyped environment
to give every variable the declared sort. The existing end-to-end wrapper
still uses the older combined model and retains its foundation gap; this
is not a completed sorted-model repair or unconditional SMT-LIB theorem.

Typed observational equality now admits matching non-Boolean operand
sorts. The supported same-model fragment requires value agreement for
non-Boolean terms, and truth agreement for Boolean terms. Reflexivity,
symmetry, transitivity, and congruence preserve a distinct `Observational`
judgment: this evidence never becomes an object-language equality or
an asserted formula. `iff~` remains Boolean-only. Existing checked
fresh-definition expansion can make a congruence conclusion syntactically
reflexive; the checker discharges that identity independently of redundant
observational premises, without converting those premises into equality.
Beyond this checked expansion, general naming/model extension still needs
freshness/model-extension witnesses and is not newly admitted. Input
membership, definition freshness, premise ordering, scope discharge, and
the closed false root remain checked.

The native marshaler is type-checked F* using the `ML` effect and foreign
handles; **no theorem proves correspondence of the foreign API to Z3's
semantics**. Native ownership, Z3 parsing/API views, OCaml/C bindings,
extraction/compiler, and the handwritten runtime remain trusted. The
shared kernel still checks asserted-input membership, all DAG entries,
definition freshness against unused as well as used inputs, premise
ordering, hypothesis discharge, and the closed false root. No foreign tag
can turn unsupported evidence into a checked inference.
The semantic-contract inhabitance limitation documented in
[the arithmetic report](ARITHMETIC_CERTIFICATE_REPORT.md) remains:
this integration is not an unconditional end-to-end SMT-LIB soundness proof.

`-RunTests` covers physical sharing, repeated proof traversal, a 12,000-layer
native AST, exact large numerals/rationals, authentic Farkas parameters,
parameterized declaration identity, binders, strict assertions/scopes,
malformed coefficients, typed observational composition and relation
separation, mixed-sort/declaration rejection, arithmetic rewrite positives
and negatives, and typed obligation diagnostics.
`tools/test_native_checker.py` exercises the direct CLI without importing
Python Z3; it also checks rejection of the removed protocol/options.

### Real affine and equality coverage (2026-10-17)

The eight `PARTIAL` cases in workflow run `39021665839` require real affine
term normalization, arithmetic equality normalization/decomposition,
supplied `arith/bound` coefficients, and checked triangle-equality clauses.
`Z3ArithmeticRewrite.fst` now checks these term and equality rewrites with
the existing exact polynomial kernel. An equality splits into non-strict
bounds only when their normalized polynomials match the equality's
difference and its negation. Triangle-equality clauses are checked by that
same decomposition, not accepted because of a theory hint. Strict-bound,
wrong-variable, and wrong-constant near misses remain unsupported.

Replaying all 17 inputs at the original pinned z3test commit produces
**16 ACCEPT, 0 PARTIAL, 1 UNKNOWN**: every formerly partial input is
obligation-free, while LassoRanker still exhausts its 10-second solver
budget without a proof. This is a separate local replay, not a rerun of
the historical 900-input cross-cut.

The native API view now preserves `arith/bound` coefficient vectors as
`ArithmeticFarkas`, whose premise/conclusion alignment and cancellation
are checked by the same exact kernel as `arith/farkas`. Incorrect weights
and coefficient counts remain explicit obligations. Assumed NLSAT origins
still remain assumptions, including on formulas that another rule could
independently establish.

**Additional semantic premise:** the `value` datatype has no real-number
constructor. Consequently `numeric_model` now explicitly requires equality
reflection for Real-sorted expressions: equal numeric projections imply
equal interpreted values. Operator laws alone do not establish this.
The real rewrite and numeric equality soundness lemmas are conditional on
this standard numeric-value model law; it is not an axiom asserting that a
particular rewrite, certificate, or proof is valid. The existing untyped
environment/inhabitance gap described above remains unresolved. No
unconditional end-to-end SMT-LIB soundness claim is made.

### Warning-free verification and extraction (2026-10-17)

The build treats F* warnings and enabled OCaml compiler warnings as errors.
The two closed-expression invariance lemmas have explicit termination
measures, and list append sites explicitly open `FStar.List.Tot` rather
than using deprecated syntax resolution. The refined sequence accessor
has an explicit impossible empty case, implemented by the runtime as an
exception rather than a value-producing fallback.

F* 2026.09.27 also emits single-arm constructor projectors whose domain
refinements disappear in OCaml. `tools/complete_ocaml_projectors.ml` uses
the matching OCaml compiler's parser/AST/printer to add an `invalid_arg`
arm only to generated `__proj__` functions matching a constructor of a
multi-constructor datatype. It operates on staged extracted modules,
not handwritten runtime or bridge code, and leaves values on the verified
domain unchanged. It does not disable partial-match warnings or alter
checker rules. This small extraction adaptation joins the existing
compiler/runtime trust boundary. Native tests exercise both a valid
projector and rejecting out-of-domain projector/sequence calls.
Run it with `Z3_FSTAR_CHECKER` pointing to the built checker:

```powershell
$env:Z3_FSTAR_CHECKER = '~/z3checker/checker'
python -m unittest discover -s fstar\tools -p 'test_native_checker.py'
```

A direct integration pilot also exercised the fixed `_000` input from each
of the nine archived SMT-LIB logics: four `ACCEPT`, one `PARTIAL`, and four
`REJECT`, with no process errors. The largest accepted proof had 396,782
proof entries and 48,294 unique marshaled expressions. This uses the
current linked Z3 5.3.1, not the historical cross-cut's Python Z3 5.1.
The rejected arithmetic samples originally exposed non-Boolean observational
equality, which the subsequent coverage extension supports in its
same-model fragment. The quantified samples expose proof-binder lambdas,
which remain unsupported. Actual operand sorts are preserved, never
coerced into Boolean facts or accepted as trusted theory tags. This
historical pilot is an integration check, not an updated coverage estimate.

**Latest cross-logic measurements (2026-10-16):**
[SMT-LIB cross-cut report](SMTLIB_CROSSCUT_REPORT.md) reevaluates the same
900 inputs with PR #11208 plus the producer correction above:
**334 `ACCEPT`, 242 `PARTIAL`, 142 `REJECT`**, retaining all 334 preceding
accepts, with no new complete refutations. There are 134 solver unknowns,
46 whole-process timeouts, and two allocation aborts. Fifteen formerly
non-unknown outcomes now reach solver timeouts; fewer partials are not
an improvement in obligation discharge. Native integer evidence export
and the new polynomial certificate's native AST bridge remain pending.
The report preserves the initial PR regression, its corrected replay,
the preceding 103-refutation coverage gain, native rule census, timings,
and historical solver/Python comparisons with their provenance caveats.

**Historical material follows.** Its older build commands, runtime details,
and timing claims describe their recorded configurations, not the current
statically linked binary. References to the exporter, JSON modules, and
compatibility commands below refer to deleted code and are not runnable
instructions.

## Goal

Every earlier proof-checking harness in this repo (`tools/extract_z3_proof.py
--check`, and even `--json`'s JSON-instance-`.fst`-per-proof variant)
re-invokes `fstar.exe` once per proof: it type-checks a `.fst` file (either
the full hand-written proof term, or a tiny JSON-instance wrapper) against
the whole Pulse proof-checker development, including an SMT-solver call,
every single time. That is correct but slow (**~10.3s** per proof, dominated
by F*/Z3 startup and re-verification of code that never changes between
runs) and conceptually wrong for a "run this already-verified checker on
new input" workflow: nothing about the *checker itself* changes from proof
to proof, only the *data* (the proof document) does.

This report describes a **compiled, standalone, native executable** built
once from the already Pulse-verified checker (`Z3PulseProofCheckerJson.fst`'s
`check_proof_json`), which at proof-checking time does no F*/fstar.exe
invocation, no re-type-checking, and no SMT-solver call at all — it just
runs ordinary compiled code against the JSON. Measured **~7ms** per proof
(WSL-internal timing, no process-launch overhead), roughly **1500x** faster
than the old per-proof `fstar.exe` path, because the entire cost of
verification was already paid once, at build time, by F*/Pulse itself.

## Why OCaml, and why a hand-written runtime shim

F* ships a `--codegen OCaml` backend (also `FSharp`, `krml`/C, `Plugin`,
...). OCaml was chosen because Pulse's separation-logic-verified, genuinely
*imperative* code (`ref`/`let mut`, not just pure functions) was confirmed
to extract to completely ordinary OCaml — `Pulse_Lib_Reference.alloc`/
`read`/`write` calls over a plain `ref` — with no special restricted subset
needed (unlike krml/Low*, which imposes additional restrictions on what
Pulse/F* code is expressible in C).

This machine has **no OCaml toolchain anywhere** (confirmed by exhaustive
search of `PATH`/`Program Files`/the filesystem). Per explicit instruction,
one was installed **inside WSL** (Ubuntu), since WSL has `gcc`/`make`, and
opam/OCaml are otherwise unavailable natively on Windows:

- Installed `m4`/`unzip` without root via `apt-get download <pkg>` (fetches
  the `.deb` without installing) + `dpkg -x <pkg>.deb ~/bin` (extracts
  without root).
- Installed the static `opam` binary the same way (opam's installer script
  run with `--download-only`, then the binary copied manually into
  `~/bin` — bypassing the installer's usual `sudo cp` step).
- `opam init --bare --disable-sandboxing -a -y` bootstraps an opam root
  without needing root or `bwrap`-sandboxing permissions.
- F* itself ships a **prebuilt** OCaml extraction runtime
  (`lib/fstar/lib/fstar.cmxa`/`fstar.a`, containing precompiled
  `Prims`/`FStar_*` modules) that extracted code is normally expected to
  link against. This was found to be **unusable in this environment**: its
  `.cmi` files require an *exact* OCaml compiler version match (bisected via
  `.cmi` magic-number/interface-hash comparison to **OCaml 5.3.0**
  specifically — 5.2.1 too old, 5.4.1 too new) *and* an exact match of the
  `batteries` library build used when `fstar.cmxa` was itself compiled
  (`fStar_String.cmi` requires a `BatUTF8` interface hash that no
  installable opam `batteries` version 3.1.0–3.11.0 reproduces on OCaml
  5.3.0). No combination of OCaml/batteries versions resolved this.
- **Resolution**: rather than keep chasing exact prebuilt-library version
  matches, inspect which `Prims`/`FStar_*`/`Pulse_Lib_*` symbols the
  *actually extracted* `.ml` files reference (a small, fixed set — about 40
  identifiers, found via `grep` across all extracted files) and hand-write
  a minimal from-scratch OCaml implementation of exactly those symbols,
  with **zero external opam package dependencies**. This sidesteps the
  version-matching problem permanently: the shim only has to agree with
  itself.

## The runtime shim (`fstar/ocaml_runtime/`)

| File | Provides |
|---|---|
| `prims.ml` | Exact `Prims.int`/`nat`/`pos` via Zarith `Z.t`, with arithmetic/comparison operators, Euclidean division/remainder, and `int_zero`/`int_one`/`of_int`/`not`/`pow2`; native `bool`/`string`/`list` aliases |
| `fStar_Pervasives.ml` | `false_elim` raises an explicit exception if an erased F* refinement is violated |
| `fStar_Pervasives_Native.ml` | `option` aliased to OCaml's native `option` (`type nonrec 'a option = 'a option = None | Some of 'a`); `fst`/`snd` |
| `fStar_List_Tot_Base.ml` | `length`/`rev`/`map`/`append`/`op_At`/`hd`/`mem`/`index`, wrappers over `Stdlib.List` with exact integer conversions |
| `fStar_Char.ml` | Native integer codepoints for extracted raw character patterns; `int_of_char` converts to `Z.t`, while `u32_of_char` retains the native codepoint |
| `fStar_UInt32.ml` | Native integer character-facing representation; `v` converts to exact `Prims.int` |
| `fStar_UInt.ml` | Fixed-width modular arithmetic, masks, shifts, rotations, and bitwise operations via Zarith |
| `fStar_String.ml` | `strlen`/`list_of_string`/`string_of_list`, byte-wise via `Stdlib.String`/`Stdlib.Char` (sufficient: the JSON proof format is pure ASCII) |
| `fStar_FunctionalExtensionality.ml` | `restricted_t` as a plain function-type alias (type-level only; never invoked at runtime by this checker) |
| `pulse_Lib_Reference.ml` | `ref`/`alloc`/`read`/`write` over a native OCaml `ref`, matching the exact (ghost-argument-padded) call shapes the extracted code uses: `alloc () v`, `read r () ()`, `write r v` |
| `pulse_Lib_Dv.ml` | `unreachable () = Stdlib.failwith "..."` |
| `main.ml` | CLI entry point: reads JSON from stdin (no args) or a file (one arg), calls `Z3PulseProofCheckerJson.check_proof_json`, prints `ACCEPT`/`REJECT`, exits `0`/`1`/`2` |

**Exact integers (2026-10-15):** `Prims.int` is now Zarith `Z.t`, not the
previous 63-bit shim. Extracted modules open `Prims`, allowing its exact
operators to shadow OCaml's machine-integer operators without editing
generated code. Arbitrary-size decoded references and arithmetic
certificates must not wrap. Native character patterns remain a separate
representation with explicit integer projections. The runtime is still
handwritten, not formally verified; huge values remain subject to resource
limits. See [the arithmetic integration report](ARITHMETIC_CERTIFICATE_REPORT.md)
for the semantic bridge, certificate checks, and measured coverage.

## Build pipeline (`fstar/tools/build_ocaml_checker.ps1`)

Two phases, fully scripted and reproducible from a clean checkout (given a
one-time WSL + opam switch `fstar53` (OCaml 5.3.0) setup, see the script's
header comment):

1. **Phase 1 (Windows, `fstar.exe`)**:
   - `fstar.exe --codegen OCaml` requires *every* module in the dependency
     graph — including the module being extracted itself, not just its
     dependencies — to already have a `.checked` file on disk ("Cross-module
     inlining expects all modules to be checked first"). A single
     `fstar.exe <file>.fst` invocation also defaults to "fly_deps" mode,
     which rejects multiple file arguments and won't write a `.checked`
     file for the top module unless every dependency was cached in a
     *separate prior* invocation.
   - Solution: invoke `fstar.exe --cache_checked_modules --cache_dir
     --include <dir> --smt <z3.exe> <single-module>.fst` **one module at a
     time**, in (approximately) dependency order, across up to 5 passes
     (modules whose deps aren't cached yet are harmlessly re-verified and
     retried on the next pass) — until all 17 modules (`Z3AstTheory.fst`
     through `Z3PulseProofCheckerJson.fst`) are cached.
   - Then one more `fstar.exe --codegen OCaml --cache_dir ... --extract
     "<module list>" Z3PulseProofCheckerJson.fst` call emits one plain
     `.ml` file per module under `--odir`.
2. **Phase 2 (WSL, `ocamlfind ocamlopt`)**: copies the hand-written shim
   (`ocaml_runtime/*.ml`) and the extracted `.ml` files into a WSL build
   directory, and compiles everything — shim files first, then the
   extracted modules in dependency order, then `main.ml` — into one native
   executable with
   `ocamlfind ocamlopt -package zarith -linkpkg <all files in order> -o checker`.
   The exact integer runtime requires Zarith in the selected opam switch.

Two non-obvious script bugs were found and fixed while validating this
script end-to-end from a clean state (deleted `build_cache`/`build_extract`
and `~/z3checker`, reran from scratch):

- PowerShell's `$ErrorActionPreference = "Stop"` combined with piping
  `fstar.exe`'s stderr output (including harmless warnings, e.g. "Warning
  290") through `Select-String` turned every such warning into a
  *terminating* `NativeCommandError`, aborting the script after the very
  first module even though `fstar.exe` itself succeeded. Fixed by using
  `$ErrorActionPreference = "Continue"` and checking cache-file existence
  / `$LASTEXITCODE` explicitly instead of relying on PowerShell exceptions.
- The here-string used to generate the WSL build shell script
  (`build_wsl_tmp.sh`) was written with Windows (`\r\n`) line endings via
  `Set-Content -Encoding ASCII`, which bash interprets literally (`set -e`
  became `set -e\r`, i.e. an invalid option; and a path ending in `\r`
  doesn't exist), and the non-interactive `wsl -e bash` invocation does not
  source `~/.bashrc`, so `~/bin` (where `opam`/`ocamlfind` live) was never
  on `PATH`. Fixed by writing the script with `\n`-only line endings
  (`[System.IO.File]::WriteAllText` with an explicit replace of `\r\n` to
  `\n`) and explicitly prepending `export PATH="$HOME/bin:$PATH"` inside
  the generated script.

After these fixes, `tools/build_ocaml_checker.ps1` runs start-to-finish
from a fully clean `build_cache`/`build_extract`/`~/z3checker` state and
produces a working `~/z3checker/checker` executable, confirming the whole
pipeline — not just the originally hand-run ad hoc commands — is
reproducible.

## Validation

- **Cross-validated against the real Pulse checker**: generated a genuine
  JSON proof document via `tools/extract_z3_proof.py --json` on a real
  `.smt2` benchmark, ran it through both (a) the new compiled executable,
  and (b) `fstar.exe` directly verifying a properly-named JSON-instance
  `.fst` file wrapping the same JSON — both agreed (`ACCEPT` / "All
  verification conditions discharged successfully").
- **Negative test**: fed the executable a malformed/non-JSON input —
  correctly printed `REJECT` and exited with a non-zero status.
- **Performance**: `fstar.exe --check` per proof: **~10.27s** wall-clock
  (F*/Z3 startup + full re-verification). New compiled executable, run
  repeatedly inside WSL (no per-call process-launch overhead counted):
  **~7ms** per invocation. The entire cost difference is explained by the
  old path re-doing verification work (type-checking + SMT) that is
  already complete and will never change, once per proof, while the new
  path does no verification work at proof-check time at all — it only
  interprets already-verified, compiled code against new data.

## Harness integration (`tools/extract_z3_proof.py`)

A new `--fast-check` flag (requiring `--json`) was added alongside the
pre-existing `--check` flag:

```
python tools/extract_z3_proof.py --json --fast-check my_benchmark.smt2
```

This writes the JSON proof document exactly as `--json` always did, then
pipes it (via `wsl -e bash -c "<checker-exe> <wsl-path-to-json>"`,
with the path translated from a Windows path to its corresponding
`/mnt/<drive>/...` WSL path) to the precompiled executable
(`--checker-exe`, default `~/z3checker/checker`) and reports
`ACCEPT`/`REJECT`. Critically, **this path never writes or compiles a new
`.fst` file, and never invokes `fstar.exe`**, satisfying the original
requirement that "the scripts that invoke the proof checker should not
rebuild a new Pulse file" — the checker executable is built exactly once
(via `build_ocaml_checker.ps1`) and reused across every subsequent proof.

The pre-existing `--check` flag (which does still shell out to `fstar.exe`
per proof) is left unchanged, so both the slow/fully-from-source path and
the fast/precompiled path remain available for cross-checking.

## Full refutations (`--full-proof`)

The default, legacy equational-fragment workflow remains unchanged.
The extractor also supports a separate `resolution-v1` document format
that preserves the complete ground refutation DAG:

```powershell
python fstar\tools\extract_z3_proof.py problem.smt2 --full-proof --fast-check --json-out proof.json
```

This format uses the same sort/declaration/expression pools, plus
`assertions` (expression indices), a `proofs` array of
`{"kind": ..., "conclusion": <expr index>, "premises": [<earlier proof index>, ...]}`,
and a `root` proof index. Unsupported steps have kind `trusted` and
retain their original rule name in `rule`; they are not disguised as
equational rewrite leaves.

`Z3ResolutionProofJson.fst` decodes each node into
`Z3UnifiedProof.fst`'s common `proof_node` representation. Its conclusions
and checked premises carry one of three distinct judgments:
`Holds A`, `Equal s t`, or `Observational s t`. Equality conclusions
are classified uniformly whether produced by resolution, MP, or an
equational rule. A single kernel handles inference, hypothesis scopes,
and explicit obligations, without manufacturing `Rewrite`, `Trusted`,
or `REq` wrappers around previously checked premises.
This allows congruence to consume equalities derived by `mp` or
`unit-resolution`. It also handles equality paths for `trans*`, checks
asserted leaves against the declared inputs, tracks hypotheses per
derivation, and requires a `false` root with no open hypotheses.
The checker supports ground inference and explicit ground/quantified
definition introductions, with capture-avoiding expansion as described
below. Quantified conclusions and inputs must be well scoped, including
the sorts of bound variables. Free variables are rejected. This does
not add general quantifier instantiation or Skolemization inference.

### At-most-once DAG checking and indexed caches

Both native JSON checking paths process each proof-array entry at most
once, in topological order. Caches are keyed by the entry's integer ID,
not by recursively hashing its proof term. A shared premise retrieves its
already-computed result; it never recursively checks the premise again.
Self references, forward references, negative indices, and dangling
references are rejected. Cache state starts empty for each document.

The full-proof path already cached `checked_fact` values, including their
hypothesis scopes. The legacy JSON path now does the same bottom-up
computation through `cached_proof`, whose F* refinement proves
`result == fact term` for every cached success **and failure**. The
refinement and its proof are erased during extraction: no recursive
`fact` call is executed to establish or retrieve a cached result.
The Pulse JSON wrapper consumes this result while retaining its previous
postcondition. The separate in-memory `Z3PulseProofChecker.check_proof`
tree API is unchanged; the native JSON CLI no longer invokes that
recursive tree traversal.

The shared persistent binary-trie cache also indexes decoded expressions.
References now take `O(log ID)` lookup time, and expression accumulation
uses list prepend rather than repeatedly copying a growing prefix.
`lemma_index_put` proves that insertion stores the requested key and
leaves all other lookups unchanged. The full-proof speedups below come
from this indexing change, not from adding a proof cache where one
already existed.

The following are medians of three alternating before/after runs on
identical certificates in WSL. Timings include native process startup,
JSON parsing, decoding, and checking, but exclude Z3 proof generation,
F* compilation, and WSL startup. `/usr/bin/time` also records peak RSS.

| Certificate | Proof nodes | Before | After | Speedup |
|---|---:|---:|---:|---:|
| `dead_dnd001` | 32,679 | 1.410 s | 0.608 s | 2.32x |
| `QF_UF_006` (`gensys_brn1083`) | 26,446 | 1.010 s | 0.508 s | 1.99x |
| `QF_UF_094` (`NEQ031_size7`) | 94,000 | 22.552 s | 15.231 s | 1.48x |
| `QF_UF_015` (Sokoban) | 11,714 | 70.305 s | 3.216 s | 21.86x |
| Legacy shared transitivity DAG, depth 40 | 41 | timeout at 5 s | 0.108 s | >46x |

The legacy synthetic DAG has over two trillion node occurrences when
unfolded as a tree, but just 41 indexed proof nodes. Its baseline timing
is a timeout, not a completed run. On `dead_dnd001`, median peak RSS also
drops from 123.7 MiB to 99.5 MiB. All 58 exported QF_UF certificates now
report `ACCEPT` within a 30-second per-proof limit; the slowest takes
14.9 seconds in the four-worker recheck. Acceptance policies and proof
obligation counts are unchanged. Detailed timing/RSS samples and corpus
results are retained under ignored `build_extract` artifacts
`proof_once_benchmarks.json`, `proof_once_benchmarks.db`, and
`proof_once_corpus.json`.

`RUnitRes` now checks a stated consequence instead of requiring a
syntactically rewrapped residual. A residual `[C]` may conclude `C` or
`(or C)`, including when `C` is itself a disjunction. An empty residual
may conclude `false` or `(or)`. Reordering and sound weakening are
accepted provided every surviving literal is covered. Resolving a
formula directly against its negation also works when that formula is
a disjunction. The resolution soundness theorem covers these
representations; dropping a surviving literal is still rejected.

The executable distinguishes:

- `ACCEPT`, exit 0: a closed refutation with no unverified leaf obligations.
  This is relative to the explicit trust policy for definitional axioms below.
- `PARTIAL N`, exit 3: the derivation and hypothesis scopes checked, but
  `N` rewrite/unsupported-rule obligations remain unverified.
- `REJECT`, exit 1: malformed data, invalid inference, undeclared input,
  a non-false root, or an open hypothesis.

Full-proof mode discharges syntactically reflexive rewrites using the
verified total identity rule `identity_rewrite x = Some x`, and n-ary
Boolean `and`/`or` flattening using `Z3BooleanRewrite.flatten_rewrite`.
Flattening recursively splices occurrences of the same connective into
one ordered argument list, preserving duplicates and leaving different
connectives opaque. It supports empty and singleton nested applications;
the result is still an application of the original connective.
The declarations, operator tags, domains, Boolean operands, and result
sort are checked. Reordering, deduplication, and reverse reassociation
are not licensed by this rule.

`lemma_flatten_rewrite_sound` derives semantic equality from the standard
n-ary conjunction/disjunction semantics, using proofs that flattening
preserves their argument-list meanings.

`Z3BooleanNormalForm.fst` additionally proves n-ary De Morgan and
double-negation normalization, implication elimination, contextual
associativity/commutativity/idempotence, singleton collapse, Boolean
constant/complement elimination, and absorption (`a /\ (a \/ b) = a`
and its dual). Structural normalization traverses the recognized Boolean
fragment without a truth-table width limit; recursive set comparison has
fuel 32. `Z3BooleanRewrite.fst` also proves reflexive equality of any sort
reduces to `true`, including inside Boolean contexts.

When these structural rules do not suffice, a depth-8, width-10 Boolean
skeleton uses shared subexpressions as opaque boundaries and checks at
most 1,024 truth-table rows. This reuses the verified generic truth-table
engine in `Z3BoundedBoolEquiv.fst`, **not** its differently numbered
`Z3BasicExprTheory` classifier. A canonical native-tag classifier and
`lemma_boolean_cut_sound` connect the skeleton to the existing standard
Boolean semantics; `lemma_boolean_equiv_sound` proves the resulting
semantic equality. Non-Boolean theory atoms remain opaque except for the
proved reflexive-equality rule. Budget exhaustion means unverified, not
equivalent; no runtime solver call or additional trust assumption is used.

Boolean `ite` is exported with `op_ite` (Z3's declaration name is `if`).
Both Boolean classifiers require three Boolean arguments and a Boolean
result. The verified cut lowers it to `and`/`or`/`not`, reducing constant
conditions or branches directly before normalization. The semantic bridge
uses an explicit standard `ite_sound` interpretation contract; non-Boolean
branches and uninterpreted lookalikes remain opaque to this Boolean engine. Depth/atom budgets
are unchanged. With this support, `cvc\read5.smt2` changes from `PARTIAL 1`
to `ACCEPT`: all 12 rewrite leaves are discharged, including its nested
Boolean ITE chain, under the same default trusted-definition policy.

`Z3ArrayRewrite.fst` adds a separate, fuel-64 contextual equality checker:

- `store(store(a, i, v), i, w) = store(a, i, w)`;
- `store(a, i, select(a, i)) = a`;
- `select(store(a, i, v), i) = v`;
- `select(store(a, i, v), j) = if(i = j, v, select(a, j))`.

These identities compose inside applications, nested stores/selects, array
equalities, and negations. Equality operands may be reversed. Typed ITEs
with scalar or array branches support constant/reflexive conditions,
identical branches, and branches independently proved equal to the same
target. `lemma_equivalent_sound` proves semantic equality by induction
over the recursion budget and argument lists, reusing `Z3ArrayTheory`'s
store/select proofs. The additional `term_ite_sound` model contract is
standard branch-selection semantics, not an assumption that the proposed
rewrite is valid. Select/store matching retains `Z3ArrayLemma`'s flat,
single-index, non-Boolean scalar index/element fragment and exact
declaration, operator-tag, and sort checks. Distinct index names are not
assumed unequal; fresh names are not assumed to denote their definitions.
Unsupported instances and budget exhaustion remain obligations.

The full-proof exporter also preserves exact integer, rational, and
bitvector numeral identities as opaque declarations. Previously, distinct
numerals could decode to identical declarations (e.g. both named `Int`),
which contextual ITE branch checking exposed. Their exact printed values
and numeral-kind parameters now distinguish them; this adds no arithmetic
reasoning or numeral-value interpretation.

These rewrite checks apply to ordinary equality or Boolean observational
equivalence without changing either relation. Other rewrites remain
obligations; Python-side classifications are diagnostic mirrors, not the
acceptance authority. The legacy equational matcher inventory is unchanged.

On `QG-classification\loops6\dead_dnd001.smt2`, all 1,058 rewrite leaves
are now discharged (previously 310 remained after identity and flattening).
Rechecking the 58 successfully exported QF_UF proofs from the existing
seed-42, 100-file sample discharges all 47,776 rewrite leaves. Before
indexed caches, eight workers and a 30-second per-proof checking limit
gave 57 `ACCEPT` results and one timeout; that last proof (`QF_UF_015`,
Sokoban) reported `ACCEPT` in 70.1 seconds with a 120-second limit.
The other 42 sampled
files did not previously produce exported proofs and are not counted as
checked successes. These historical results used the then-default def-axiom
trust policy, not independent validation of those definitions. See the
checked-policy recalibration below for current results.

#### Fresh QF_UF/QF_AX evaluation (2026-10-14)

A complete rerun used the same seed-42 manifest and SHA-256-checked input
files: 100 UNSAT-annotated benchmarks per logic, 32 workers, a 10-second
proof-generation wall-clock limit, a separate 60-second export watchdog,
and a 10-second native-checker limit. Unlike the 58-certificate recheck
above, this reran proof generation and export as well.

| Logic | Proved UNSAT | Exported | ACCEPT | PARTIAL | Checker timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 57 | 56 | 0 | 1 | 43 |
| QF_AX | 100 | 99 | 1 | 83 | 15 | 1 |

QF_UF had seven proof-generation timeouts and 36 export timeouts; QF_AX
had one export timeout. There were no checker rejects or errors. The
remaining QF_UF checker timeout was `QF_UF_094` (`NEQ031_size7.smt2`);
the prior 30-second recheck and the fresh 10-second evaluation therefore
measure different limits and workloads.

The 56 accepted QF_UF proofs contained 1,350,973 DAG nodes and no pending
obligations. The 84 validated QF_AX derivations contained 285,459 nodes
and 8,055 pending obligations: 8,031 `th-lemma` and 24 unsupported rewrites.
These counts cover only `ACCEPT`/`PARTIAL` results, not timed-out proofs.
These historical `ACCEPT` results were conditional on the then-trusted
`def-axiom` policy.

For comparison, the previous full-proof evaluation with the same limits
gave QF_UF 1 `ACCEPT`, 48 `PARTIAL`, and 9 checker timeouts from 58 exports;
QF_AX had 83 `PARTIAL` and 16 checker timeouts from 99 exports.
Its validated proofs retained 32,101 QF_UF rewrite obligations and
23,226 QF_AX obligations. Validated sets differ between runs, so aggregate
obligation counts are not a paired per-proof comparison.

The rerun took 187.5 seconds. Its manifest, per-file proofs, phase timings,
checker outputs, source/binary hashes, summary, CSV, and SQLite benchmark
log are retained locally in
`C:\smtlib-benchmarks\proof_check_full_20261014_2054\full`.

#### Fresh rerun with array and Boolean ITE checking (2026-10-15)

The same SHA-256-checked, seed-42 sample of 100 files per logic was
rerun end-to-end after the array and Boolean ITE changes, with unchanged
32-worker, 10-second proving, 60-second export, and 10-second checking
limits. Native protocol counts are authoritative; Python obligation
predictions are retained only as diagnostics.

| Logic | Proved UNSAT | Exported | ACCEPT | PARTIAL | Checker timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 57 | 56 | 0 | 1 | 43 |
| QF_AX | 100 | 99 | 71 | 12 | 16 | 1 |

There were no checker rejects, errors, or diagnostic count mismatches.
QF_UF again had seven proving and 36 export timeouts; QF_AX had one
export timeout. The QF_UF checker timeout remains `QF_UF_094`.
The 83 validated QF_AX derivations contain 252,305 DAG nodes, with
7,782 array theory lemma instances discharged and 24 remaining rewrite
obligations across the 12 partial proofs. Accepted QF_UF proofs contain
1,350,973 nodes and no obligations. Acceptance remains relative to the
unchanged default trusted-definition policy.

The sample does not include `cvc\read5.smt2`; its separately demonstrated
Boolean ITE improvement is therefore not measured by these counts.
The earlier array-only paired recheck's 70 QF_AX acceptances and this
run's 71 should not be interpreted as a controlled ITE-only gain:
this is fresh proof generation/export, and timeout sets vary.

The run took 189.2 seconds. The 200 per-file outcomes/statistics,
157 exported proofs, CSV, 200 logged SQLite benchmark runs, original
manifest, source hashes, working-tree patch, and binary provenance are
retained in
`C:\smtlib-benchmarks\proof_check_full_20261015_0345\full`.
The native binary's SHA-256 is
`51863acb94708857ff4fbac0a1903c2cb8971288bcba004f383d6e5536a8cda5`.

#### Contextual array rewrite evaluation (2026-10-15)

The frozen binary above and the new binary were run on the **same 157
byte-identical exported certificates** from the preceding sample, with
32 workers and a 10-second checking deadline. No proof rewriting,
re-export, or trusted-definition policy change was involved.

| Logic | Before ACCEPT / PARTIAL | After ACCEPT / PARTIAL | Remaining obligations before / after | Checker timeouts, both |
|---|---:|---:|---:|---:|
| QF_UF | 56 / 0 | 56 / 0 | 0 / 0 | 1 |
| QF_AX | 70 / 12 | 79 / 3 | 24 / 3 | 17 |

Thus **21 of the 24 outstanding rewrite obligations (87.5%)** were
discharged, making nine previously partial proofs fully accepted under
the existing trust policy. There were no accepted-proof regressions,
rejects, or errors. The paired run's timeout set differs slightly from
the preceding fresh run; coverage comparisons above use only the paired
results, not the earlier 71-acceptance figure. Across the same 82
validated QF_AX certificates, summed process wall times were 110.04 s
before and 110.41 s after (about +0.34% in this single measurement);
QF_UF was 57.76 s versus 57.70 s. These concurrent process-time sums
are not end-to-end elapsed times or a statistically established speedup.

A fresh generation/export/check run on the same SHA-256-verified
100+100-file manifest, with the same 32-worker, 10/60/10-second limits,
gave:

| Logic | Proved UNSAT | Exported | ACCEPT | PARTIAL | Checker timeout | Not checked |
|---|---:|---:|---:|---:|---:|---:|
| QF_UF | 93 | 57 | 56 | 0 | 1 | 43 |
| QF_AX | 100 | 99 | 79 | 3 | 17 | 1 |

It took 189.9 seconds, with no rejects, errors, or diagnostic count
mismatches. The 82 validated QF_AX derivations contain 221,215 DAG nodes,
including 7,575 checked array-theory lemma instances and three remaining
rewrite obligations. Two (`QF_AX_022`, `QF_AX_041`) introduce `k!0`
without a checked definition witness; the third (`QF_AX_085`) needs
stronger guarded-ITE reasoning. They correctly remain `PARTIAL`.
QF_UF again validates 1,350,973 nodes without obligations.

All 47 Python/exporter/native tests pass, including contextual positive
cases, reversed rewrites/guards, unsupported array sorts, fresh names,
unjustified distinct indices, wrong values/bases, recursion-budget
exhaustion, operator spoofing, ill-sorted ITEs, and distinct numerals.
The native dependency build and the executable Boolean/full-DAG F*
regression modules discharge all verification conditions.

Paired results, input hashes, source snapshots, both native binaries, and
fresh results/proofs/CSV/provenance plus 200 SQLite benchmark records are
retained under
`C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815`
(`paired` and `full`). The new native binary's SHA-256 is
`0cca221826b0ccf2d48d3fe43075290d05cb2d7fc04980ec835a88b3cb904102`.

The ground Boolean rules `mp~` and `iff~` are checked, not trusted.
Z3's emitted `refl` name is also recognized as reflexivity (the older
`reflexivity` spelling remains accepted).
Observational equality `(~ A B)` is preserved with its own `op_oeq` tag
and the unified kernel's distinct `Observational` judgment.
It is proof-only: it cannot be asserted as an ordinary Boolean fact,
embedded inside a Boolean expression, or consumed by ordinary equality
congruence/resolution. `mp~` requires `~`, whereas ordinary `mp` rejects it.
The explicit `iff~` bridge converts `(= A B)` to `(~ A B)`, not conversely.
Observational reflexivity, symmetry, transitivity, paths, and Boolean
congruence retain `~` conclusions; mixed transitivity can promote Boolean
equality premises through that one-way bridge without ever producing `=`.

The ground observational theory proves observation preservation and derives
equisatisfiability for this checked subset. It does **not** identify Z3's
general equivalence modulo naming with same-model Boolean equality:
naming is handled only through the explicit definition accumulation and
expansion below, before the observational kernel runs. General
Skolemization and unverified NNF steps remain obligations. Non-Boolean
observational equalities remain outside the checked fragment.
Legacy equational-mode `ACCEPT` still has its original, structural-only
meaning and must not be mistaken for certification of an UNSAT refutation.

### SMT array axioms and checked theory lemmas (2026-10-14)

`Z3ArrayTheory.fst` establishes the axiom schemas instantiated by
`src\smt\theory_array_base.cpp` and `theory_array_full.cpp`. Arrays are
extensional functions; a multi-index array is represented by a tuple index.
The mathematical coverage is broader than the executable matching fragment:

| SMT instantiation | Formal result in `Z3ArrayTheory` |
|---|---|
| Store axiom 1, reading at the written index | `lemma_select_store_same` |
| Store axiom 2, reading at another index | `lemma_select_store_diff`, `lemma_store_axiom2`; `lemma_store_axiom2_coordinate` covers each multi-index disequality guard |
| Lambda beta reduction; select congruence | `lemma_select_lambda`, `lemma_select_congruent` |
| Extensionality and its Skolem index | `lemma_array_extensionality`, `lemma_extensionality_witness`, `lemma_extensionality_index_exists`, `lemma_extensionality_axiom` |
| Select of constant, as-array, and n-ary map | `lemma_select_const`, `lemma_select_as_array`, `lemma_select_map_n` |
| Default of constant, as-array, lambda, and n-ary map | `lemma_default_const`, `lemma_default_as_array`, `lemma_default_lambda`, `lemma_default_map_n` |
| Default of store: singleton, finite non-singleton, fresh-index cases | `lemma_default_store_singleton`, `lemma_default_store_finite`, `lemma_default_store_fresh` |
| Epsilon/diagonal witnesses | `lemma_diagonal_fresh`, `lemma_integer_epsilon_fresh` |
| Choice of a satisfying predicate index when one exists | `lemma_choice_witness`, `lemma_choice_axiom` |

The default model uses a shared epsilon index. Store-default invariance
requires that epsilon differ from the stored index: it is **not** proved
as an unconditional identity at an arbitrary fixed index. The singleton
case instead returns the stored value. The finite non-singleton case
establishes the two default/select identities and equality of reads at a
diagonal index different from the write. For integer indices, a finite
list of written indices has an explicitly constructed fresh epsilon.
Extensionality likewise requires a genuine difference witness, not an
arbitrarily chosen index; witness existence is proved for inhabited index
sorts. The as-array default instantiator is currently disabled in C++,
but its mathematical schema is included.

The new `Z3ArrayLemma.fst` recognizes premise-free `th-lemma` conclusions:

```text
select(store(a, i, v), i) = v
(i = j) or (select(store(a, i, v), j) = select(a, j))
(a = b) or not(select(a, array-ext(a, b)) = select(b, array-ext(a, b)))
```

Equality orientation and the two clause literals may be swapped.
Declarations, operator tags, arities, argument/result sorts, base arrays,
indices, and witness arguments must all match. `array-ext` has a distinct
`op_array_ext` tag; an uninterpreted function with that name, an unrelated
array pair, or an arbitrary witness does not discharge the obligation.
The native checker is authoritative; Python classification is only a
diagnostic mirror. Unsupported instances remain `PARTIAL`, not silently
trusted. The current executable fragment covers one-dimensional flat
arrays with non-Boolean scalar index and element sorts, using the existing
`VArr`/`VInt` value representation. Boolean-valued, nested, multi-index,
map/default/choice, and quantified array instances are not newly accepted
by these rules.

`lemma_array_lemma_sound` derives the matched conclusions from the proved
array theory and standard select/store/difference-witness semantics.
`Z3UnifiedProof.model_sound` includes this explicit `array_model`
interpretation contract, just as it includes Boolean and arithmetic
semantics. Matched nodes contribute zero pending obligations; other
theory leaves retain their original obligation. This array evaluation
predated the checked `def-axiom` policy described below.

The broader evaluation also exposed a tightly related structural-rule
gap: `not-or-elim` now accepts a positive literal when the disjunction
contains its negation, as well as the previously supported negative
conclusion. Both polarities have F* soundness and regression checks;
unrelated conclusions are rejected.

#### Seven downloaded logics and paired coverage

The official SMT-LIB 2025 non-incremental archives were downloaded from
[Zenodo record 16740866](https://zenodo.org/records/16740866), verified
against their published MD5 checksums, and extracted under
`C:\smtlib-benchmarks`. Each logic's sample is
`random.Random(42).sample(sorted(UNSAT_annotated_paths), 100)`, with input
SHA-256 hashes retained in the manifest.

Proof generation/export ran once, using 32 workers, a 10-second
proof-generation limit and a separate 60-second export watchdog.
The table compares the frozen previous native checker with the new one
on those archived DAGs, at 32 workers and 10 seconds per check. It also
includes the existing QF_AX sample, without rerunning proof search.
All 109 certificates containing an untagged `array-ext` declaration were
re-exported and checked to be structurally identical to their archived
documents after erasing **only** the new built-in operator tag. Source
and replacement hashes are retained; the other 511 certificates are
unchanged.

| Logic (100 selected each) | Proved UNSAT | Exported | ACCEPT before / after | PARTIAL before / after | REJECT before / after | Checker timeout before / after |
|---|---:|---:|---:|---:|---:|---:|
| QF_LIA | 79 | 69 | 5 / 12 | 25 / 51 | 33 / 0 | 6 / 6 |
| QF_LRA | 58 | 55 | 2 / 3 | 28 / 52 | 25 / 0 | 0 / 0 |
| QF_IDL | 48 | 25 | 1 / 2 | 19 / 20 | 2 / 0 | 3 / 3 |
| QF_UFLIA | 97 | 95 | 3 / 3 | 80 / 92 | 12 / 0 | 0 / 0 |
| QF_AUFLIA | 100 | 100 | 1 / 28 | 87 / 63 | 4 / 0 | 8 / 9 |
| AUFLIA | 91 | 91 | 0 / 0 | 0 / 0 | 91 / 91 | 0 / 0 |
| UFLIA | 86 | 86 | 0 / 0 | 0 / 0 | 86 / 86 | 0 / 0 |
| QF_AX | 100 | 99 | 1 / 70 | 81 / 12 | 0 / 0 | 17 / 17 |

In this historical run, all 177 quantified exports were rejected by the
then-ground-only decoder;
they are not counted as verified. Files that did not export are not
checked. Seven exports failed through Python expression-recursion limits
(three QF_LIA, four QF_IDL); the other missing exports timed out.
The original baseline driver's two reported diagnostic errors
(`QF_LIA_017`, `QF_LRA_023`) were mismatches between Python's predicted
obligation count and the native `PARTIAL` count, not native errors.
The paired table records actual native protocol results, with no such
errors. Timeout counts can vary from earlier runs.

Across the seven new logic samples, accepted refutations increase from
12 to 48. Including QF_AX, they increase from 13 to 118, with no
accepted-proof regressions. On the **same 82 QF_AX proofs validated in
both phases**, pending obligations fall from 7,599 to 24; all remaining
obligations are array rewrites, rather than array `th-lemma` instances.
The same 87 mutually validated QF_AUFLIA proofs fall from 10,765 to
5,133 obligations. The other logics' mutually validated sets keep the
same obligation totals; the `not-or-elim` correction enables additional
proofs to pass structural checking. These remain conditional
refutations under the documented trusted-definition policy, not a
claim of independently checked CNF definitions.

The manifests, download metadata/checksums, baseline results, proof
documents, retag-equivalence checks, and paired native outputs remain in
`C:\smtlib-benchmarks\proof_check_seven_20261014`, principally
`baseline`, `tagged_certificates`, and `array_extension_final`.
The previous/current native SHA-256 hashes for this paired run are
`25e359134f83972e7de8c5fd97cd15b30380cb12c1ff160d63113e491f992cd0`
and `f5ea8d56d71b5c1e6f5910488fd575a871f10a040e33e82e204c7e5e6589a4f5`.
All checker verification conditions and the F* regression module pass;
43 Python/exporter/native tests cover valid and malformed array
instances, witness spoofing, and both `not-or-elim` polarities.

### Definitional axioms and original assertions

`def-axiom` is no longer trusted. A premise-free ordinary Boolean leaf
contributes zero obligations only when its conclusion is independently
checked: a propositional Tseitin tautology, a guarded term-ITE identity,
a verified `distinct` expansion clause,
or a tautology after expanding an accumulated fresh definition witness.
Other well-formed instances contribute one explicit obligation and yield
`PARTIAL`, never certified `ACCEPT`. Malformed/non-leaf instances are
rejected. The obligation-free soundness theorem has no assumption that
`def-axiom` conclusions are true. The same policy applies to the older
`{"kind":"trusted","rule":"def-axiom",...}` encoding.

Only **`asserted` leaves** must match the supplied input assertions.
Membership is structural, not logical equivalence; generated Tseitin
clauses need not themselves be inputs. This is checked in every full-proof
document, with or without:

```powershell
python fstar\tools\extract_z3_proof.py problem.smt2 --full-proof --check-original-assertions --fast-check
wsl -e bash -c '~/z3checker/checker --check-original-assertions proof.json'
```

The document field `"check_original_assertions": true` and native CLI flag
remain compatible, but neither changes the `def-axiom` policy nor adds a
membership requirement to it. The native flag additionally rejects legacy
equational documents, which have no original-input policy. A malformed
metadata field is rejected, and document metadata cannot disable the flag.
The caller must supply the actual original assertions; the checker does
not authenticate a JSON input list against an external SMT file.

The source audit followed `mk_clause_def_axiom` and the gate clauses in
`src\smt\smt_internalizer.cpp:1672-1868`, term ITE clauses at `930-953`,
distinct expansion at `551-561`, and the weakening/true cases in
`src\solver\simplifier_solver.cpp:323-332`. The public schemas are
documented in `src\api\z3_api.h:601-634`.
`Z3BooleanNormalForm.forced` proves a clause by propagating the assumption
that all its disjuncts are false; its semantic lemma does not enumerate
assignments or bound gate arity. A shared Boolean frontier gives consistent
abstraction at depth three, even when operands occur at different depths.
One additional level unfolds literal connectives without adding a
frontier entry per literal of a wide gate.
Validated operator declarations distinguish built-ins from uninterpreted
lookalikes. Binary XOR has an explicit `op_xor` tag and standard Boolean
interpretation contract. Bounded Boolean equivalence remains a fallback
for formulas within a 128-Boolean-node budget; large unsupported theory
axioms do not trigger unbounded normal-form work.

The audit also found forms needing more than propositional reasoning.
Distinct expansion is now checked by the semantic embedding below.
Remaining unsupported forms include BV `carry`/`xor3` gates
(`src\smt\theory_bv.cpp:1052-1101`), quasi-macros with fresh else functions
(`src\ast\macros\quasi_macros.cpp:256-340`), quantified Horn transformations,
and temporary clauses (`src\smt\smt_context.cpp:3463`). An unsupported
instance is an obligation, not silently accepted because of its rule tag.

#### Initial checked-policy calibration (2026-10-15, before distinct support)

The paired run rechecked the same 156 successfully exported certificates
from the existing seed-42, 100-QF_UF/100-QF_AX manifest, without regenerating
proofs. Both binaries used 32 workers and a 10-second per-proof limit:

| Logic | Policy | ACCEPT | PARTIAL | Checker timeout | Not exported |
|---|---|---:|---:|---:|---:|
| QF_UF | Previous trusted axioms | 56 | 0 | 1 | 43 |
| QF_UF | Independently checked axioms | 54 | 2 | 1 | 43 |
| QF_AX | Previous trusted axioms | 79 | 3 | 17 | 1 |
| QF_AX | Independently checked axioms | 79 | 3 | 17 | 1 |

There were no rejects or checker errors. The two formerly accepted UF
proofs (`QF_UF_001`, `QF_UF_015`) now correctly retain a `distinct`
expansion obligation rather than relying on the rule's name. The existing
UF timeout is `QF_UF_094`. The three AX obligations are the previously
documented unsupported rewrites, not new axiom obligations.

A separate axiom-only calibration retained all 11,416 `def-axiom` leaves
from all 156 exports, pruned unused expressions, and appended an asserted
false root solely to exercise every leaf through the native document
checker. This is an axiom-coverage measurement, **not** an additional set
of certified input refutations. It checked 11,413 leaves, with three
explicit obligations and no timeouts, rejects, or errors. The unsupported
leaves are the actual `distinct`-to-pairwise-disequality expansions at
arities 9, 209, and 7 in the three UF certificates above. No `intro-def`
nodes occur in this corpus; fresh Skolem definition witnesses are
additionally covered by ground/quantified regressions.

The archived jobs, per-proof outcomes, binary provenance, and pruned
axiom-only certificates are in
`C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815\defaxiom-policy`.
The previous/final native SHA-256 hashes are
`d06d634b447037eeb9a336b1c03efb5d050e9802d4784c095b9e6c8345d86513`
and `b881a4aeca6db0baf20fb43e2afe8718d117c9d59d9568493f4d1cabcf4070c6`.
All checker verification conditions, the F* regression module, and the
56-test Python/exporter/native suite pass. Regressions include wide
compound Tseitin gates, XOR and Boolean/term ITEs, both Boolean definition
clause orders, ground and quantified Skolem witnesses, missing guards,
conflicts/cycles, final input freshness, and exact `asserted` membership
in both CLI modes.

### Verified n-ary distinct expansion

`Z3BasicExprTheory.fst` defines `distinct_from` and `distinct_values` as
pairwise inequality over arbitrary semantic values, and proves their
agreement with the existing executable `all_distinct` for equality types.
The general predicate is important: array-valued semantic objects contain
functions and do not have decidable F* equality. No assumption that two
different syntax nodes denote different values is made.

`Z3DistinctAst.fst` adds typed native declarations, constructors,
recognizers, and the exact expansion from
`src\ast\ast.cpp:2584-2602`. Zero or one argument expands to `true`;
two arguments expand to `not (= a b)`; larger arities expand to the flat
conjunction of every pair `i < j`, in source order. Arguments must have
one common sort, including Boolean and array sorts. Repeated arguments
are allowed and correctly make the corresponding disequality false.

`Z3DistinctEmbed.fst` provides `apply_lemma_distinct`, proves that its
synthesized expansion has the same denotation as the original operator,
and derives both generated `def-axiom` clauses:

```text
(or (not (distinct args...)) expansion)
(or (distinct args...) (not expansion))
```

Swapped disjuncts and the binary case's simplified double negation are
recognized. The proof uses only the standard interpretation contract
for `distinct`, plus the existing Boolean/equality contracts; it does
not assume the generated clauses true. `Z3Definitions.tautology` invokes
these rules before propositional abstraction, so neither the truth-table
width limit nor the fallback budget limits the operator's arity.
The checker matches the complete canonical pair list, not arbitrary
subsets or duplicate/mismatched pairs.

The exporter and JSON decoder use the new native `op_distinct` tag.
Full declarations, homogeneous argument sorts, arity, and empty integer
parameters are validated. An uninterpreted lookalike is not promoted
based only on its name. Older documents with an untagged `distinct`
declaration need re-exporting with the updated exporter.

The paired evaluation used the same archived proof DAGs and limits as
above. For five affected certificates, nine operator annotations were
migrated only after matching actual `Z3_OP_DISTINCT` declarations in the
checksum-verified original parsed inputs, including their complete sort
signatures. Ambiguous uninterpreted lookalikes are rejected by the migration;
all other JSON fields and proof DAG nodes are checked unchanged.

| Logic | Before distinct rules: ACCEPT / PARTIAL / timeout | After: ACCEPT / PARTIAL / timeout |
|---|---:|---:|
| QF_UF (57 exports) | 54 / 2 / 1 | 56 / 0 / 1 |
| QF_AX (99 exports) | 79 / 3 / 17 | 79 / 3 / 17 |

Both newly accepted UF proofs now have zero pending obligations. The
axiom-only calibration checks **all 11,416 leaves in all 156 exports with
zero obligations**, including the three previously unsupported `distinct`
expansions. This does not certify the full proofs that still exceed the
10-second limit. The remaining three AX obligations are unrelated rewrites.
There are no new rejects, errors, or axiom-only timeouts.

Jobs, authenticated tag migrations, results, and binary provenance are
archived at
`C:\smtlib-benchmarks\proof_check_array_rewrites_20261015_0815\distinct-extension`.
The previous/final native SHA-256 hashes are
`b881a4aeca6db0baf20fb43e2afe8718d117c9d59d9568493f4d1cabcf4070c6`
and `b4b430fe820940b03523f2e8ed017ac8c8a952542f5c08e30f6df141e874b593`.
All theory/embedding/kernel verification conditions and the executable F*
regression module pass. The 60-test Python/exporter/native suite includes
actual generated distinct proofs, an expansion-derived refutation,
arities 0/1/2/3/9/209, Boolean and array arguments, and rejection or explicit
obligations for malformed declarations, spoofed operators, wrong polarity,
and missing/duplicated/substituted pairs.

### Accumulated definition introductions and final freshness

`intro-def` and `apply-def` are checked rules, including their older
`{"kind":"trusted","rule":...}` encodings. The checker first accumulates
all explicit definition introductions and supported `def-axiom` definition
witnesses, checks the DAG using their
expanded expressions, and **only after checking the closed false root**
checks that none of the introduced function declarations occurs anywhere
in any original input assertion. The final pass includes unused input
assertions, nested terms, and quantifier bodies; it compares entire
function declarations, not textual names, so genuine overloads remain
distinct. A failed freshness check returns `REJECT`, even when ordinary
inference checking completed successfully. This also applies in strict
original-assertion mode.

`Z3Definitions.fst` supports constant definitions, universally quantified
function definitions, Boolean naming clauses (including positive-only
definitions), and the two guarded equalities defining a term ITE.
The function's arguments must be distinct bound variables covering the
definition's parameters; parameter permutations and nested binders are
supported. Equations follow Z3's `expression = name` convention; the
opposite orientation is also recognized when only that side is an
eligible defining head. Boolean/ITE definitions may quantify their
conjuncts separately, as `defined_names.cpp` does.

For `def-axiom`, supported witnesses are defining equations, complete
Boolean/term-ITE definition pairs, and two separate, complementary
guarded equalities defining the same fresh term. The pair may be
universally quantified. A lone guarded equality does not introduce a
definition or establish an arbitrary axiom. Already-checked tautologies
are not treated as introductions, so ordinary Tseitin operands do not
acquire an artificial freshness requirement.

Identical repeated introductions are idempotent. Conflicting definitions,
recursive dependency cycles, ill-sorted or unbound parameters, invalid
defining clauses, and introductions with premises are rejected. Forward
dependencies between acyclic definitions are permitted. All proof entries
are checked, including introductions outside the root's dependency cone.

The implementation uses capture-avoiding, de-Bruijn-indexed expansion,
not an additional trusted equality or a runtime solver call. An
`intro-def` fact must become a checked tautology after expansion;
`apply-def` must become a checked equality or Boolean observational
equivalence. Universal closure and guarded ITE equalities have separate
semantic proofs using standard universal-quantifier/ITE interpretation
contracts. `check_fresh_inputs` has a proved refinement: whenever it
succeeds, expansion leaves the complete original assertion list
syntactically unchanged. Thus the checked transformed derivation is a
refutation of those same inputs, without assuming definitions true in an
arbitrary unchanged interpretation.

The native dependency build and executable F* regressions pass, including
capture avoidance, cycle rejection, and freshness under binders. The
52-test Python/exporter/native suite passes, with positive ground and
quantified schemas, actual use of accumulated definitions in a refutation,
and rejection of a fabricated refutation whose original inputs are
satisfiable. An additional regression checks actual NNF-generated
`intro-def` nodes; unrelated arithmetic obligations remain explicit.

This support does not infer missing definitions from premise-free
`rewrite` leaves: the two
archived array naming obligations still require explicit definition
witnesses. General `sk`, `quant-inst`, and other quantified proof rules
have not been newly verified.

### Verified binary commutativity

`Z3Commutativity.fst` checks precisely `(op x y) = (op y x)` with the same
validated declaration on both sides, matching argument sorts, and no
premises. Supported operators are polymorphic equality (`op_eq`), Boolean
`and`/`or`, and `Int` `+`/`*` (`op_plus`/`op_mul`). Equality includes
uninterpreted, array, and Boolean operand sorts. The inference concludes
ordinary equality, never observational equivalence.

`lemma_eq_commutativity` and `lemma_commutativity_step_sound` derive the
result from standard equality/Boolean semantics.
`lemma_add_commutativity`, `lemma_mul_commutativity`, and
`lemma_arithmetic_commutativity` prove the integer cases from standard
integer evaluation, not a caller-supplied commutativity axiom. The generic
model hypothesis requires arithmetic declarations to implement integer
addition or multiplication over the shared `VInt` value representation
(with the existing interpreter's total fallback on non-integer values).
Only structural matching executes in the native checker;
it does not evaluate or multiply input numerals.

The exporter keeps unsupported commutative theories (`Real`, bit-vector
arithmetic, etc.) and non-binary shapes as explicit obligations. A document
that labels an unsupported or malformed step as checked `commutativity`
is rejected; an uninterpreted symbol or spoofed name/tag is not sufficient.

`Z3UnifiedProof.lemma_check_step_sound` covers the common inference
checker; `lemma_check_node_sound` composes it with asserted inputs,
scoped premises, hypothesis discharge, trusted definitions, and explicit rewrite/unsupported
obligations. Both distinguish equality semantics from observational
semantics. The original `proof`, `rproof`, and `oproof` types remain
available to existing standalone/legacy callers, but the full-DAG checker
no longer constructs them. Theory-specific soundness lemmas remain in
their existing modules.

Rebuild once with `fstar\tools\build_ocaml_checker.ps1`. The script now
extracts both checker roots and derives the WSL source paths from the
checkout instead of assuming `C:\z3fstar`. Its optional `-CacheDir`
reuses existing caches while still checking source/dependency freshness.
Focused tests are `Z3ResolutionProofCheckerTests.fst` and
`tools\test_extract_z3_proof.py`; set `Z3_FSTAR_CHECKER` to the native
executable to include the latter's end-to-end tests.

## What this does and does not establish

The legacy semantic theorems are conditional on interpretation contracts,
not a completed end-to-end SMT-LIB soundness theorem. In particular, the existing
global `boolean_model` ranges over untyped environments and needs a
well-sorted-valuation restriction before an inhabitance/model-construction
theorem is possible. The arithmetic report records this remaining formal
foundation gap separately from the executable certificate results.
Native datatype documents use the separate contextual typed theorem
described above, without these legacy contracts. Its verified
unsatisfiability statement concerns the checked typed interpretation;
the parser/native-view correspondence and the interpretations of
additional theories are not proved here.

This executable is only as trustworthy as the F*/Pulse verification that
produced the `.ml` files it links, **plus** the hand-written runtime
shim's faithfulness to the real `Prims`/`FStar_*`/`Pulse_Lib_*` semantics
those `.ml` files assume. The shim is small and was validated by (a)
cross-checking its `ACCEPT`/`REJECT` verdict against genuine `fstar.exe`
verification on real extracted proofs, and (b) exact-integer and oversized
reference regressions against the native checker. It is not itself a formally verified artifact —
unlike `Z3PulseProofCheckerJson.fst` itself, nothing machine-checks that
`prims.ml`'s `pow2`/`FStar_UInt.ml`'s bitvector ops/etc. actually satisfy
the specifications the Pulse-verified code was proved against; this is a
standard (and, for a code-extraction trust chain, unavoidable) gap also
present whenever F*'s own prebuilt `fstar.cmxa` runtime is used instead.

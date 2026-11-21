# Verified Checking of Z3 Proofs

[Overview](README.md) | [Formalization](FORMALIZATION.md) | [Source audits](SOURCE_AUDITS.md)

## Purpose and guarantees

This activity develops verified checkers for Z3 proof steps and
certificates using the [formalized semantics and lemmas](FORMALIZATION.md).
It is independent of source auditing: the subject is a proof supplied as
input, not the correctness of the C++ implementation that produced it.

The development includes pure proof calculi, executable Pulse checkers,
semantic rewrite recognizers, direct native proof marshaling, and a
standalone OCaml executable accepting SMT-LIB. These cover different
fragments and should not be read as a claim that every Z3 proof is fully
checked. The in-memory Pulse developments are independent of the native
CLI and are not linked into that executable.

In particular, a well-formed equational derivation is semantically sound
only when its rewrite leaves are justified. Verified matchers discharge
recognized leaves using theory lemmas. Partial checking retains unmatched
leaves as explicit obligations; clausal rules classified as `Trusted`
likewise remain obligations, not automatically proved facts. Reports state
the assumptions and rule coverage of each path. The [arithmetic certificate
report](ARITHMETIC_CERTIFICATE_REPORT.md) documents a remaining legacy
semantic-model contract inhabitance gap: the conditional semantic theorems
are not an unconditional end-to-end SMT-LIB soundness theorem. Native
datatype documents instead use the contextual, sort-indexed kernel below;
that path does not assume the legacy model contracts. For the default
kernel, `Z3CoreKernel.lemma_core_check_node_sound` proves the Boolean,
equality and congruence rules (and bounded bit-vector steps) from the
inhabited typed contract `Z3CoreModel.core_model`. Checked quantifier
instantiation is proved separately by `Z3QuantifierKernel` under an
inhabited typed quantifier contract, and quantifier introduction by
`Z3BinderKernel` for certificates of closed inputs, core rules and exact
forall/exists introductions. The binder-certificate scope guard
(`Z3UnifiedProof.binder_scoped`, structural theorems in `Z3BinderScope`)
rejects certificates whose entries are not scoped at the binder depth
where the root uses them. The remaining rules of that kernel still rest
on the legacy `Z3UnifiedProof.model_sound`, which has no model.

## Modules and architecture

`Z3OperatorTags.fst` owns the checker-internal operator vocabulary independently
of semantic carriers. `Z3ValueTheory.value` is deprecated as a foundation for
new SMT semantics: it remains available for existing unindexed interpretations
and soundness proofs, and its `op_*` names remain compatibility aliases.
New semantics should use `Z3DatatypeValue` with sort-indexed carriers, as in
`Z3TypedRoot`. This separation does not yet remove legacy proof dependencies
from the production verification closure or change checker coverage.

`Z3IndependentArrayRoot` supplies datatype-free one-dimensional array
operations over the typed root carrier and proves read-over-write,
constant-read, extensionality, and the difference-witness property. These
ghost operations are packaged as a `Z3SortedArray.family` by
`Z3IndependentArrayFamily`. The family permits ghost-valued algebra
construction, and its extensionality law is an explicit proof function
rather than a nested quantified refinement. This changes neither the law
nor the executable support check. `Z3IndependentArrayInterpretation`
constructs a standard typed-root model satisfying the sorted array model
contract by interpreting canonical supported `array-ext` declarations as
the difference witness. Other free-symbol applications are preserved.
`Z3IndependentArrayPreservation` proves that original assertions without
selected `array-ext` applications retain their truth when extending any
standard typed-root interpretation. Its executable guard checks an
occurrence budget before traversing the assertions; its proof covers
quantifiers, lambdas and datatype applications. Arbitrary root models need
not interpret `array-ext` this way. `Z3IndependentArrayReplay` proves bounded, scoped array-lemma
and rewrite checks sound in that constructed root. It uses the existing
array-syntax matchers, including their scalar-sort restrictions.
`Z3IndependentArrayDocument` exposes these checks through the opt-in
`--array-replay` route. Premise-free `th-lemma` equalities can use either
the array-clause recognizer or the bounded array-rewrite recognizer.
It augments only pending documents, bounds traversal,
and preserves the base verdict when the assertion guard or replay fails.
Its certification theorem applies to standard typed-root models; inputs
containing a selected canonical `array-ext` application are not promoted.
The route also tries definition replay after array augmentation when both
kinds of candidate occur. Definition freshness is checked against the
augmented assertions, including every selected array fact; the combined
soundness theorem retains the same standard-root and assertion-guard limits.
On the saved 25-case QF_AX cohort with a 60-second per-case limit, the
baseline had 1 certified, 22 pending and 2 timed out; array replay had
15 certified, 7 pending and 3 timed out. Fourteen previously pending cases
were certified, while one previously pending case timed out. Array replay
performs an additional root check and can therefore increase runtime.
Adding the `th-lemma` rewrite fallback preserved those 25 whole-document
outcomes; a focused nested-store control exercises the newly accepted case.
Combined array-definition replay also preserved the cohort outcomes; a
focused mixed proof requires both replays, with freshness-negative controls.

`Z3IndependentGroundDefinition` recognizes bounded, fresh
ground equalities and constructs an interpretation satisfying the equality
without changing the original inputs. `Z3IndependentGroundDefinitionRoot`
proves that this interpretation preserves typed-root laws.
`Z3IndependentGroundDocument` uses one premise-free definition as a
pending-only fallback in `--definition-replay`, with bounded selection.
Only the first premise-free definition is attempted. In a pending QF_AX
store-commutativity proof, the augmentation reduces pending obligations from
78 to 77 but does not certify the document, so its original verdict is kept.
On the 25-case QF_AX cohort, `--definition-replay` with diagnostics certified
1 case, left 21 pending and timed out on 3 at 60 seconds per case.

`Z3IndependentArrayGroundDocument` composes ground-definition replay with
array replay for the pending-only `--array-replay` fallback. The ground
override preserves the sorted array model, so array facts can mention the
fresh constant. Freshness is checked against the original assertions;
the original-assertion `array-ext` guard and the ground selection and work
bounds still apply. The previously pending store-commutativity proof above
is certified by the combined route. On the same 25-case QF_AX cohort with
`--array-replay --stats --diagnostics` and a 60-second per-case limit, the
paired prior route certified 15, left 7 pending and timed out on 3; the
combined route certified 16, left 6 pending and timed out on the same 3.
The newly certified case took 0.419 seconds versus 0.448 seconds previously.
For the 21 unchanged, non-timeout cases the median wall time was 0.796
seconds versus 0.759 seconds previously (median paired ratio 1.051); these
single runs shared the machine with other work and are not a controlled
performance comparison. On Match-5, the definition route still certified
all 52 `nnf-pos` and one `nnf-neg` outer roots in 19.32 seconds; the array
route left five binder/NNF obligations pending.

The array replay occurrence bound was subsequently raised from 4,096 to
32,768; document traversal remains bounded separately. On the same cohort
and flags, the verified checker certified 21, left 1 pending and timed out
on the same 3 cases, versus 16/6/3 with the previous bound. The five newly
certified cases took 4.39–34.67 seconds. For 17 unchanged non-timeout cases,
the median paired time ratio was 0.989; these single runs shared the machine
with other work. Match-5 definition replay remained certified with all
53 outer NNF roots nonpending in 19.13 seconds. The remaining partial swap
proof has nine obligations after array augmentation, including expressions
exceeding the new per-expression bound.

Raising the bounded replay limit to 65,536 subsequently certified that last
partial case: the same cohort produced 22 certified and the same 3 timeouts.
The newly certified proof took 10.95 seconds versus 18.84 seconds previously.
For the 21 unchanged non-timeout cases the median paired ratio was 1.006;
these single runs shared the machine with other work. Match-5 definition
replay remained certified with all 53 outer NNF roots nonpending in 19.31
seconds.

`Z3SortedProof.direct_consequence` reuses one conclusion-scope check across
its alternatives. An F* equivalence lemma checked separately confirms that
this does not change the result for any input. The paired 25-case QF_AX run
retained 22 certified cases and the same 3 timeouts; the median paired time
ratio for the 22 completed cases was 0.947. These are single runs on a shared
machine, not a controlled performance claim. The first timeout also exceeded
45 seconds on the base route: solving, marshaling and epsilon elaboration
finished promptly, while document replay remained active. Match-5 definition
replay remained certified with all 53 outer NNF roots nonpending in 18.42
seconds.

`Z3SortedProof` also carries the already-computed scope result into
propagation, recomputing it only when a constructor rewrite changes the
conclusion. A separate F* induction establishes exact equivalence with the
previous propagation decision. The paired QF_AX run again retained 22
certified cases and 3 timeouts; the median paired time ratio over completed
cases was 0.961. These single shared-machine runs do not establish a
controlled speedup. Match-5 definition replay remained certified with all
53 outer NNF roots nonpending in 18.17 seconds.

For `--array-replay --diagnostics`, `Z3IndependentChecker.check_array_diagnosed`
shares the initial document replay between the verdict and diagnostic.
Its interface proves equality with the existing array verdict and with the
CLI's previous diagnostic, including the synthetic zero-obligation
diagnostic for certified verdicts. The same pending-only augmentation and
root-coverage checks apply. On the paired 25-case QF_AX run at 60 seconds,
the result changed from 22 certified and 3 timeouts to 22 certified, 1
partial and 2 timeouts; the newly completed case was `PARTIAL 149` in
45.97 seconds. The 22 unchanged cases had a median paired time ratio of
1.010 in single shared-machine runs. With both options, `check_ms` now
includes diagnostic collection because it is combined with checking.
Match-5 definition replay remained certified with all 53 outer NNF roots
nonpending in 18.07 seconds.

An exploratory extracted checker with array expression and document-work
limits increased to 262,144 and 8,000,000 timed out at 60 seconds on the
newly completed partial case above, versus 45.97 seconds with the verified
limits. The two other previously timed-out cases also timed out at 60 seconds.
This was an unverified temporary experiment, not a change to the checker or
a controlled performance comparison; the existing limits remain.

`Z3LpGomorySyntax` owns Gomory certificates, candidate construction and
executable split checking independently of the legacy value carrier.
`Z3LpGomory` retains the existing legacy semantic soundness proofs.
`Z3FiniteFieldCertificate` provides the shared PAC certificate representation
for the legacy and sort-indexed replayers; their replay algorithms and
soundness proofs remain separate. `Z3SortedFiniteFieldTests` proves that
the two replayers agree on acceptance for every shared certificate and input.
`Z3UnifiedProofSyntax` owns unified judgments, rules, proof-node data,
classification, relation matching, reachability and hypothesis bookkeeping
as well as binder-premise replacement and Skolem-step replay without
importing legacy values. `Z3UnifiedNode` implements the default node dispatch
independently, parameterized by the existing rule, theory, and binder checks.
`Z3UnifiedProof` supplies those checks and retains their legacy semantic proofs.
`Z3RelationalReachability` proves edge/argument matching and traversal sound
over an abstract relation (reflexive for argument matching, symmetric and
transitive for traversal). The default,
scoped, and sort-indexed proofs instantiate it without changing their
executable matching or traversal.
`Z3RelationalRuleSyntax` owns the default reflexivity, symmetry, transitivity,
path, congruence and observational-iff recognizers. `Z3SortedRelational`
proves their judgments sound for scoped terms in an arbitrary sort-indexed
interpretation, including observational premises, and connects them to the
parameterized default node dispatcher. `Z3HypothesisSemantics` proves the exact
deduplicating premise-hypothesis union and conditional fact reasoning over
arbitrary valuations. Both legacy and sorted proofs use its union theorem, and
the sorted relational dispatcher proves conditional soundness of its returned
facts. `Z3SortedRelationalBridge` specializes
that theorem to the actual default checker callback and still imports the
legacy checker for that compatibility link. This proof does not add a scope
gate to the default document checker. `Z3DocumentFactSemantics` proves premise lookup and table-update
invariants independently of the carrier. `Z3SortedDocumentBridge` uses them to
prove conditional soundness and table preservation for actual checked core
entries with scoped relational conclusions; it remains a legacy-dependent
bridge and does not establish whole-document soundness.
`Z3DocumentReplaySemantics` proves that replay with zero pending obligations
preserves a sound fact table given sound entry checks. `Z3SortedLeafFacts`
proves conditional soundness for asserted and hypothesis nodes without a new
scope gate. The transitional sorted bridge handles these leaves together with
scoped relational core entries, assuming asserted inputs hold.
`Z3HypothesisSemantics` also proves hypothesis discharge over explicit
valuation laws, with a legacy adapter and an independent sort-indexed model in
`Z3SortedHypothesisSemantics`. `Z3SortedLemmaFacts` uses it for the default
lemma rule when the proposition and premise hypotheses are scoped. The
transitional replay bridge includes that rule under these proof assumptions;
the checker does not enforce them as additional acceptance gates.
`Z3SortedScopedReplay` instead maintains scoped hypotheses as a fact-table
invariant, allowing those assumptions to be derived for each checked lemma
entry rather than postulated for every possible premise table.
`Z3ModusPonensSyntax` contains the production-used ordinary and observational
modus-ponens recognizers; their parity with the former branches was proved for
all inputs before delegation. `Z3SortedModusPonens` proves their conditional
soundness for scoped judgments, and `Z3SortedScopedReplay` maintains scoped
judgments as well as scoped hypotheses to handle both rules.
`Z3SortedDefaultRoot` proves a conditional refutation theorem for the actual
prepared-document diagnostic when it reports zero pending obligations, the
inputs hold, and every entry meets the scoped replay assumptions. It also
covers the input-diagnostic stage when Skolem preparation succeeds. This is
not yet a theorem for the full preparation pipeline or for all accepted rules.
`Z3IndependentChecker.fsti` exposes the sort-indexed epsilon root gate and its
conditional refutation theorem without a dependency on `Z3ValueTheory`. This
is a prototype F* entry point; the default route and its acceptance remain
unchanged. `Z3IndependentNative` connects this gate to the independent native
proof marshaller. `tools/build_independent_checker.py` builds a separate OCaml
executable from that legacy-free closure. Its `ACCEPT` requires
`RootCertified`; uncovered fragments report `UNKNOWN`, and unsupported steps
remain `PARTIAL`. Native-to-F* marshaling remains part of the trust boundary.
The build requires F*, its checked-module cache, a matching Z3 executable and
native OCaml installation, and an OCaml environment with `ocamlfind` and
`zarith`. Run `python tools\build_independent_checker.py --help` for the
required paths and a new output directory. The resulting `checker` accepts an
SMT-LIB file or standard input; `--stats` reports phase times and proof sizes.
`--diagnostics` separately replays the sorted checker and reports bounded,
lossy obligation fingerprints; it checks that the replay agrees with the
root verdict and never changes certification. A zero-pending replay can still
be `UNKNOWN` when the root coverage gate is not satisfied.

The default independent checker now shares proof replay with diagnostics through
`Z3IndependentChecker.check_diagnosed`. Its `.fsti` contract proves equality
with both the original `check` verdict and `diagnose` result. Batch and
incremental diagnostic modes reuse that pair; array replay shares the same
base helper. Non-diagnostic checking, optional definition fallback, root
coverage and resource limits are unchanged.

A fresh serial `fstar-build` guard compared the preceding CLI with the new
CLI linked to the same 106 kernel/runtime objects and static producer archive.
Six completed pairs preserved all solver-response sequences and 38 UNSAT
verdicts. Their observed wall time fell from 57.464 s to 36.335 s (36.77%).
Ten pending `nnf-pos` and five pending `nnf-neg` outer roots remained in both
arms. A seventh reference session timed out at 60 s; the candidate completed
in 37.818 s. Its extra query tails are not semantic acceptance improvements.
These are targeted single-pair observations, not full-corpus parity or a
per-NNF-step speedup. Candidate `check_ms` includes the shared diagnostic
pass; the old CLI excluded its duplicate diagnostic pass, so wall time is
the primary comparison. Evidence is in session
`files\core-diagnostics-paired-01` and
`files\core-diagnostics-candidate-01.json`.

The independent OCaml extraction adapter also realizes
`Z3BinderScopeSyntax.name_length` directly with the existing trusted
`FStar_String.strlen`, rather than decoding a character list and counting
its cells. `Z3BinderScopeIndependent.lemma_name_length` proves the source
identity; the runtime counter uses the decoder's exact byte-step widths,
including malformed UTF-8. Scope charges, remaining work, limits and Cherry
code are unchanged. The adapter requires the exact expected extracted
binding and stops on drift. Native binder tests compare it with the original
list-based count on every two-byte string, deterministic random bytes,
malformed sequences and million-byte strings. The fresh 107-module candidate
and three replay suites passed; paired and frozen-proof measurements are
tracked in `PORTING_PROGRESS.md`. Solver-session observations alone are not
proof-identical comparisons.

Local frozen-proof controls now isolate checker changes from solver/proof
variation. Name-count realization preserved all 58 verdicts and full
diagnostics in both modes, reducing core checker time 9.58% and definition
checker time 13.69%. A separate pure fallback-order change tries the existing
definition-free binder route before the standalone Skolem route. Its original
`.fsti` verdict contract is retained and verified; it preserved all 58 frozen
results and reduced definition checking another 7.38% in its own pair.
Definition replay had zero pending roots among the same 1,295 `nnf-pos` and
48 `nnf-neg` outer roots. Two proofs remain partial for other obligations.
These captured-document measurements do not establish legacy or full-corpus
parity. Captures/replayers are local session artifacts, not a production
deserialization interface.

`Z3IndependentBooleanContext.fsti` equates its cached contextual-equivalence
result with the original Boolean normal form implementation. The native
adapter inlines that verified body without a module cycle and fails on
unexpected extraction shapes. On the same 58 frozen proofs, all 14 full-result
comparisons passed. Core checking was 44.340 versus 42.668 s; definition
checking was 103.954 versus 102.688 s. Cumulative allocation fell 5.84% and
4.01%, respectively. These are single-pair observations, not statistical
significance or new rule coverage.

`Z3IndependentCertificateFallback` addresses legacy-accepted proofs whose
local rules are checked but whose unused binder certificates fail the new
root coverage gate. Only `RootUncovered` is eligible: a certificate-pruned
document must pass the unchanged full epsilon/root checker. The `.fsti`
contract preserves pending/rejected decisions; its soundness lemma transfers
the certified result through unchanged original assertions. No scope or
supported-sort check is relaxed. The array wrapper shares this core recovery
without running its original core check twice.

`Z3IndependentRootReplay.fsti` requires exact equality with the original root
verdict and sorted-proof diagnostics. Its implementation prepares the epsilon
and dependent-definition contexts once, retaining the dependent definitions for
the coverage gate. Dependent closures are still computed only when needed;
no pending/rejection or supported-scope gate changes. On 127 identical frozen
proofs, all 18 core/definition result comparisons passed (2026-11-14 18:13 PST).
Core time was 52.630 versus 51.588 s, with 1.09% less cumulative allocation;
definition time was 110.729 versus 110.520 s, with 0.47% less allocation.
Coverage remained core 115 ACCEPT/12 PARTIAL and definition 125/2, with
2,109 positive/60 negative NNF roots and unchanged pending counts. These are
single-pair measurements, not full-corpus legacy performance parity.

`Z3IndependentScopeLookup.fsti` equates its result with the original variable
scope predicate. Index zero compares the head directly; all other indices keep
the length/index guard. The native adapter inlines the verified extracted body
and rejects changed/duplicate extraction shapes. Native tests also preserve
negative-index exceptions outside the F* `nat` domain and quantifier ordering.
No cache, global state, theory law, or acceptance gate is added.

On the same 127 frozen proofs, all 18 full-result comparisons passed
(2026-11-14 19:10 PST). Core time was 51.718 versus 51.020 s; definition time
was 110.586 versus 109.428 s, with unchanged allocation and NNF coverage.
The separate 20-proof `Heap-4` pair improved 1.46%/2.04%, core/definition.
These single-pair observations do not establish full-corpus performance parity.
The slower called-helper variants were not promoted.

`Z3IndependentCachedReplay.fsti` equates cached entry preparation, node checking,
and full diagnostics with `Z3SortedProof`. A fresh, immutable memo is threaded
only within one root-check call. Its key contains the raw entry and resolved
premise facts, with schema/assertions fixed by its type. Entries accumulate in
a list; an id index is built only for certificate recovery. Recovery still
prepares both documents and runs the full original gates, discarding the memo
if elaborated assertions differ. It does not assume certificate repair preserves
elaboration or skip original rejection/pending checks.

On 147 frozen proofs, all 20 exact comparisons passed (2026-11-14 19:49 PST).
Core time was 68.233 versus 65.036 s (-4.69%), allocation -5.50%;
definition time was 160.148 versus 158.870 s (-0.80%), allocation -2.11%.
NNF roots/pending stayed 2,785/10 positive and 70/6 negative in core,
2,785/0 and 70/1 in definition. These are single-pair predecessor comparisons,
not full-corpus legacy performance parity. The eager cache variant was not promoted.

The independent executable's basic SMT-LIB baseline used 25 UNSAT-annotated
inputs per logic from the workflow's pinned archive configuration at `z3test`
revision `b09a2011aabe656b4a4f22c3bf13c883563fa8e1`, seed
`independent-checker-b09a2011`. The selected input manifest SHA-256 is
`72cba03d2816fa47b8bb65d2dc03105b0781cb1243813846bbed1a789666cc44`.
Z3 5.4.1 used a 10 s solver timeout, 60 s whole-case timeout, 3600 s total
budget and 4096 MiB address-space limit. Outcomes are:

| Logic | Certified | Pending | Unknown | Timeout |
|---|---:|---:|---:|---:|
| AUFLIA | 13 | 11 | 1 | 0 |
| QF_AUFLIA | 8 | 14 | 0 | 3 |
| QF_AX | 1 | 22 | 0 | 2 |
| QF_IDL | 11 | 5 | 2 | 7 |
| QF_LIA | 12 | 6 | 5 | 2 |
| QF_LRA | 5 | 11 | 8 | 1 |
| QF_UF | 22 | 3 | 0 | 0 |
| QF_UFLIA | 2 | 22 | 1 | 0 |
| UFLIA | 9 | 10 | 3 | 3 |
| Total | 83 | 104 | 20 | 18 |

No cases were rejected, reported SAT, errored, or left unrun. All 20 unknowns
reported solver timeout. Certification is conditional on the root model and
coverage gate above; this is not an end-to-end SMT-LIB soundness claim.
All 104 pending cases were replayed with matching diagnostics. A coarse
duplicate-`distinct` rewrite fingerprint was the sole pending family in
eight cases; a binder-to-binder fingerprint was the sole family in nine.
These fingerprints are lossy and do not by themselves establish that the
underlying obligations share a valid proof.
`Z3SortedDistinct.fsti` and `Z3SortedDistinct.fst` now specify pairwise
distinctness over sort-indexed values and prove duplicate-argument rewrites
under an explicit distinctness model law. `Z3SortedDistinctRoot` constructs
typed-root interpretations satisfying that law and the existing root
contract, while preserving the choice of non-distinct symbols. The executable
checker does not treat an arbitrary interpretation of `distinct` as
the SMT-LIB operator.
`Z3IndependentDistinctReplay` separately augments a document with only
closed, premise-free duplicate-`distinct` rewrite equations and proves that
epsilon-root certification of the transformed document refutes the original
assertions under the distinctness model law. The standard distinct model
inhabits that law. The standalone checker's opt-in `--distinct-replay` uses
this theorem only when the original verdict is pending and transformed
replay is root-certified; all other original verdicts are preserved. Its
diagnostics follow the document actually certified, and `--stats` labels this
mode `sorted-distinct`. On the nine baseline cases whose sole diagnostic
fingerprint was a duplicate-`distinct` rewrite to false, all nine changed
from pending to certified (one QF_UF and eight QF_UFLIA); the rest of the
225-case cohort has not been remeasured with this option.

The standalone checker supports `--interactive` on stdin for incremental
SMT-LIB sessions. It checks each UNSAT proof in its original solver context;
`--diagnostics` reports per-query `nnf-pos` and `nnf-neg` root-node counts and
pending counts. These count observed proof roots, not all nested NNF steps;
rejected or interrupted queries cannot contribute complete NNF counts.

The first bounded incremental run selected all 583 sessions from
`fstar-build` at `bench` revision `583d31809e96f4b1303a899be079b262ad433ff6`;
the selection manifest SHA-256 is
`144afe29f4da1eedd76407abba6446a54b4938ee4f2821f5bb8f1dbc43c6261c`.
With the default independent route, a 10 s solver timeout, 60 s session
timeout, 3600 s total budget and 4096 MiB address-space limit, 288 sessions
completed, 21 timed out and 274 were unrun. There were no session errors,
crashes or protocol errors. The completed queries, including those emitted
before session timeouts, reported 6,973 certified proofs, 286 partial proofs,
103 unsupported-root-fragment verdicts and no rejected proofs; 174 solver
queries returned unknown. Of 78,625 observed `nnf-pos` roots, 10 were pending;
of 2,624 observed `nnf-neg` roots, 35 were pending. These counts come from
7,362 reported UNSAT proofs and exclude unreported queries and unrun tails.
They measure root-level replay, not all nested NNF steps or end-to-end
SMT-LIB soundness; the selection order also makes the attempted prefix
unrepresentative of the full corpus.

In the first query of `pulse/queries-Pulse.Checker-1.smt2`, pending Skolem
node 605 has 4,722 unfolded expression nodes: its definition is eligible, but
the 4,096-node collection cap excludes it. The 792-entry certificate of
pending `nnf-neg` node 606 is well scoped; four used closed inner Skolem
steps also exceed that cap while fitting 8,192 nodes. An exploratory replay
using an augmented, freshness-checked context and their equations reduced the
two pending obligations to zero. This was an instrumented diagnostic, not a
root certification or a checker change. A larger-budget route must preserve
the original route's verdicts and prove its own choice-extension soundness;
simply raising the shared cap could change context selection and coverage.
`Z3IndependentSkolemReplay.fsti/.fst` now provides a separate 8,192-node
closed-Skolem collection and elaboration, with the same ordering and
freshness checks and a proof that its generated equations hold in the
corresponding choice-context model. `Z3IndependentSkolemModel` proves the
combined closed and dependent choice extension preserves original assertions,
and `Z3IndependentSkolemRoot` proves root certification under the existing
root model and coverage conditions. The opt-in `--skolem-replay` route changes
only an original pending verdict to certified when this new gate succeeds;
otherwise it preserves the original verdict. It works in batch and interactive
mode, but cannot be combined with `--distinct-replay`. The native builder runs
`tools/test_independent_skolem_replay.ml` against the extracted implementation.

In a targeted replay with a 10 s solver timeout, 40 s per session, 4096 MiB
address-space limit, and diagnostics enabled, `Checker-1` and `Recursion`
each gained one certified proof and removed one pending `nnf-neg` root.
`Checker.Match-2` remained pending; `Checker.Prover-5` timed out after five
of its six previously reported UNSAT queries. The initial opt-in run took
16.6 s for `Checker-1`, versus 6.1 s in the default run, because diagnostics
repeated the certification check. Diagnostics now use the zero-obligation
result implied by certification, and the original diagnostic for all other
verdicts. A subsequent run took 7.0 s for `Checker-1`; `Checker.Prover-5`
completed in 26.4 s with one more certified proof than its default baseline.
Proofs generated in different runs can differ, so root counts and timings
are not a proof-equivalence or stable performance measurement. These four
sessions are not a corpus-wide remeasurement.

On nine basic controls (one per logic), eight verdicts matched the baseline
and one timed out at a separate 12 s whole-case limit; all 25 QF_FF verdicts
matched. Raw results are in `/home/nbjorner/z3-independent-skolem-measure-12`
and `/home/nbjorner/z3-independent-skolem-measure-14`.

The remaining `Checker.Match-2` pending proof includes open dependent Skolem
steps over the 4,096-node limit. `Z3IndependentDependentReplay.fsti/.fst`
provides a separate 8,192-node dependent-context collector with orderedness
and original-input freshness enforced in its interface. Its extracted
boundary test checks the old and new limits and rejects a nonfresh witness.
The model-extension and root-certification proofs also cover this context:
`--skolem-replay` now tries it only if the previous Skolem route is pending
and promotes the verdict only when the expanded root gate certifies. A
proof establishes preservation of all previous non-pending Skolem verdicts.

With the same 10 s solver timeout, diagnostics, and 4096 MiB memory limit,
`Checker.Match-2` reported four certified proofs rather than three certified
and one pending; its one pending `nnf-neg` root was discharged. Wall time
was 10.7 s versus 8.9 s with the preceding Skolem route. `Checker-1` and
`Recursion` remained certified; `Checker.Prover-5` retained two pending
proofs and took 35.3 s versus 26.4 s. The nine basic controls and 25 QF_FF
cases matched their immediately preceding outcomes, including one basic
whole-case timeout at 12 s. These are targeted observations, not a full
corpus remeasurement. Raw results are in
`/home/nbjorner/z3-independent-dependent-measure-15`.

The expanded dependent replay is now skipped when a short-circuit scan
establishes that all consumed dependent definitions match the original
collector. F* proves this implies identical contexts and root verdicts, and
therefore preserves the unpruned checker's verdict for every document. In two
paired runs with diagnostics, `Checker.Prover-5` took 32.5 s with the scan
versus 34.7–35.2 s without it; `Checker.Match-2` took 10.7 s in both modes.
The reported `nnf-pos` and `nnf-neg` root and pending counts matched across
these runs. The nine basic controls and 25 QF_FF cases retained their prior
outcomes, including one basic timeout at 12 s. These small, targeted
measurements are not a corpus-wide performance claim. Raw results are in
`/home/nbjorner/z3-independent-dependent-measure-17`.

The two remaining partial proofs in `Checker.Prover-5` contain eight pending
outer binder roots: seven `quant-intro` and one `nnf-pos`. Their scope guards
exhausted the original work budget. `Z3IndependentBinderReplay.fsti/.fst`
provides a separate, proved replay, initially with four times the scope-work
budget and now with eight times that budget;
the scope-demand limits and step-work budget remain unchanged. The extracted
regression exercises the old and new limits and rejects malformed,
ill-scoped, and over-budget certificates.

An optional `--skolem-replay` fallback now uses this replay on the expanded
dependent-Skolem document. It changes only premise-free binder entries that
were previously unreplayed and now replay successfully into asserted entries.
The added propositions are proved in the same choice extension as the Skolem
equations, and a root theorem refutes the original assertions. Its coverage
gate retains the original assertion, entry, and certificate-term checks; for
an elaborated binder, successful expanded replay supplies the larger-budget
scope check. The default verdict is unchanged, and the optional route changes
only pending verdicts to certified.

On `Checker.Prover-5`, a targeted incremental run certified all six reported
UNSAT proofs, versus four certified and two partial in the preceding run. The
previously pending `nnf-pos` root was certified; no `nnf-neg` roots were
pending in either run. The new run took 52.6 s versus approximately 32.5 s
previously; generated proofs can differ, so this is not a controlled
performance comparison. `Checker.Match-2` retained four certified proofs in
10.8 s. Nine basic controls and 25 QF_FF controls matched their preceding
verdicts, including one basic whole-case timeout. These are targeted results,
not a full corpus rerun. Raw results are in
`/home/nbjorner/z3-independent-binder-measure-21`; earlier diagnostics are in
`/home/nbjorner/z3-independent-quant-investigation-01`.

The binder elaboration now constructs assertions and entries in one pass.
F* proves its result identical to the earlier two-pass construction. In a
paired `Checker.Prover-5` run, the two-pass and single-pass builds took
52.1 s and 46.7 s respectively, each certifying all six proofs; the generated
last proofs had different NNF root counts. The nine basic and 25 QF_FF
controls retained their preceding verdicts. Raw results are in
`/home/nbjorner/z3-independent-binder-measure-22`.

The coverage gate now reuses the selected binder entries from elaboration,
falling back to replay when an original entry is absent from the expanded
document. F* proves its verdict identical to the previous gate for every
document. A paired `Checker.Prover-5` run took 47.5 s before and 39.5 s after
this change, with all six proofs certified and no pending NNF roots in either
run; the last generated proofs had different NNF root counts. `Checker.Match-2`
retained four certified proofs in 10.6 s. The nine basic and 25 QF_FF controls
retained their previous verdicts, including one basic whole-case timeout.
Raw results are in `/home/nbjorner/z3-independent-binder-measure-25`.

The initial QF_FF cohort used the `z3test` generator at revision
`b8d11d8edb5ebf7d8693fc58b875c6f90720c6c9`, seed
`independent-checker-b8d11d8e`, and manifest SHA-256
`d1b388eb0689fcb7e6999c65ad19ca6ed775ae4d21f1694ea498d9a0707aaa51`.
It contains five independently exhaustively checked UNSAT formulas for each
field size 2, 3, 5, 7, and 17. With the default independent route and the
same solver and per-case budgets as above, three cases were certified and
22 remained pending; none were rejected, unknown, timed out, or errored.
All 22 diagnostic replays matched their baseline verdicts. The pending
families include finite-field rewrites and theory lemmas; these fingerprints
are diagnostic only. This is a generated cohort, not a representative
SMT-LIB finite-field suite or an end-to-end soundness claim.

A separate sample of 25 QF_FF compilation benchmarks was selected from the
CAV 2023 finite-field artifact (Zenodo record 7865471): 13 `ff` and 12
`pureff` files, ranked by SHA-256 of their archive paths within each group.
On the independent field route with a 60-second whole-case limit, two proofs
were certified, one was partial with 235 pending obligations, three inputs
returned SAT, 17 returned solver-unknown, and two timed out. The partial proof
includes many finite-field rewrite obligations. The sampled artifact is not
the full SMT-LIB QF_FF population; solver-unknown and SAT results do not
measure proof-checker coverage. The inputs, hashes, selection script, and
results are under the current session's `files/qfff-cav23-*` and
`files/inspect_ff_artifact.py`.
For the partial proof, an instrumented augmentation added 348 recognized
facts and left 68 pending theory-lemma obligations; root coverage held.
This was a diagnostic replay, not a certificate. The reported 235 pending
obligations are from the unaugmented diagnostic.
The independent field route now also replays scoped, modulus-matched PAC
certificates using `Z3SortedFiniteField`'s bounded checker and soundness
theorem. On the same artifact proof, diagnostic augmentation added 370 facts
and left 46 theory lemmas pending; the actual verdict remained partial. A
synthetic refutation with a valid PAC certificate is certified, while invalid
certificates, wrong moduli, open premises, and proof premises are rejected.
All 25 artifact cases retained their original whole-case outcomes with the
same time limit; the 25 generated controls were also certified.
All 46 remaining diagnostic PAC entries in that proof contain at least one
negated certificate premise. Inverse-witness equations require an appropriate
field/invertibility guarantee, which the general modular-ring model does not
assume. The presence of negated premises alone does not establish that every
failure is caused solely by the witness restriction.
An unverified, diagnostic-only extracted-code experiment added inverse-witness
equations and matched negated premises against complementary positive
literals. It left one of the 46 obligations pending; this was not a
certificate and did not change the checked implementation. The remaining
certificate hit the 16,384 polynomial-size limit at replay node 594.
With that experimental limit raised to 32,768 it instead hit the existing
4,000,000 work limit at node 1,116 of 11,441. Raising experimental work to
16,000,000 reached node 2,858 before exhausting that bound. No limits were
changed in the verified checker.

`Z3IndependentFiniteFieldMonomial` is an off-route foundation for a compact
replay representation. It compresses adjacent equal variable indices into
runs and proves both expansion back to the original monomial and preservation
of evaluation. Its compact multiplication merges equal-variable runs and is
proved to evaluate identically to `Z3SortedFiniteField.mono_mul` on the
expanded operands; this semantic statement also holds for unordered inputs.
Its degree is exactly the sum of input degrees and its run count is at most
the sum of input run counts, even when the inputs are unordered.
An off-route metered compression is proved equal to the original compression
and uses exactly the expanded input length plus one abstract units; that
amount of fuel is necessary and sufficient for completion.
A separate fuel-metered multiplication is proved equal to that operation
on success. Its work is bounded by the combined input run counts plus one,
and that much fuel always suffices; this does not bound integer bit costs.
For sorted source monomials, compression produces strictly ordered runs.
An off-route metered ordered-run guard preserves early rejection and agrees
with the original guard. Its successful abstract work and sufficient fuel are
bounded by the run count plus one; integer bit costs are not included.
Multiplication preserves that ordering and its expansion is exactly the
existing monomial merge, not just evaluation-equivalent. Compact comparison
is proved equivalent to expanded lexicographic comparison even for unordered
runs. A separate fuel-limited comparison returns the number of recursive
calls when successful; F* proves its result matches the original comparison,
its reported calls do not exceed the fuel or the sum of input run counts plus
one, and that this latter amount of fuel always suffices. A separate metered
structural equality check has the same guarantees; merge needs both checks
because it tests equality before ordering. These bounds count calls,
not the bit complexity of index/count comparisons or subtractions; it does
not yet meter normalization or replay and is not on the production route.
Ordered runs also round-trip through expansion and compression, so
equal expansions have equal compact representations.
`Z3IndependentFiniteFieldPolynomial` uses these facts to prove that compact
addition expands to the existing `padd` result and preserves evaluation when
its input monomials have canonical runs. Its guard checks monomial runs, not
polynomial-term ordering. Metered polynomial compression composes the monomial
meter with a single fuel balance. F* proves equivalence and exact work of one
plus the expanded polynomial size plus its term count; that much fuel is
necessary and sufficient. Separate metered monomial and polynomial sortedness
checks preserve early rejection and are proved to agree with the original
checks, with sufficient fuel bounded by expanded size and term count.
Off-route input preparation composes these checks, compression, and
normalization with one fuel balance. It distinguishes fuel exhaustion from
unsorted input, agrees with the existing input preparation, and has a proved
conservative abstract-work bound. Computing that bound itself scans the
input, and native refinements still need validation. This module is also
off-route and has no replay
budget or certificate checker yet. Its separate fuel-limited addition charges
each merge call and the metered equality and ordering calls; F* proves that a
successful result equals the original addition and its reported work is
positive and at most the supplied fuel. It also proves that fuel of
`1 + terms * (3 + 2 * weight)` always suffices, where `terms` and `weight`
are the combined input term counts and compact weights. A successful merge's
reported work is also bounded by that expression even with more supplied
fuel. Both bounds hold for unordered inputs. This is a count of abstract
steps, not a bound on integer bit complexity, actual allocations, or
cumulative replay work.
An off-route metered alternating split likewise returns the original split
and uses at most the input term count plus one units; that much fuel always
suffices. Fuel-metered canonicalization composes the split, both recursive
subcalls, and the metered merge using a single decreasing balance. F* proves
that a successful result equals the original canonicalization and its
reported abstract work does not exceed the initial fuel. For `n` input terms
and compact weight `w`, `1 + n * n * (16 + 8 * w)` bounds successful work
and suffices for completion. Metered reduction uses exactly one abstract
unit per term plus one; metered normalization shares fuel between
canonicalization and reduction. F* proves its result matches normalization,
and bounds both required and successful work by the canonicalization bound
plus the input term count plus one. Replay metering remains to be proved.
An off-route normalized addition likewise composes metered merge and
normalization with one fuel balance. F* proves result equivalence and
conservative bounds on successful work and sufficient fuel based on the
combined input term counts and weights.
Its monomial scaling preserves canonical
runs and is proved to expand to the existing `scale_mono` operation and
preserve the corresponding evaluation law. A separate metered scaling
composes the metered monomial product across terms and proves equivalence and
an abstract-work bound of `1 + weight + terms * (1 + factor_runs)`, which
also suffices as fuel. An off-route normalized scaling operation composes
this with metered normalization and proves equality, cumulative work and
sufficient fuel using the input's conservative raw-result size bound.
Its normalization is also proved
to preserve canonical runs, expand exactly to the existing normalization,
and preserve polynomial evaluation modulo the positive modulus.
Raw addition has at most the combined input term/run weight and term count,
and preserves a common degree bound. Raw scaling preserves term count,
increases weight by at most input term count times factor run count, and
increases each degree by the factor's degree. These structural bounds do not
require canonical inputs. Canonicalization and normalization cannot increase
term count or compact weight and preserve any input degree bound; the
canonicalization proof applies the same bounds recursively to its split
subinputs.
Separate strict polynomial-term predicates now distinguish adjacent term order
(`terms_ordered`) from canonical runs inside each monomial. Monomial comparison
is proved irreflexive and transitive, and total on distinct canonical compact
representations. Strict term order implies that the head precedes every later
term; merging two ordered polynomials with canonical runs preserves it.
Reduction preserves strict term order, and canonicalization and normalization
produce strictly ordered terms when their input monomial runs are canonical.
The exact identity `terms_ordered q ==> canon q == q` is proved through the
alternating split and merge, without requiring canonical monomial runs.
These contracts are exposed in `.fsti` files. They do not yet enable a
normalization fast path or change any production route or fuel policy.
Scaling must not assume this invariant: lexicographic monomial order is not
multiplicative. For example, `[] < [0]`, but multiplication by `[1]` gives
`[1] > [0;1]`. A later optimization must recheck term order or retain sorting
after scaling, rather than importing an invalid preservation assumption.
Strict bounded F* verification passed for both revised interface/implementation
pairs and seven affected compact proof clients through the certificate checker.
Extracted native polynomial, metered-state and metered-PAC suites passed.
The polynomial controls distinguish duplicate terms from duplicate monomial
runs, exercise proper prefixes and huge compact exponents, compare term order
against expanded lexicographic order, and check the new merge/reduction/
canonicalization properties on the existing randomized cases.
Solver/model/help and Python smoke checks passed; the scope suite ran
18 tests with seven skips. Optional checker integration tests were skipped
without a configured independent binary. No fresh cohort coverage gain or
full independent-build success is claimed for this proof-foundation stage.
An off-route strict term-order meter now checks adjacent monomials with the
metered comparator and rejects disorder without scanning the remaining tail.
It charges each guard call and comparator call, agrees with `terms_ordered`,
and proves positive work at most the supplied fuel. A conservative sufficient
and successful-work bound is `G(q) = 1 + terms * (2 + 2 * compact_weight q)`.
The guard itself does not compute this bound or prescan the polynomial.
`guarded_normalize_metered` shares fuel between this guard and either direct
metered reduction, when ordered, or the original metered normalization,
otherwise. F* proves exact normalization equivalence for arbitrary well-typed
compact inputs, including noncanonical monomial runs, and bounds work and
sufficient fuel by `G(q) + canon_work_bound terms weight + terms + 1`.
On ordered inputs, successful work is at most `G(q) + terms + 1`.
These conservative abstract bounds do not bound bigint bit complexity,
actual allocations or native input validation.
On the deterministic ordered 256-term native control, the new operation used
768 abstract units versus 7,681 for the old normalization, with identical
output. This is a primitive work-count comparison, not a document ACCEPT,
artifact replay result or wall-clock speedup. Production wiring and fuel
limits are unchanged; arithmetic/state/PAC composition remains the next step.
The revised interface/implementation and seven affected compact client pairs
passed strict bounded F* verification. Native polynomial and metered-state
suites passed before the combined build/test command reached its 240-second
limit; the remaining PAC-only suite then passed using completed build objects.
New controls check exact fuel boundaries, extra-fuel stability, branch/work
accounting, early disorder rejection, duplicate cancellation, malformed runs,
scaling's order reversal, huge coefficients/exponents, moduli 1/2/7/17, and
200 randomized raw/canonical input pairs. The scope suite ran 18 tests with
seven skips; solver/model/help and Python smoke checks passed.
Separate off-route metered addition, scaling and input-preparation helpers now
compose guarded normalization with one cumulative fuel balance. Their contracts
retain the original normalized results, semantic input rejection, positive
work accounting and conservative sufficient-fuel bounds. Each bound adds the
guard's term/weight bound to the corresponding existing arithmetic bound,
using the proved raw-result size bounds rather than performing a runtime
pre-scan. Input preparation still rejects unsorted monomial inputs before
compression; scaling still permits the sorting fallback when term order changes.
The existing arithmetic APIs and production routes/limits remain unchanged.
Experimental compact state/PAC propagation is described below; isolated
artifact measurement remains separate.
The revised interface/implementation and seven compact client pairs passed
strict bounded F* verification. The extracted polynomial suite passed its
existing 10,000 randomized cases plus composed-operation controls for exact
fuel boundaries, extra-fuel stability, raw/normalization work sharing,
early input rejection, cancellation, malformed runs, order-reversing scaling,
huge coefficients/exponents and 200 randomized operand/input sets.
On the deterministic ordered 128+128-term addition control, the new helper
used 1,534 abstract units versus 8,447 for the original helper, with identical
output. This is not a wall-clock, artifact-replay or document-coverage result.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smoke checks passed. No production API or fuel policy was switched.
The experimental compact metered state's input, addition and scaling now
use those guarded helpers, including the corresponding bounds and proof
lemmas. Existing PAC handlers and cumulative replay inherit the change through
their shared state operations; no parallel replay implementation was added.
Strict F* verification passed for the state, metered PAC and compact certificate
interface/implementation pairs. The `.fsti` contracts remain API-compatible:
they still prove reference-result equivalence, shared fuel, work bounds and
semantic-invariant preservation. Experimental consumed-fuel counts intentionally
change; unmetered references, production routes and production limits do not.
Native state controls now require the exact sum of guarded preparation/arithmetic,
lookup and insertion work, rather than only testing an insufficient insertion
budget. A new ordered two-node PAC control checks cumulative fuel and support
retention alongside the existing mixed/random and long replay controls.
Both native state and PAC suites passed, including the 12,000-node replay
control. The ordered two-node PAC control completed in 3,003 abstract units,
with exact cumulative-fuel and one-less-fuel rejection checks and unchanged
support. This is a native replay control, not an artifact or document verdict.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smoke checks passed. The pre-guard 64-million-unit artifact exhaustion remains
historical evidence.

The subsequent guarded artifact run completed all 11,441 PAC nodes in
23,658,640 abstract units and 1.330 seconds. It matched the unmetered replay's
entire result state, observed the unit root and used all 37 support indices.
The same run's checked-prime compact certificate succeeded in 3.034 seconds
and unmetered reference replay succeeded in 2.737 seconds. The 64,000,000-unit
cap, 110-second external timeout, 4,500,000-KiB virtual-memory limit,
65,536-KiB stack limit and nice level 10 were unchanged. Full-harness time
was 11.38 seconds with 424,736-KiB peak RSS, including solving, marshaling
and baseline checks; these are not replay-only memory or controlled speedup
measurements. The pre-guard replay exhausted its budget at node 4024.

The isolated native harness was rebuilt from 51 dependency-closure modules,
retaining specialized document-bridge index helpers while updating the
Fermat, independent-index, monomial, polynomial and metered-state modules.
Post-run validation checked the benchmark and source hashes, baseline
success, cumulative budget, full-state equality, unit root and support use.
Session evidence is retained in `guarded-artifact-64m-01.txt`,
`guarded-artifact-64m-01.json` and
`guarded-artifact-harness-01\source-manifest.json`.
This is not a full-document `ACCEPT`: production remains `PARTIAL 235`,
the guarded route is still off production, and native input/resource and
certificate setup/finality safeguards remain integration prerequisites.

On 2026-11-14, the metered PAC module added `unit_root_metered`,
`all_used_metered` and `finalize_metered`, with explicit `.fsti` contracts.
Successful calls equal the original unit-root/support predicates, consume
positive work no greater than their fuel, and satisfy conservative sufficient
work bounds; `None` denotes exhaustion, not a false predicate or document
verdict. Root/support indices are checked before entering nat-indexed trie
lookups. Nonpositive native fuel returns exhaustion, while invalid indices
return a metered false result. The support scan is tail-recursive, short-circuits
at the first invalid/missing/false entry and charges list guards and actual
trie lookup work. Combined finalization spends root work before scanning
support with the remaining fuel; an invalid root skips support entirely.
Bounds are ghost-only and do not add an executable support/key pre-scan.
The core replay interface publishes the unit-root characterization needed
for the cross-module equivalence proof; its runtime predicate is unchanged.

Verification and native validation were completed by 2026-11-14 11:35:49
PST (UTC-08:00). Strict F* checks passed for the core replay, metered state,
PAC, metered PAC and compact certificate interface/implementation pairs.
Native PAC/finality and certificate suites passed from fresh, separate
26-module and 30-module extraction closures. New controls cover reference
equality, exact/one-less cumulative fuel, negative native fuel/indices,
missing/false support, large keys, constant-polynomial shape, early rejection,
and 12,000 support indices; existing randomized and 12,000-node replay
controls remain. The scope suite ran 18 tests with seven skips; solver,
model, help and Python smokes passed. Python required explicitly selecting
the checkout's compatible DLL instead of the default DLL missing an API.

At that stage these were finality primitives, not yet a shared-budget certificate API.
They do not validate support declaration order or replace setup checks, and
do not bound bigint comparison, native parsing, allocation or prime evidence.
The guarded artifact result above predates these additions and does not
include their work in its replay budget. Production routes, acceptance and
limits are unchanged.

The initial version of
`Z3IndependentFiniteFieldCompactCertificate.check_for_prime_metered`
composed replay and finality under one fuel budget, with an explicit `.fsti`.
It requires the same already-prime modulus as `check_for_prime`; it is not
an untrusted native prime-evidence entry point. Nonpositive native fuel
returns `None` before setup. In that version, positive fuel reserves one admission unit;
setup rejection returns `Some (false, 1)`, failed replay returns false with
its spent work, and successful replay passes only the remaining fuel to
finalization. Empty replay still pays for finality. Exhaustion is distinct
from a completed false result.

The strict F* contracts prove that every completed result equals
`check_for_prime`, its positive work fits both supplied fuel and the ghost
`check_for_prime_bound`, and exhaustion implies fuel below that sufficient
bound. The soundness lemma reuses the existing certificate theorem without
weakening its prime, scoping or Boolean-conclusion preconditions.
The sufficient bound is ghost-only, including its reference replay; execution
does not perform that reference replay or a bound pre-scan.

That version budgets replay/finality, **not the full certificate cost**.
The admission unit does not bound premise/node length scans, modulus discovery,
`Witness.bind`, equation/support indexing or clause extraction. Prime evidence,
bigint bit costs, parsing and actual allocation remain outside this work model.
Existing `check`, `check_with_evidence` and `check_for_prime` behavior and
production routes/limits remain unchanged. Earlier artifact/cohort results
above predate this composed API; its later isolated measurement is below.

Validation completed at 2026-11-14 11:43:35 PST (UTC-08:00): the revised
certificate `.fsti`/`.fst` pair passed strict verification and extraction,
and its native suite passed from a fresh 33-module dependency closure.
Controls compare completed results with the existing already-prime checker
for primes 5, 263 and 65,537; test exact/one-less fuel and independent
replay/finality work decomposition; and cover invalid roots/support,
unrelated conclusions, failed/empty replay, wrong modulus and premise/node
limits. Empty replay returns false with two units (admission plus finality),
while one unit exhausts; a rejected replay spends no finality work.
Existing checked-evidence/composite-modulus controls also passed.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
model smokes passed. At that stage an evidence-checked metered entry point
and measurement of the composed artifact path remained next steps.

The first version of `check_with_evidence_metered` discovers the modulus and uses the existing
`Witness.prime_with_evidence` gate before calling the already-prime metered
helper. Native callers do not supply a prime-refined argument. The explicit
`.fsti` proves completed-result equality with `check_with_evidence`, positive
work within the caller's fuel and a ghost sufficient bound, and the original
scoped Boolean-conclusion soundness theorem. Nonpositive native fuel returns
exhaustion before inspecting evidence or certificate setup. A rejected
header/modulus/evidence returns false with one admission unit; a successful
gate reserves that unit and passes only remaining fuel to the existing
certificate helper, adding its spent work. Valid small primes retain the
reference behavior of ignoring unnecessary evidence.

The additional admission unit is not a bound on evidence checking.
Primality, setup, parsing, bigint bit complexity and allocation remain
unmetered; external limits and further safeguards are still necessary.
Existing APIs and production paths remain unchanged.

Validation completed at 2026-11-14 11:52:19 PST (UTC-08:00): strict
certificate interface/implementation and extraction verification passed,
as did the fresh 33-module native certificate suite. New controls cover
small primes without evidence, a large prime with checked Lucas evidence,
missing/incomplete/invalid evidence, composite and nonpositive moduli,
irrelevant evidence on small primes, invalid roots/support, failed/empty
replay, unsupported modulus shape and premise/node limits. All completed
results match the original evidence-checked checker; exact/one-less fuel
and gate-plus-certificate work decomposition pass, including negative
native fuel and early gate rejection. Existing certificate controls remain.
The scope suite ran 18 tests with seven skips; solver/model/help and
Python model smokes passed. Production paths and limits are unchanged.

On 2026-11-14 at 12:01:40 PST (UTC-08:00), the isolated evidence-checked
certificate API completed entry 1332's 11,441 PAC nodes with a true result
in 1.463 seconds and 23,658,874 abstract units. Independent controls checked
the exact decomposition: 23,658,640 replay units, 232 finality units and two
admission units. The metered replay's entire state matched the unmetered
reference, its root was a unit and all 37 support indices were used. The
same run's baseline checked-evidence certificate succeeded in 2.935 seconds,
unmetered replay in 2.674 seconds and metered replay control in 1.340 seconds.

The 64,000,000-unit cap, 110-second external timeout, 4,500,000-KiB virtual
memory, 65,536-KiB stack and nice level 10 were unchanged. The composed API's
elapsed interval includes its modulus/evidence/setup work, but abstract fuel
does not bound those costs. Whole-harness wall time was 12.85 seconds with
616,996-KiB peak RSS, including solving, marshaling, baseline checks and the
independent replay/finality controls. These single-run observations are not
API-only memory or a controlled speedup measurement.

The fresh 51-module native build retained the bridge's specialized index
extraction while overlaying seven current runtime modules. Post-run validation
checked benchmark, all harness-source/script and relevant F* source hashes,
and recorded the executable hash alongside exact-work and soundness-precondition
controls. Session evidence: `evidence-artifact-64m-01.txt`,
`evidence-artifact-64m-01.json` and
`evidence-artifact-harness-01\source-manifest.json`.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smokes passed. No F* implementation changed in this measurement stage.
This is **not** a full-document `ACCEPT`; production remains `PARTIAL 235`.
This measurement predates bounded header admission and its revised fuel
accounting; it does not measure the current admission-aware implementation.
The later source-hashed admission-aware measurement is recorded below.

The admission-aware `check_with_evidence_metered` now reserves its outer gate
unit and runs `admit_header_metered` before modulus discovery or evidence
checking. The explicit interface exposes a tail-recursive
`count_at_most_metered`: a completed count returns the exact length when it
fits, or semantic rejection when it exceeds the cap. Negative caps reject;
nonpositive native fuel exhausts. Its exact abstract work is
`1 + min(length, cap)` for nonnegative caps, and one for negative caps.
It stops at the cap without traversing the rejected tail. Its bound is
ghost-only, so execution does not precompute the length.

Header admission first counts premises up to 4,096. Empty or oversized
premises reject without scanning nodes or support; otherwise nodes are counted
up to 100,000 using only the remaining fuel. Successful node counting is
followed by support counting capped at the accepted premise count; oversized
nodes skip support. Accepted headers still carry the same pair of exact
premise/node counts. The strict contracts prove the result characterization, exact
header work and exhaustion below the sufficient bound. The evidence entry
shares that work with its existing gate, already-prime helper, replay and
finality; completed verdicts remain equal to `check_with_evidence`, with the
same scoped Boolean-conclusion soundness assumptions.

This intentionally changes experimental fuel totals: valid certificates add
their header work to the former total; failed modulus/evidence checks now
pay one gate unit plus header work. Empty premises cost two units at the
evidence entry. The already-prime helper still repeats
its length checks only after the outer entry has validated their caps; the
returned header counts are not yet reused by that helper. Modulus inspection,
binding/equation-index setup, prime evidence, bigint bit complexity, parsing and actual
allocation remain outside this abstract budget. This is not a complete native
resource policy. Existing unmetered APIs and production routes are unchanged.

Strict certificate interface/implementation and extraction verification
passed by 2026-11-14 12:14:36 PST (UTC-08:00). At 12:15:51, the fresh
33-module native certificate suite passed, retaining the existing
certificate/evidence controls and adding negative/zero/exact/one-less fuel,
empty/at-cap/over-cap counts, large caps, early header rejection, 200,000-node
rejected tails and revised header/gate/certificate work decomposition.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
model smokes passed. The subsequent admission-aware artifact run is below.
Remaining support/setup/evidence/native-resource safeguards precede
production integration and the agreed paired cohort reruns.

At 2026-11-14 12:24:58 PST (UTC-08:00), the admission-aware certificate
completed the same 11,441-node artifact with checked prime evidence: true,
23,670,448 abstract units and 1.514 seconds. Its independently checked
decomposition was 23,658,640 replay + 232 finality + 11,574 header + two gate
units. The header control returned exact counts of 131 premises and 11,441
nodes. Independent metered replay took 1.370 seconds, matched the full
reference state and passed unit-root/all-support checks. Same-run unmetered
certificate and replay controls succeeded in 2.991 and 2.782 seconds.

All 51 native dependency-closure modules were compiled afresh, preserving
the bridge's specialized index helpers and overlaying seven verified runtime
modules. Post-run validation at 12:25:00 checked benchmark, live F* sources,
runtime sources and script hashes and recorded the executable hash.
The same 64,000,000-unit / 110-second / 4,500,000-KiB virtual-memory /
65,536-KiB stack / nice-10 limits were retained. Whole-harness wall time was
12.93 seconds and peak RSS 616,372 KiB, including solving, marshaling,
baseline checks and independent header/replay/finality controls. API elapsed
time includes setup/evidence work, but abstract fuel does not bound all
those costs. These single-run observations do not measure API-only memory
or establish a controlled speedup.

Session evidence: `admission-artifact-64m-01.txt`,
`admission-artifact-64m-01.json` and
`admission-artifact-harness-01\source-manifest.json`.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smokes passed. No F* implementation or production route changed during this
measurement stage. Isolated certificate true is **not** document `ACCEPT`;
production remains `PARTIAL 235`. That measurement predates support-list
admission and does not include its additional work. The later support-aware
artifact measurement is recorded below; this result remains historical.

Bounded support admission was verified and extracted on 2026-11-14 by
12:33:10 PST (UTC-08:00). The new `lemma_support_length_rejected` proves that
support longer than the premise list makes the original evidence-checked
certificate return false. Its private induction proves successful
`FF.support_tree n previous tree support` has at most `n - previous - 1`
entries: the existing support predicate requires strictly increasing
nonnegative indices below `n`. Starting at `previous = -1` gives the premise
count as a sound cap, without changing old unmetered APIs or weakening the
certificate theorem.

The evidence entry now shares fuel across premise, node and support counts
before modulus/evidence/setup. Support counting charges one plus the smaller
of its length and the accepted premise count, stops without traversing the
rejected tail, and preserves exhaustion versus completed false. It does not
validate individual indices: within-cap negative, duplicate or out-of-range
indices still reach the original setup checks. Exact header-work and
completed-verdict equivalence proofs include the new count, and ghost bounds
and proof lemmas do not introduce runtime length pre-scans. The already-prime
helper and existing unmetered APIs remain unchanged.

At 12:34:42 the fresh 33-module native certificate suite passed, retaining all
previous controls and adding empty/at-cap/over-cap support (including 4,096),
200,000-element rejected tails, early premise/node rejection before support,
negative/duplicate/out-of-range/huge indices, exact/one-less shared fuel and
nonpositive native fuel. Scope tests ran 18 cases with seven skips; solver,
model, help and Python smokes passed. Verified source and extraction hashes
are retained in `compact-support-admission-test-01\verified-sources.json`.

This changes experimental work counts, not production coverage. At that stage,
support-trie construction in the certificate path remained unmetered despite its admitted list-length
bound; modulus inspection, binding/index setup, prime evidence, bigint bit
complexity, parsing and allocation still need safeguards. The subsequent
metered support-index primitive is described below; deliberate setup-fuel
composition and a fresh source-hashed artifact rerun remain next.
Paired basic SMT-LIB, QF_FF and
`fstar-build` guards remain required before integration or legacy removal.

`support_tree_metered` now provides standalone fuel-limited support-index
construction with an explicit `.fsti`. It matches `FF.support_tree` for every
completed tree or semantic rejection, including signed `n` and `previous`.
An empty list returns the supplied tree, even for nonpositive `n`; nonempty
negative, nonincreasing or out-of-range indices reject before nat-indexed trie
insertion. Nonpositive native fuel exhausts before inspecting the list.
The private accumulator is tail-recursive and preserves unrelated existing tree entries.

Work consists of one list guard plus the actual
`Z3IndependentProofIndex.put_metered` work for each valid prefix index,
followed by one empty-list or rejecting guard. The ghost `support_tree_bound` is exact for
completed calls and sufficient for completion; exhaustion implies fuel below
that bound. Trie insertion costs its proved key depth. The strict lemma
establishes reference equality and exact positive work no greater than fuel.
Execution uses remaining fuel and accumulated work, not a length/reference
or bound pre-scan. An invalid suffix returns semantic rejection rather than
exposing the partially built tree.

Strict certificate interface/implementation verification completed at
2026-11-14 12:41:23 PST (UTC-08:00), followed by extraction at 12:42:49 and
the fresh 33-module native certificate suite at 12:44:30. Native controls
compare full reference trees/rejections, test negative/zero/exact/one-less
fuel, signed bounds/previous/indices, empty lists, duplicates, out-of-range
and 200-bit keys, prepopulated-tree preservation/updates, early rejection
before a long tail, insertion/terminal fuel sharing and 12,000 ordered support
entries. All prior certificate/evidence/admission controls remain.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smokes passed. Verified source/extraction hashes are retained in
`compact-support-setup-test-01\verified-sources.json`.

At that stage the primitive was not yet called by `check_for_prime_metered`:
support setup still used the original unmetered builder. No existing certificate
work accounting, unmetered API or production behavior changed in that stage,
and no new artifact/document measurement was claimed. The subsequent
setup-fuel composition is below. Modulus discovery, binding,
other indexing, evidence checking, bigint bit complexity, native parsing,
allocation and stack/resource safeguards remain separate obligations.

`check_for_prime_metered` now builds support through `support_tree_metered`
after its existing header/modulus checks and admission unit, before
`Witness.bind`. Invalid support returns completed false with its actual guard
and insertion work and skips binding/replay. A completed support tree passes
only remaining fuel to replay and finality. Binding rejection still pays for
completed support setup; failed replay skips finality; empty replay still
pays for support preparation and finality. The evidence entry composes this
with its existing outer gate and premise/node/support header counts.

The primitive and its unchanged interface declarations were moved ahead of
the already-prime clients to preserve F* dependency order. Ghost sufficient
bounds follow the new setup order, while runtime uses actual returned work,
not a bound/reference pre-scan. Strict proof contracts retain equality with
the old unmetered `check_for_prime`/`check_with_evidence` verdicts, work within
fuel, exhaustion below sufficient bounds and the original scoped
Boolean-conclusion soundness assumptions.

Strict certificate interface/implementation verification completed at
2026-11-14 12:50:32 PST (UTC-08:00). Fresh extraction completed at 12:52:22
and the fresh 33-module native certificate suite passed at 12:54:06.
Controls independently decompose support construction, replay and finality,
then add header and outer-gate work for the evidence entry. They cover
invalid support, binding rejection after completed support setup, failed replay
skipping finality, empty replay paying support/finality, and negative/zero/
exact/one-less cumulative fuel. In the existing one-support fixture, empty
replay returns false with five units rather than the pre-setup two.
All previous certificate/evidence/admission and standalone support controls
remain. The scope suite ran 18 cases with seven skips and solver/model/help/
Python smokes passed. Source/extraction hashes and exact compiled overlay
alignment are retained in `compact-support-fuel-test-01\verified-sources.json`.
Certificate fuel accounting intentionally changes;
unmetered APIs and production routes remain unchanged. Actual support
construction is now charged, but modulus discovery, binding, equation indexing,
clause extraction, evidence checking, bigint bit complexity, parsing,
allocation and stack/resource safeguards remain separate obligations.
A fresh source-hashed support-aware artifact was measured on
2026-11-14 at 13:03:33 PST (UTC-08:00), with post-run validation completed
at 13:03:35. The certificate returned true for all 11,441 PAC nodes using
23,670,703 abstract units in 1.567 seconds, under the unchanged
64,000,000-unit cap. Exact work was independently reconciled as:
23,658,640 replay + 232 finality + 11,612 header + 217 support construction
+ two gates. Header controls returned 131 premises, 11,441 nodes and 37
support indices. The support tree equaled `FF.support_tree`, and its work
matched a separate oracle using `Z.numbits (Z.succ key)` for insertion depth.
Replay/finality controls received only the actual remaining fuel; replay
matched the full reference state, unit root and support use.

The same-run checked unmetered certificate returned true in 3.012 seconds,
unmetered replay in 2.782 seconds and independent metered replay in 1.363
seconds. All 51 native dependency-closure modules compiled afresh from 116
pinned sources, with seven verified runtime overlays and bridge index
specializations preserved. Post-run checks revalidated the verified-source/
extraction manifest, live F* sources, runtime sources, scripts and pinned
benchmark, and recorded the executable hash.

Whole-harness time was 12.80 seconds with 616,848-KiB peak RSS, under the
unchanged 110-second timeout, 4,500,000-KiB virtual-memory limit,
65,536-KiB stack limit and nice level 10. That includes solving, marshaling,
baseline checks and independent header/support/replay/finality controls,
not just the certificate API. The API interval includes still-unmetered
setup/evidence work; abstract fuel does not bound all costs. These single-run
observations are not a controlled speedup or an API-only memory measurement.

Session evidence: `support-artifact-64m-01.txt`,
`support-artifact-64m-01.json`,
`support-artifact-harness-01\source-manifest.json` and
`compact-support-fuel-test-01\verified-sources.json`.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smokes passed. No F* implementation or production route changed in this
measurement stage. Isolated certificate true is **not** document `ACCEPT`;
production remains `PARTIAL 235`. Earlier artifact work/timing remains
explicitly pre-support history. This support-aware measurement predates
equation-index charging below and is not a measurement of that revised API.
Deliberate integrated cohort reruns remain planned.

`index_equations_metered` now matches `FF.index_equations`, including empty
lists, arbitrary signed starting indices, stopping before inspecting the tail
once the index becomes negative, descending keys and prepopulated trees.
Its tail-recursive accumulator charges one guard per reached list step plus
the actual `Index.put_metered` insertion work for each nonnegative index.
The terminal/negative-index guard costs one unit. Exhaustion returns outer
`None`; completion returns the full reference tree and exact work. No
partially constructed tree is exposed on exhaustion.

The public `.fsti` includes the ghost `index_equations_bound` and the
exact-work/reference/sufficient-fuel lemma. The ghost bound is not an
executable pre-scan. `check_for_prime_metered` calls the new primitive only
after successful support preparation and `Witness.bind`, then gives only
remaining fuel to replay/finality. Failed binding still skips indexing;
failed replay pays completed indexing but skips finality; empty replay pays
index preparation and finality. Both certificate entry points retain equality
with their unmetered verdicts, within-fuel/bound guarantees and the same
scoped Boolean-conclusion soundness assumptions.

Strict certificate interface/implementation verification completed at
2026-11-14 13:09:33 PST (UTC-08:00), fresh extraction at 13:10:44, and the
fresh 33-module native certificate suite passed at 13:12:32. The first
verification invocation lacked the repository source include and was
corrected; the initial native fixture reversed polynomial tuple fields and
was fixed before recompiling the entire native closure. Controls compare
full reference trees and independently compute insertion depth with
`Z.numbits (Z.succ key)`. They cover negative/zero/exact/one-less fuel,
negative and 200-bit indices, descending updates, prepopulated preservation,
200,000-element ignored tails, 12,000 equations and certificate
support/index/replay/finality accounting. Existing support, evidence,
admission, binding-rejection and failed/empty-replay controls remain.
The scope suite ran 18 tests with seven skips; solver/model/help and Python
smokes passed. Source/extraction hashes and exact compiled overlay alignment
are retained in `compact-equation-index-fuel-test-01\verified-sources.json`.

Certificate work accounting intentionally changes; old unmetered APIs and
production routes do not. The 23,670,703-unit / 1.567-second artifact result
is pre-equation-index history, not a current-code measurement. No revised
artifact cost/timing or document `ACCEPT` is claimed from native fixtures.
Modulus discovery, binding, clause extraction, evidence checking, bigint
bit complexity, parsing, allocation and stack/native resource safeguards
remain separate obligations. The subsequent standalone modulus traversal
is below; at that point full recognition and certificate composition were
not yet enabled.

`find_modulus_metered` and `find_modulus_args_metered` now match the
reference `FF.find_modulus` and `FF.find_modulus_args` first-result semantics.
The runtime uses a tail-recursive search with an explicit pending-list stack:
recognized parents stop before their children, children precede siblings,
empty frames resume saved siblings, and non-App nodes do not expose their
bodies to this search. A field sort alone is not recognized as modulus
evidence. The result distinguishes outer fuel exhaustion from completed
missing modulus (`Some (None, work)`).

In that initial standalone stage, each expression/recognizer visit and
empty-frame transition cost one abstract unit. Traversal stopped before
the next visit when fuel was exhausted. The later full-recognition
composition below replaces the one-unit recognizer model with actual work.
The public `.fsti` includes exact positive ghost bounds and completed-result/
work/sufficient-fuel contracts for both entry points. Private ghost weights
justify the finite explicit-stack traversal; neither weights nor bounds nor
reference searches are executable pre-scans. The runtime shares one budget
across children and siblings rather than resetting it.

The reference recognizer is `FF.modulus_of`, not a sort-only lookup.
Inspection confirmed `get_sort` simply projects the stored sort, but
the original `modulus_of` could call `operation_of`/`operation_at` with
unmetered domain repetition, sort checks, argument scans and arity calculations.
That unit accounted for one recognizer invocation, **not all work inside
it**; subsequent recognition composition is below. Bigint bit complexity
and all allocation/native costs remain separate. That standalone stage left
all certificate callers,
old APIs and certificate work accounting unchanged. Operation-declaration
recognition and then argument recognition were prerequisites before deliberate
certificate integration, completed in the later stages below.

Strict certificate interface/implementation verification completed at
2026-11-14 13:20:31 PST (UTC-08:00); fresh extraction completed at 13:22:20,
and the fresh 33-module native certificate suite passed at 13:23:27.
Controls compare full results against the original searches and compare
traversal work against a separate recursive oracle, not the runtime's
pending-stack implementation. They cover empty/missing/direct/nested
searches, parent/first-match precedence, resumed siblings, quantifier-body
skipping, unrecognized field sorts, composite/invalid numerals, nonpositive/
exact/one-less fuel, 200,000-element ignored tails, 12,000 nested
expressions and a 120,000-level input exhausted after three search steps.
Existing certificate/evidence/admission/support/index/replay/finality
controls remain. The scope suite ran 18 tests with seven skips;
solver/model/help and Python smokes passed.
Source/extraction hashes and exact compiled overlay alignment are retained
in `compact-modulus-search-test-01\verified-sources.json`.

No artifact or document was remeasured in this standalone stage. The
23,670,703-unit / 1.567-second artifact remains pre-equation-index history,
and production remains `PARTIAL 235`. No coverage improvement or document
`ACCEPT` is inferred from these native fixtures.

`domain_arity_metered` now validates a field domain and returns its arity
through one tail-recursive prefix scan. The public contract identifies its
completed result with `Some (length domain)` exactly when
`sort_list_eq domain (FF.repeat_sort p (length domain))` holds, otherwise
inner `None`. Private induction proves the pointwise/repeated-sort
equivalence. Runtime does not build the repeated list or scan length first.
Each reached domain step costs one unit, including its terminal or first
bad-sort guard; outer `None` means exhaustion.

`operation_of_metered` matches `FF.operation_of` for all declarations.
One declaration gate covers the fixed-shape parameter/tag/modulus/range
checks. Unary negation compares against a singleton domain, so oversized
domains reject without a whole-domain scan. Recognized variadic tags
share only remaining fuel with the validated-arity scan and require at
least two arguments. Unsupported tags, malformed parameters, invalid
moduli and wrong ranges skip the scan. Empty or unary variadic domains
complete false recognition rather than becoming accepted operations.
The `.fsti` includes exact positive ghost bounds and completed-result/
work/sufficient-fuel contracts for both primitives.

Comparisons target the flat `ff_sort p`; they do not recursively compare
two arbitrary sort trees. Integer/modulus bit complexity and all actual
allocation/native costs are still separate obligations. Modulus-search and
certificate callers were deliberately unchanged in that standalone stage;
subsequent recognition composition is below. Old APIs and certificate work
accounting did not change.

Strict certificate interface/implementation verification completed at
2026-11-14 13:30:39 PST (UTC-08:00), fresh extraction at 13:31:57, and the
fresh 33-module native certificate suite passed at 13:33:05. Controls
compare operation results directly with `FF.operation_of` and independently
check domain acceptance/arity and reached-prefix work. They cover all
recognized/unrecognized tags, missing/extra parameters, invalid and
composite moduli as allowed by the reference recognizer, wrong ranges,
flat/nested/wrong-field domain sorts, zero/unary/binary arity,
nonpositive/exact/one-less fuel, 200-bit values, early bad-sort/header
rejection with 200,000-element ignored tails, a 200,000-sort valid domain
scan and 12,000-argument declarations. All existing certificate and search
controls remain. The scope suite ran 18 tests with seven skips;
solver/model/help and Python smokes passed.
Source/extraction hashes and exact compiled overlay alignment are retained
in `compact-operation-declaration-test-01\verified-sources.json`.

No artifact or document was remeasured. Production remains `PARTIAL 235`;
the 23,670,703-unit / 1.567-second artifact remains pre-equation-index
history. The subsequent paired argument/operation_at stage is below.

`arguments_match_metered` now matches
`FF.args_have_sort p args && length args = length domain` by scanning
the two spines together. It checks each reached argument's stored sort
against the flat `ff_sort p`, but does not revalidate domain element
values: declaration recognition already establishes those. A first bad
sort or unequal remaining spines returns completed false without inspecting
the ignored tail. Both-empty returns true. The tail-recursive accumulator
charges one unit per reached pair or terminal/rejection guard, with no
executable length pre-scan.

`operation_at_metered` shares actual declaration work from
`operation_of_metered` with only remaining fuel for argument matching.
Rejected declarations skip arguments. Its `.fsti` proves exact positive
work, sufficient fuel and completed-result equality with `FF.operation_at`.
Exhaustion is outer `None`, distinct from completed missing recognition.
The helper uses stored sorts via constant-shape `get_sort`, not traversal
of argument bodies. Integer bit complexity and all native/allocation costs
remain separate obligations.

Strict certificate interface/implementation verification completed at
2026-11-14 13:39:08 PST (UTC-08:00), fresh extraction at 13:40:31, and the
fresh 33-module native certificate suite passed at 13:41:40.
Controls compare full results with the reference argument predicate and
`FF.operation_at`, then independently reconcile actual declaration work
with reached paired-scan steps. They cover all tags, rejected declarations,
missing/short/extra argument arity, bad-sort prefixes and ignored tails,
nonpositive/exact/one-less/shared fuel, stored quantifier/lambda sorts,
deep bodies not traversed, 200,000-element paired scans, and
12,000-argument operations. Existing certificate/declaration/search controls
remain. The scope suite ran 18 tests with seven skips; solver/model/help and
Python smokes passed. Source/extraction hashes and exact compiled overlay
alignment are retained in
`compact-operation-argument-test-01\verified-sources.json`.

That was a standalone stage. Old APIs, modulus-search/certificate callers
and certificate work accounting were unchanged; subsequent full-recognition
and explicit-stack search composition is below, before certificate discovery
integration. No artifact or
document was remeasured. Production remains `PARTIAL 235`, and the
23,670,703-unit / 1.567-second artifact remains pre-equation-index history.

`modulus_of_metered` now matches `FF.modulus_of` with exact positive work.
One fixed-shape gate probes `FF.numeral`: its parameter/domain/range checks
do not scan arbitrary list spines or two arbitrary sort trees. Valid numerals
return immediately. Non-App nodes complete missing recognition. Other Apps
pass only remaining fuel to `operation_at_metered`, which charges actual
declaration/domain and paired argument/arity work. Integer bit complexity
and all native/allocation costs remain separate.

The explicit-stack search now calls this metered recognizer instead of
unmetered `FF.modulus_of`. Recognized parents return with actual recognition
work; missing recognition gives only remaining fuel to children/siblings.
Empty-frame transitions still cost one. Updated ghost bounds and proofs
retain exact work, positive progress, sufficient fuel, first-result reference
equality and tail-recursive runtime traversal. No ghost weights/bounds or
reference searches execute as pre-scans. The earlier one-unit recognizer
model is historical, not the current search accounting.

Strict certificate interface/implementation verification completed at
2026-11-14 13:47:01 PST (UTC-08:00), fresh extraction at 13:48:26, and the
fresh 33-module native certificate suite passed at 13:49:38.
The independent oracle now accounts for numeral/declaration/argument work
plus recursive traversal, without calling the metered functions for its
expected work. Its sibling accumulator is tail-recursive for long flat
inputs. Controls cover valid/invalid numeral shapes and values, operation
tags/arity/sorts, parent/first-match precedence, rejected domain/argument
prefixes with long ignored tails, exact/one-less/nonpositive/shared fuel,
200,000 arguments, 12,000 nested expressions and a 120,000-level input
exhausted under tiny fuel. The two-argument parent fixture returns the same
modulus with eight units: one numeral gate + four declaration + three
argument units, without visiting children. This is a native control, not an
artifact or wall-clock measurement.

All existing certificate/admission/support/index/replay/finality controls
remain. The scope suite ran 18 tests with seven skips; solver/model/help
and Python smokes passed. Source/extraction hashes and exact compiled
overlay alignment are retained in
`compact-modulus-recognition-test-01\verified-sources.json`.
Certificate callers and work accounting deliberately remained unchanged in
that standalone stage. Subsequent discovery-fuel composition is below;
binding, clause extraction, prime evidence, integer bit complexity and
native resource safeguards remain separate obligations.
No artifact or document was remeasured. Production remains `PARTIAL 235`,
and the 23,670,703-unit / 1.567-second artifact remains pre-equation-index
history.

Both metered certificate clients now use `find_modulus_args_metered`
instead of executable reference discovery. The evidence entry first shares
its gate/header fuel with outer discovery, checks prime evidence only after
successful discovery, and gives only the remainder to
`check_for_prime_metered`. That helper retains its original header guards,
then charges its gate plus actual inner discovery before support construction,
binding, equation indexing, replay and finality. Both original discovery
checks remain; no bypass API was introduced. Missing/wrong moduli and rejected
evidence pay reached discovery work; invalid headers skip it.

Updated ghost bounds and proofs retain completed reference verdicts,
positive/bounded work, sufficient-fuel completion and scoped Boolean soundness.
The existing `.fsti` contracts needed no change. Final strict verification
passed at **2026-11-14 13:59:05 PST (UTC-08:00)**, extraction at 13:59:12,
and the fresh 33-module native certificate suite at 14:00:23.
Native controls reconcile gate/header + outer discovery + helper gate +
inner discovery + support + equation index + replay + finality, including
exact/one-less/nonpositive/shared fuel, wrong/missing/composite moduli,
missing/invalid evidence, invalid support, binding rejection and failed/empty
replay. A 120,000-level discovery input exhausts under tiny fuel at both
entry points without calling the unbounded reference search.

The scope suite ran 18 tests with seven skips; solver/version/model/help
and Python model smokes passed. Three source/test fingerprints and all 30
extracted/compiled overlay hashes align in
`compact-modulus-fuel-test-01\verified-sources.json`.
Comparing extracted runtime with the preceding stage confirms only the two
metered clients changed; original unmetered APIs remain unchanged.
Ghost bounds/lemmas are erased, and neither metered client calls reference
discovery. At that stage, prime evidence, binding, clause extraction, the
helper's original length pre-scans, integer bit complexity, parsing/allocation
and native safeguards remained separate obligations. This is not a complete
resource bound. That code-migration stage did not remeasure an artifact or
document; the subsequent source-hashed measurement below includes both
discovery costs and equation indexing under unchanged caps. Production
remains `PARTIAL 235`; the 23,670,703-unit / 1.567-second artifact remains
historical.

The fresh discovery/index-aware artifact run completed at **2026-11-14
14:13:14 PST (UTC-08:00)**, with post-run hash/accounting checks recorded
at 14:13:15. Entry 1332 returned true with checked 255-bit prime evidence:
all **11,441 PAC nodes** completed in **23,673,102 abstract units / 1.448 s**.
Exact work is 23,658,640 replay + 232 finality + 11,612 header +
10 outer discovery + 10 inner discovery + 217 support construction +
2,379 equation indexing + two gates. Independent recognition/traversal
oracles matched discovery results/work; the complete support tree and
288-equation index matched their reference trees, with independent
list-guard/trie-depth work checks. The full replay state, unit root and
support use matched the reference.

Five cumulative certificate phase-boundary budgets exhausted without
resetting fuel. The full certificate and equation index each completed
at exact measured work and exhausted one unit below it. All 51 closure
modules compiled afresh with warnings as errors from 116 pinned source
files and seven verified runtime overlays. Preparation validated the
baseline source hashes outside the certificate migration, preserved the
bridge-specific index helpers and retained the full monomial degree export.
Before/after checks pinned the verified F*/extraction/runtime/script and
benchmark hashes, and the executable fingerprint was recorded.

Caps stayed at 64,000,000 units, 110 seconds, 4,500,000 KiB virtual memory,
65,536 KiB stack and nice level 10. Whole-harness cost was **14.48 s /
789,472 KiB peak RSS**, including solving, marshaling, baseline checks,
independent phase controls and repeated exact/one-less certificate checks.
Same-run unmetered certificate/replay controls succeeded in 2.800/2.589
seconds; separate metered replay took 1.285 seconds. These are single-run
observations, not a controlled speedup or certificate-only memory measurement.
The earlier 23,670,703-unit / 1.567-second support-aware run predates the
new accounting. This isolated result is **not** document `ACCEPT`; production
is unchanged at `PARTIAL 235`.

Session evidence: `discovery-index-artifact-64m-01.txt`,
`discovery-index-artifact-64m-01.json` and
`discovery-index-artifact-harness-01\source-manifest.json`.
The scope suite ran 18 tests with seven skips; solver/version/model/help
and Python model smokes passed. Session `z3agent.db` benchmark run 2 stores
the isolated certificate result, API time and full measurement metadata.
A separate plain-CLI `-st` profiling attempt (run 1) timed out after
100,145 ms under a 100-second cap; memory/conflict/theory statistics are
unavailable. The modes are not a controlled comparison, and that auxiliary
timeout is not a checker cohort/document verdict or a failure of the native
artifact checks.
No checker implementation or interface changed in that measurement stage.
Its accounting predates the bounded already-prime header migration below.
Binding, clause extraction, prime
evidence, integer bit complexity, parsing/allocation and native safeguards
remain separate obligations before production integration and fresh paired
basic SMT-LIB, QF_FF and `fstar-build`/NNF cohorts.

`check_for_prime_metered` now uses existing `count_at_most_metered` for
premises and nodes, rather than executable certificate length pre-scans.
Its original nonempty/max-premise/max-node guards retain their order.
The gate and reached count work share fuel with discovery, support,
binding, equation indexing, replay and finality. Empty/oversized premises
skip nodes and discovery; oversized nodes skip discovery. No support
admission rule or new counter API was added. Existing counter definitions
and `.fsti` declarations moved before the helper without changing their
contracts or runtime bodies. The evidence entry retains its own header
admission and passes only remaining fuel to this revised helper.

Updated ghost bounds and proofs retain completed reference verdicts,
positive/bounded work, sufficient-fuel completion and scoped Boolean
soundness. Strict interface/implementation checks passed at
**2026-11-14 14:25:25 PST (UTC-08:00)**, extraction at 14:26:44 and the
fresh 33-module native certificate suite at 14:27:56. Independent phase
accounting includes both new counts. Controls cover empty/exact-cap/
oversized headers, ignored 200,000-element tails, tiny remaining fuel,
node rejection guards, wrong/missing moduli, evidence/support/binding/
replay rejection and exact/one-less/nonpositive/shared fuel. The deep
discovery fixture now budgets through completed header admission, so it
tests discovery exhaustion rather than exhaustion in the earlier counters.

The scope suite ran 18 tests with seven skips; solver/version/model/help
and Python model smokes passed. Three source/test fingerprints and all
30 extracted/compiled overlay hashes align in
`compact-prime-header-fuel-test-01\verified-sources.json`.
Runtime comparison by definition confirms only `check_for_prime_metered`
changed; all other APIs and counter bodies are unchanged despite movement.
Ghost bounds/lemmas are erased, and no executable certificate premise/node
length pre-scan remains in the helper. At that stage, derived equation/term
length scans, binding, clause extraction, prime evidence, integer bit
complexity, parsing/allocation and native safeguards remained separate obligations.
No artifact or document was remeasured. The 23,673,102-unit / 1.448-second
discovery/index-aware artifact is historical before this counting change;
production remains `PARTIAL 235`.

The helper now also meters the lengths of bound equations and terms.
Both use existing `count_at_most_metered` with actual remaining fuel as
the limit: a completed count is exact and costs length plus one; a
completed overflow rejection would require more than the available fuel
and is unreachable. Insufficient fuel therefore exhausts, not rejects.
Equation counting precedes indexing and preserves the original descending
start length minus one, including empty length/start -1. Term counting
precedes clause extraction and replay. Actual count work shares the later
index/replay/finality budget; failed support/binding still skips it.
Updated ghost bounds and proofs retain completed reference verdicts,
positive/bounded work, sufficient-fuel completion and scoped Boolean soundness.
No new counter API or public-interface change was needed.

Strict interface/implementation verification passed at **2026-11-14
14:37:28 PST (UTC-08:00)**, extraction at 14:38:22 and the fresh 33-module
native certificate suite at 14:39:38. Independent work decomposition now
includes equation-count/index/term-count phases. Controls cover empty,
singleton and 12,000-element exact counts, tiny fuel on 200,000 elements,
exact/one-less/nonpositive/shared fuel, each new phase boundary, empty/failed
replay and rejected setup/evidence. The scope suite ran 18 tests with seven
skips; solver/version/model/help and Python model smokes passed.
Three source/test fingerprints, all 30 extracted/compiled overlay hashes
and the native executable fingerprint are retained in
`compact-derived-length-fuel-test-01\verified-sources.json`.

Runtime comparison confirms only `check_for_prime_metered` changed,
with four capped counts and zero direct length calls; other APIs/counters
and the `.fsti` remain unchanged. Ghost bounds/lemmas are erased. Binding
internals, clause recognition, prime evidence, integer bit complexity,
parsing/allocation and native safeguards remain separate obligations.
The subsequent standalone primitives below bound Boolean-domain/canonical-or
recognition behind `FF.clause_literals`, preserving all metadata checks
and its unchanged-args/singleton result without traversing argument bodies.
No artifact or document was remeasured. The 23,673,102-unit / 1.448-second
artifact remains pre-header/derived-count history; production remains
`PARTIAL 235`.

Standalone `boolean_sorts_metered`, `canonical_or_metered` and
`clause_literals_metered` now have explicit `.fsti` reference, exact-positive-
work and sufficient-fuel contracts. Boolean-domain recognition uses a
tail-recursive prefix scan: each reached cons/terminal guard costs one unit;
a non-Boolean head rejects without touching its tail. Canonical-or recognition
charges a fixed gate and, only after matching name `"or"` and interpreted tag
`op_or`, the reached domain work. It retains the original range and empty-
parameter checks after domain recognition. Empty and unary domains remain
valid. Wrong names/tags skip the domain; wrong ranges do not skip earlier
domain work.

Clause extraction shares the recognizer's actual work, with no additional
wrapper unit; non-App expressions cost one unit. Canonical App arguments
are returned unchanged, including empty/mismatched lists, and other
expressions produce the original singleton. No argument/body traversal or
new arity validation is introduced. Exhaustion is outer `None`, distinct
from a completed false recognizer or completed singleton fallback.
The ghost bounds erase. Strict interface/implementation verification passed
at **2026-11-14 14:47:51 PST (UTC-08:00)** and extraction at 14:49:45.
At that standalone stage, these primitives were not yet composed into
certificate fuel; previous clients and accounting remained unchanged.

The fresh 33-module native certificate suite passed at **2026-11-14
14:50:59 PST (UTC-08:00)**. Independent reference/work controls cover
exact/one-less/nonpositive/shared fuel, malformed metadata, empty/unary/
12,000-element domains, ignored 200,000-element tails and tiny budgets.
The unchanged-arguments control returns a 200,000-element list containing
120,000-level bodies by identity within four units. No arity constraint is
added. Scope tests ran 18 cases with seven skips; solver/version/model/help
and Python model smokes passed. Source/test, 30 extraction/runtime and
executable fingerprints are in
`compact-clause-primitives-test-01\verified-sources.json`.
Runtime comparison confirms four new definitions, all prior definitions
and the other 29 extracted modules unchanged, with ghost bounds/lemmas
erased and no new reference/length pre-scans. Clause-fuel composition is
recorded below; binding, prime evidence, bigint/native/parsing/allocation safeguards
remain separate. No large artifact or document was remeasured; production
remains `PARTIAL 235`.

The already-prime metered helper now composes these primitives after
the reached exact term count and before replay. Actual clause work shares
the replay/finality budget; insufficient fuel exhausts rather than
semantically rejects. Support/binding failures skip clause extraction.
The ghost bound includes reached clause work; updated proofs retain
completed reference verdicts, positive/bounded work, sufficient-fuel
completion and scoped Boolean soundness. The evidence entry inherits
this work through its existing remaining-fuel helper call.

Strict interface/implementation checks passed at **2026-11-14
14:56:53 PST (UTC-08:00)**, extraction at 14:58:44 and the fresh
33-module native certificate suite at 14:59:57. Independent phase
accounting includes clause recognition, with before/after boundaries,
exact/one-less/nonpositive/shared fuel, original metadata/arity behavior,
non-App conclusions, empty/failed replay and rejected setup. Controls
include 12,000-element domains, tiny fuel on 200,000-element domains,
rejected prefixes and ignored deep argument lists; failed support/binding
skips the large clauses. Scope tests ran 18 cases/seven skips;
solver/version/model/help and Python model smokes passed.

`compact-clause-fuel-test-01\verified-sources.json` retains three source/test,
30 extraction/runtime and executable fingerprints. Runtime comparison
confirms only `check_for_prime_metered` changed; 25 other definitions,
29 other extracted modules and the explicit public interface are unchanged.
The helper has one metered clause call and four existing capped counts,
with no reference clause call/direct lengths; ghost bounds/lemmas erase.
Binding internals, prime evidence, bigint/native/parsing/allocation
safeguards remain separate obligations. Bounded encoding allocation was
queued next and is recorded below. No artifact or document was
remeasured; 23,673,102 units / 1.448 s remains historical before
header/derived/clause accounting, and production remains `PARTIAL 235`.

Standalone `allocate_metered` now agrees with `FF.allocate` under explicit
`.fsti` exact-positive-work/reference/sufficient-fuel contracts. It charges
one gate, caps term counting at `max_variables - 1`, and requires accepted
append/copy work of length plus one to fit remaining fuel before copying.
Accepted work is `2 * length + 3`; oversized states reject after 4,097 units,
without scanning the ignored tail. Insufficient count/copy fuel exhausts,
not rejects. The original limit, term order/duplicates and equations/count
are preserved; no term-body, sort or additional state validation is added.
The bounded append itself is the existing list append, with at most 4,095
existing terms after admission. This is abstract spine/copy work, not a
bound on actual heap bytes, native allocation or bigint bit complexity.

Strict interface/implementation checks passed at **2026-11-14
15:05:42 PST (UTC-08:00)**, extraction at 15:06:39 and the fresh 33-module
native suite at 15:07:56. Controls cover independent reference/work oracles,
empty/small/exact-cap/rejected states, count/copy boundaries,
exact/one-less/nonpositive/shared fuel, deep terms and tiny fuel on
200,000-element spines. Scope tests ran 18 cases/seven skips;
solver/version/model/help and Python model smokes passed.
`compact-encoding-allocation-test-01\verified-sources.json` records three
source/test, 30 extraction/runtime and executable fingerprints.
Runtime comparison confirms one added allocator definition, all 26 prior
definitions and the other 29 extracted modules unchanged. Ghost
bounds/lemmas erase; the new body has one capped count, one budgeted append
and no reference allocator/direct length pre-scan.
Binding/certificate callers and accounting remain unchanged. Stack-safe
structural sort comparison was queued next and is recorded below, before
declaration/expression equality and binding composition. No artifact/document was
remeasured; production remains `PARTIAL 235`.

Standalone metered sort/list comparison now has explicit `.fsti` contracts
for reference `sort_eq`/`sort_list_eq`, Boolean structural equality, exact
positive work and sufficient-fuel completion. The native loop is
tail-recursive over paired lists with an explicit pending stack, not
recursive native sort descent. Each reached paired-node/list guard costs
one unit, including empty/pending guards. Array domains precede ranges;
sort symbols precede arguments; a mismatch skips deferred work. No sort
validity check is introduced, including empty array domains and malformed
SortApp arguments. All size/bound/reference/proof functions are ghost-only.
String/bigint/symbol scalar comparisons and native allocation remain separate
byte/bit-cost obligations.

Strict interface/implementation verification passed at **2026-11-14
15:15:11 PST (UTC-08:00)**, extraction at 15:17:01 and the fresh 33-module
native certificate suite at 15:18:19. Native controls passed independent
reference/structural/work oracles, constructor/symbol/scalar cases, list
shapes, short-circuit order, empty/12,000-element lists,
exact/one-less/nonpositive/shared fuel and ignored 200,000-element tails.
Independently constructed 120,000-level array sorts completed true at
600,003 units; a deepest-leaf mismatch completed false at 120,001 units,
skipping deferred ranges. Both exhausted one unit below exact work;
tiny-fuel prefixes also passed. No unbounded reference comparison was
called on these deep trees. These are native controls, not artifact
timings or document verdicts.

Scope tests ran 18 cases/seven skips; solver/version/model/help and Python
model smokes passed. `compact-sort-comparison-test-01\verified-sources.json`
records three source/test, 30 extraction/runtime and executable hashes.
Runtime comparison confirms three added comparator definitions, all 27
prior definitions and the other 29 extracted modules unchanged; ghost
size/bound/reference/proof functions erase and no new reference/length
pre-scan executes. Binding/certificate callers and accounting remain
unchanged. Bounded declaration equality is the next prerequisite before
expression equality and binding composition. No artifact/document was
remeasured; production remains `PARTIAL 235`.

`Z3IndependentFiniteFieldBudget` checks a bound on terms plus stored runs and
a separate per-monomial degree bound, stopping when either is exhausted. It
proves this guard sound and complete for those measures, and proves that its
expanded weight equals the existing polynomial-size measure. A combined guard
also checks that each signed coefficient lies within a supplied absolute
bound, using a term-fueled scan; F* proves its soundness and completeness
alongside the structural bounds. The shared coefficient predicate also has
proofs that raw addition is bounded by the sum of its operands' bounds and
raw scaling by the product of the factor and operand bounds, including
negative coefficients. Canonicalization is proved to bound each result
coefficient by the input term count times its coefficient bound; its recursive
subresults obey the same bound for their respective inputs. Reduction is
proved to produce coefficients bounded by the positive modulus minus one.
These guards do not yet bound the cost of handling already oversized input
integers, total allocations, comparison/normalization work, or cumulative
replay work; those remain necessary before using them as a replay budget.
At the first size-limit failure in the artifact certificate,
the two operand polynomials contained 16,065 variable occurrences, including
8,460 adjacent repetitions. This observation does not establish that compact
replay will finish the certificate. No PAC replay or production limits have
changed.

A separate unverified diagnostic replay of that certificate used extracted
compact operations and an experimental run-based work measure. With a
4,000,000-unit cap it stopped at node 1,658; with 16,000,000 it stopped at
node 4,966. With a 64,000,000-unit cap it processed all 11,441 nodes, observed
a unit root and all support used, and consumed 32,383,211 units. Its first
594 polynomial results matched the existing replay, which then hit its size
limit. The completed diagnostic observed a maximum compact weight of 7,215,
degree 32 and 510-bit intermediate coefficients; one local run took 7.05 s
and 247,724 KiB peak RSS, including solving and marshaling. These work units
are not the existing replay's units. The diagnostic harness is not verified,
does not establish the full document verdict, and does not change production
limits or certify the proof.

`Z3IndependentFiniteFieldCompactStep` proves that normalized compact input,
addition and monomial scaling preserve both canonical runs and evaluation to
zero modulo a positive modulus, provided their respective input invariants
hold. The input lemma requires sorted expanded monomials; it does not prove
that encoded equations satisfy this condition. These off-route lemmas do not
establish premise or support checks, resource bounds, or certificate soundness.
`Z3IndependentFiniteFieldCompactReplay` adds an off-route indexed state and
proves that input, addition and scaling preserve canonical runs and zero
evaluation, assuming input equations evaluate to zero. A unit root is
impossible under that invariant when the modulus exceeds one. It rejects
unsorted input monomials, unordered scaling runs, and references outside the
earlier-node range. It does not yet validate premises, track support, enforce
resource bounds, or prove that encoded equations satisfy the input
preconditions. F* refinements on indices and positive run counts are erased
when extracted; a native certificate route must construct or validate these
values before calling this internal foundation.
`Z3IndependentProofIndex` supplies separate off-route fuel-metered trie
lookup and insertion. F* proves both agree with the existing index operations;
insertion uses exactly the key's trie depth, while lookup can stop early at an
empty branch. Fuel exhaustion is distinct from a missing lookup. The depth
calculation itself is unmetered, as are bigint costs, native key validation,
and allocation; compact replay does not yet use these operations.
`Z3IndependentFiniteFieldCompactMetered` composes those operations into
off-route replay-state lookup and insertion. F* proves their agreement with
the existing state operations and that inserting a canonical zero-evaluating
polynomial preserves the replay invariant. Missing or invalid references are
distinguished from exhausted fuel. Its metered input step shares fuel between
input preparation and insertion, agrees with the existing input operation,
preserves the replay invariant and distinguishes unsorted input from
exhaustion. Its metered addition shares fuel across both lookups, normalization
and insertion, and has the same equivalence and invariant guarantees. Its
sufficient-work bound is ghost-only, avoiding an executable pre-scan.
Metered scaling likewise shares fuel across run-order validation, source
lookup, normalization and insertion, with a ghost-only sufficient-work bound.
Cumulative PAC replay is not yet composed with these operations.
`Z3IndependentFiniteFieldCompactPacMetered` composes metered addition into an
off-route PAC addition step, preserving its support state and invariant. It
also meters the candidate-list traversal of the complementary-literal check,
with an exact-result proof and early exit. Expression comparisons and sort
inspection within each candidate remain unmetered. Its metered PAC input step
shares fuel across equation and support lookup, complement scanning, core
input and support insertion, with equivalence and invariant proofs.
Its metered multiplication step charges variable conversion, compact
compression and scaling under the same balance. Numeral inspection is charged
as one abstract step, but its structural and integer costs are not bounded.
An off-route tail-recursive node loop shares that balance across all nodes.
F* proves equivalence to the original replay, cumulative abstract-work and
sufficient-fuel bounds, and preservation of the replay invariant. The
sufficient bound is ghost-only and does not execute a replay pre-scan.
`Z3IndependentFiniteFieldCompactPac` adds an off-route PAC node loop:
definition inputs, supported complementary premises, addition, and
well-formed numeral/variable multiplication. It tracks used premises and
proves that each successful step and the full node loop preserve the
compact-state invariant when the indexed equations are semantically valid
and all clause literals are false.
`Z3IndependentFiniteFieldCompactCertificate` composes that loop with witness
binding, support validation, unit-root checking and prime evidence, and proves
that an accepted certificate entails its scoped Boolean conclusion. It
requires every declared support index to be used and rejects unsorted input
monomials. This complete certificate checker remains off-route: it does not
bound intermediate sizes, coefficient widths or cumulative replay work and
must not be enabled as a production route until those limits are established.

In one isolated run, the extracted compact certificate check accepted entry
1,332 of the 255-bit QF_FF artifact with verified prime evidence. The harness
also checked the scoped-premise, scoped-conclusion and Boolean-sort
preconditions. The entry has 11,441 nodes, 131 premises and 37 support
indices; the certificate check took 2.825 s, while solving, marshaling and
checking together took 5.87 s with 242,228 KiB peak RSS. The process had a
110-second timeout and a 4.5-GB virtual-memory limit. This is a single
off-route certificate result, not a full document verdict or a replay budget.
The production checker still reports `PARTIAL 235` on this artifact.

`Z3IndependentFiniteFieldPrime` supplies a bounded trial-division gate whose
successful result proves primality, and a ghost inverse-witness construction
for any modulus already proved prime. The gate accepts only moduli at most
65,536, with at most 255 trial divisors; it does not certify the 255-bit
artifact modulus. The checker build
independently tests the bounded gate.
`Z3IndependentFiniteFieldWitness` adds a prime-conditional ghost valuation:
field-term slots retain their ordinary values, while true disequality
premises obtain slots satisfying their inverse equations. It also proves
both orientations of signed-complement matching sound, and establishes
soundness of PAC term polynomials and definition equations under that
valuation. A separate binder constructs inverse equations for negative
premises, marks them with the originating premise, and proves its equation
invariant under a prime modulus. The separate replay checks this proved
primality gate, supports both signed-complement orientations, and retains
the existing PAC work limits and support checks. `Z3IndependentFiniteFieldReplay`
tries the original checker first, then this prime-gated fallback; composite
moduli retain the original behavior. A synthetic finite-field proof with a
disequality witness is certified by the field document route, where both the
original PAC and exhaustive field checkers reject it.
On the same 25 CAV 2023 artifact inputs and 60-second whole-case limit,
all verdicts matched the previous checker: two certified, one partial,
three SAT, 17 solver-unknown and two timeouts. Six saved basic controls
also retained their verdicts; 25 generated small-field controls remained
certified. The `Checker.Match-5` regression remained certified with 52
`nnf-pos` and one `nnf-neg` outer roots, all nonpending. These are bounded
samples, not coverage claims for the full input populations.
After extending the gate from 257 to 65,536, the native test compared every
integer from -10 through 65,536 against a reference primality test. The 25
artifact cases and six basic controls again matched the preceding checker;
all 25 generated small-field controls remained certified. Match-5 remained
certified with the same 52 `nnf-pos` and one `nnf-neg` outer roots, all
nonpending. The larger gate still cannot certify the artifact's 255-bit
modulus.

`Z3IndependentModPow` is an off-route foundation for future large-prime
certificates. Its exponentiation-by-squaring implementation returns the
canonical residue of `FStar.Math.Fermat.pow` for any integer base,
nonnegative exponent and positive modulus. Its separate extracted native
test compares negative and positive bases, zero and nonzero exponents,
modulus one, and 255-bit inputs against Zarith. The module does not check
primality or change the checker verdict; a certificate route must also
bound its inputs and prove the relevant primality criterion.
`Z3IndependentModOrder` adds ghost-only period reasoning: a positive
period has a least positive period, that least period divides every other
period, and for a prime modulus and nonzero base it also divides the
modulus minus one. Its concrete controls include a composite modulus, so
the general period lemmas do not assume primality. These lemmas are not a
primality test or a Lucas-certificate soundness theorem.
`Z3IndependentModDivisor` composes that result with residue transfer to a
prime divisor: when `a^e` is one modulo `n`, a period modulo any
prime divisor of `n` divides both `e` and that divisor minus one. It also
proves that coprimality of `a^v - 1` with `n` excludes that period dividing
`v`. `Z3IndependentPrimeDivisor` uses these results to prove a Lucas
criterion: if `a^(n-1)` is one modulo `n`, and `a^((n-1)/q) - 1` is
coprime to `n` for every prime divisor `q` of `n-1`, then `n` is prime.
Its ghost prime-divisor search is part of the proof, not an executable
factoring algorithm. A concrete composite control shows that the Fermat
condition alone is insufficient. No large-prime replay route is present yet.
`Z3IndependentPrimeFactors` proves that every prime divisor of a product
of primes appears in its factor list, and uses that fact to instantiate
the Lucas theorem from complete factor-list and per-factor coprimality
evidence. The proof does not itself generate or check that evidence.
`Z3IndependentCoprimePower` computes a modular power and uses verified
Euclid gcd to check the required coprimality; acceptance proves
`gcd(a^e - 1, n) = 1`, including for negative bases. Its extracted native
controls compare the result against Zarith, including 255-bit inputs.
It is not itself a bounded certificate checker or part of replay.
`Z3IndependentPrimeEvidence` now checks a complete factor list with the
Lucas criterion. It accepts moduli through `2^256`, bounds the list to
256 entries, and checks each factor with `Z3IndependentFactorPrime`: a
separate proved trial-division gate through `2^28`, using at most 16,383
trial divisors. An accepted result proves the modulus prime; extracted tests
certify 65,537 and the artifact's 255-bit modulus using its complete factor
list, and reject incomplete, malformed and composite controls. This checker
reuses the verified factor checks for adjacent repetitions while still
checking each factor's divisibility and counting it against the list bound.
On the 255-bit artifact certificate, three local runs of 500 checks took
3,291–3,318 ms before this change and 1,724–1,727 ms afterward; these are
certificate-check timings, not PAC replay timings. A paired comparison of
65,149 small complete-factor and malformed certificates produced identical
decisions. After this change all 31 basic/generated-field controls and all
25 QF_FF artifact outcomes matched their previous results. Incremental
Match-5 with definition replay remained `ACCEPT`, with 52 `nnf-pos` and one
`nnf-neg` outer roots, none pending. The evidence checker also
backs `Z3IndependentFiniteFieldWitness.check_with_evidence`, whose
soundness theorem checks the evidence against the modulus found in the PAC
premises before replay. `Z3IndependentFiniteFieldReplay.pac_with_evidence`
and its root-level soundness theorem carry this explicit evidence through PAC
replay, preserving the original PAC path for composite moduli. Extracted
controls accept witness proofs at 65,537
and at the artifact modulus with valid evidence, and reject missing,
incomplete, mismatched and composite evidence or an invalid witness root.
The evidence-aware document API checks primality once per candidate scan or
augmentation, then reuses the proved prime across PAC entries; its soundness
theorem and extracted controls include synthetic certified documents for
65,537 and the artifact modulus. The independent checker also exposes
evidence-aware verdict and diagnostic functions with a matching certification
theorem. The standalone CLI can opt in using
`--field-replay --prime-evidence BASE:FACTOR,...`; the factors must completely
factor the selected modulus minus one, including repetitions. The parser bounds
the decimal base, factor sizes and factor count, and the verified checker checks
the evidence against the modulus in the proof. Without this option, the previous
field replay path is retained. After the witness API
addition all 25 artifact cases and 31 basic and
generated-field controls matched their previous outcomes; Match-5 remained
`ACCEPT` with 52 `nnf-pos` and one `nnf-neg` outer roots, none pending. On one
local run, 100 checks of the artifact modulus certificate took 663 ms in total;
this measures the certificate check alone, not PAC replay.
The subsequent replay and root interface stage again matched all 25 artifact
cases and 31 controls, and retained the same Match-5 verdict and root counts.
The evidence-aware document stage retained these outcomes as well.
The evidence-aware checker API stage again retained all of these outcomes.
With the 255-bit certificate supplied through the CLI, all 25 artifact outcomes
still matched: two certified, one partial, three SAT, 17 solver-unknown and two
timeouts. This does not certify the remaining PAC obligations. The default CLI
also matched all 31 basic and generated-field controls; Match-5 remained
`ACCEPT` with 52 `nnf-pos` and one `nnf-neg` outer roots, none pending.
For the partial artifact proof, a separate diagnostic augmentation with the
verified evidence added 415 facts and left one PAC entry pending, compared
with 370 facts and 46 PAC entries without evidence. This intermediate result
is not a certified verdict. The remaining entry's root depends on all 11,441
PAC nodes, so pruning unreachable nodes would not reduce that replay.

`Z3IndependentFiniteFieldReplay` provides ValueTheory-free, explicitly
modulus-checked rewrite and bounded clause recognizers, with soundness proofs
conditional on the existing sorted finite-field model and its interpretation
override. An instrumented replay recognized 82 rewrite and 20 exhaustive
clause candidates across the 22 pending cases; each case had all its pending
obligations recognized, and the existing root coverage gate held for all 25
cases. These are diagnostic candidate counts, not certified proofs or changed
verdicts. The current root interpretation does not impose finite-field
operator laws. Raw results are in
`/home/nbjorner/z3-independent-qfff-investigation-01/results.json`.
`Z3IndependentFiniteFieldRoot` constructs the replay model from the bounded
typed-root field carrier for moduli greater than one, provided the field sort
is not registered as a datatype. It constructs a root interpretation and
proves that the sorted replay interpretation agrees with it on scoped
evaluation, yielding rewrite and clause soundness in that inhabited
root model. `Z3IndependentFiniteFieldDocument` conservatively turns
recognized premise-free equalities and clauses into assertions and proves
refutation of the original assertions when the augmented document is
root-certified. The opt-in `--field-replay` route selects the first modulus
in a premise-free rewrite or field-lemma entry, checks the schema and field
sort, and changes only a pending
verdict when augmented replay is root-certified. It certified all 25 QF_FF
cases, including the 22 previously pending; nine basic controls matched the
default route, including three timeout outcomes. The route cannot be combined
with the other replay options and does not change the default route. Results
are in `/home/nbjorner/z3-independent-build-26/qfff-results.json` and
`/home/nbjorner/z3-independent-build-27/basic-control-results.json`;
the final checker results are in
`/home/nbjorner/z3-independent-build-28/qfff-results.json`.

The field route's CLI diagnostics now reuse the certified verdict instead of
repeating the replay. In paired `fstar-build` runs with diagnostics, this
reduced `Checker.Prover-5` from 32.3 s to 21.7 s and `Checker.Match-2` from
9.9 s to 6.7 s. Both versions reported three certified and three partial
proofs for `Checker.Prover-5`, and three certified and one partial for
`Checker.Match-2`. The former had one pending `nnf-pos` and one pending
`nnf-neg` root in each run, although its last generated proofs had different
`nnf-pos` root counts; the latter had one pending `nnf-neg` root. These are
outer-root counts, not nested NNF steps. Raw results are in
`/home/nbjorner/z3-independent-build-28/fstar-controls`.

In a subsequent targeted `--skolem-replay` investigation,
`PulseCore.Semantics` reported 21 certified and three partial proofs. Each
partial proof had three pending `intro-def` entries and three pending
`nnf-pos` roots. The definition entries introduce unary predicates by two
quantified implication clauses; the NNF roots replace existential subterms
with those predicates. These are not unconditional tautologies in an
arbitrary interpretation. A sound replay must establish freshness, account
for the definitions, and preserve the original assertions, including when
composing with the Skolem choice extension. The diagnostic expressions are in
`/home/nbjorner/z3-independent-nnf-next-01/semantics-detail.stderr`;
this investigation did not certify the partial proofs or change the checker.

`Z3IndependentDefinitionPair.fsti/.fst` recognizes a bounded unary subset
of these paired definitions. It checks both clauses, scopedness, freshness
in the body and original inputs, and that the predicate is outside the
datatype and interpreted operators. A conditional sorted-semantics lemma
proves the pair true when the predicate agrees pointwise with its body.
`Z3IndependentDefinitionModel.fsti/.fst` constructs a single-predicate
interpretation by evaluating its body in the original interpretation. It
proves the pointwise condition, truth of the pair, preservation of fresh
expressions and original inputs, and preservation of quantifier laws. An
inhabited typed-root example checks the construction and an unrelated symbol.
`Z3IndependentDefinitionContext.fsti/.fst` composes ordered extensions,
proving all definition formulas and preserving input truth, quantifier laws,
real laws, and integer-division laws. Its newest-first gate permits
dependencies on older definitions while excluding duplicate or cyclic
definitions. `Z3IndependentDefinitionRoot.fsti/.fst` also proves preservation
of the full typed-root contract, including datatype operations. Inhabited
examples check a dependent pair, the arithmetic laws, and a datatype schema;
negative controls exercise ordering, cycles, and unsafe datatype symbols.
`Z3IndependentDefinitionSkolem.fsti/.fst` composes the definition extension
with the document's closed and dependent Skolem choice extensions. A
compatibility gate requires all Skolem witnesses fresh in all definition
formulas; under that gate the combined model preserves the original
assertions and makes the definitions, choice equations, and dependent
closures true. It also preserves the typed-root contract. An inhabited
example exercises both kinds of witness, and a predicate/witness collision
is rejected. This conservative ordering does not handle definitions that
depend on later Skolem witnesses.
`Z3IndependentDefinitionDocument.fsti/.fst` collects premise-free recognized
definition entries, checks ordering and Skolem compatibility, and replaces
those entries with assertions in a separately elaborated document. Its
refutation theorem uses the combined root model above. An extracted control
changes one pending definition to a certified document; duplicate predicates,
nonfresh predicates, and entries with premises are refused. The standalone
checker's opt-in `--definition-replay` promotes only a pending verdict when
that separate document is root-certified. Other original verdicts remain
unchanged; it cannot be combined with the other replay options.
Focused syntax controls include a nested existential and reject mismatched
clauses, self-reference, nonfresh inputs and ill-scoped bodies.
`Z3IndependentDefinitionInstance.fsti/.fst` proves that a true recognized
definition equates a predicate application with its capture-avoiding
instantiated body at any scoped argument. An inhabited nested-existential
test rejects a captured-variable mutant.
`Z3IndependentDefinitionEquivalence.fsti/.fst` extends this equality through
matching applications and quantifiers using a bounded structural matcher.
Its theorem requires the recognized definition to be true in the model;
controls reject capture, mismatched symbols and sorts, and exhausted fuel.
`Z3IndependentDefinitionContextEquivalence.fsti/.fst` lifts that theorem to
matching any one definition whose formula is true in a definition context.
`Z3IndependentDefinitionNnf.fsti/.fst` uses that theorem for a bounded
candidate check on premise-free NNF roots, proving the resulting equality
from the true definition formulas rather than trusting certificate contents.
`Z3IndependentDefinitionNnfDocument.fsti/.fst` adds those proved equations
to a separately augmented definition document and proves its root
certification refutes the original assertions. The opt-in definition route
tries this document only after its original definition-only document fails to
certify, and still promotes only a pending base verdict. An extracted
control is certified only through the new fallback; incorrect substitutions
and entries with premises remain pending.
Definition preparation shares one elaborated document and definition context
between eligibility, definition augmentation and the NNF fallback. Interface
refinements prove the prepared results equal the original transformations.
If those paths do not certify a pending document, definition replay also
tries a combined definition/Skolem document when both top-level entry kinds
occur. `Z3IndependentDefinitionSkolemReplay.fsti/.fst` composes the ordered
definition model with the larger closed Skolem replay context; its freshness
gate excludes witness collisions with definition formulas. The accompanying
document theorem proves that certification of the combined definition, NNF
and Skolem elaboration refutes the original assertions. Separately, a
definition-free document with a Skolem entry may use the verified closed
Skolem replay directly. A definition-free document may also retry the larger
dependent context when its candidate scan says the context may differ; this
includes binder-only Skolem entries. These fallbacks promote only pending
verdicts, and diagnostics use the corresponding elaborated document.
Extracted controls cover combined and definition-free dependent proofs,
nonfresh witnesses and definition/witness collisions.
When the larger dependent context may differ, or a proof contains a
`quant-intro` root, a definition-free proof can also retry binder elaboration
after dependent replay fails. This retry runs the full proof check only when
binder candidates were selected and root coverage succeeds; its certification
uses the existing binder model theorem.
An extracted mixed dependent/binder control is certified, while malformed
binders, nonfresh witnesses and previously uncovered verdicts remain unchanged.
The combined route also retries the larger dependent Skolem context when it
may differ from the original context. This includes Skolem entries nested
inside binder certificates even without a top-level `sk` entry. Its model and
document theorems use the larger context's witness-freshness checks. A
synthetic mixed proof with a dependent witness exceeding the smaller budget
is certified by this retry; nonfresh witnesses, collisions with defined
predicates and incorrect NNF substitutions are not certified.
If those routes do not certify, the combined document may also use the
verified expanded binder elaboration. Its refutation theorem establishes
that the joint definition and dependent-Skolem model satisfies the added
binder equations before checking the augmented root. This retry runs only
when at least one binder entry is selected and still promotes only pending
verdicts. Extracted mixed controls cover large dependent and binder
certificates, binder-only replay, cyclic or premise-bearing binders,
nonfresh and colliding witnesses, and incorrect NNF substitutions.
In an extracted diagnostic replay, all nine definition entries from three
partial `PulseCore.Semantics` proofs matched the recognizer, and each
three-definition context passed its ordering gate. Results are in
`/home/nbjorner/z3-independent-definition-context-01/results.txt`. This is
candidate recognition only, not a coverage measurement.

A prior paired run of the standalone checker on
`pulse/queries-PulseCore.Semantics.smt2` completed 24 queries in each mode.
Both produced 20 certified and four partial proofs, including three proofs
with nine pending `nnf-pos` roots in total. The default run observed 211
`nnf-pos` roots (9 pending) and 18 `nnf-neg` roots (1 pending); definition
replay observed 205 and 18 roots respectively, with the same pending counts.
These are observed outer roots, not all nested NNF steps; proof shapes differed
between runs. Elapsed times were 11.61 s and 12.63 s respectively in this
single pair. Raw output is under
`/home/nbjorner/z3-independent-definition-build-01/pulse-measure`.

After adding the NNF fallback, a new single paired run on the same session
completed 24 queries in each mode. Default replay certified 20 and left four
partial; definition replay certified 23 and left one partial. Observed outer
`nnf-pos` roots were 199 with nine pending by default and 213 with one
pending in definition mode; `nnf-neg` had 18 roots and one pending in each.
The three formerly partial queries 19, 21 and 22 were certified in definition
mode. Proof shapes differed, so these root counts are not a controlled
per-step comparison. Elapsed times were 12.37 s and 15.30 s; summed reported
check times were 3.26 s and 8.92 s, respectively, in this single run.
Logs are in `/home/nbjorner/z3-independent-nnf-fallback-03/pulse-measure`.
Eight of nine basic controls had matching default and definition verdicts;
both runs of the ninth exceeded the 20-second process limit. Separately, the
field replay still certified all 25 generated QF_FF controls; these are not
a representative SMT-LIB cohort. Results are in
`/home/nbjorner/z3-independent-nnf-fallback-03/control-results.json`.

Two alternating old/new pairs after sharing preparation gave elapsed times
of 15.36, 15.36 s before and 13.42, 13.57 s after. Summed reported check
times were 9.06, 8.96 s before and 7.36, 7.47 s after. Each run certified
23 of the 24 queries and left query 16 partial. Outer `nnf-pos` totals were
213 before and 222 after, with one pending in each; all runs observed 18
`nnf-neg` roots with one pending. Different proof shapes limit direct
per-step comparisons. Eight previously completed basic controls matched
between versions, including two solver timeouts; the ninth previously
exceeded the process limit and was not repeated. Raw measurements are in
`/home/nbjorner/z3-independent-nnf-prepared-02/pulse-measure` and
`/home/nbjorner/z3-independent-nnf-prepared-02/basic-comparison.json`.

In two subsequent alternating pairs, the prepared definition route certified
23 of 24 queries in 13.30 and 13.51 s; the gated Skolem fallback certified
24 of 24 in 13.14 and 13.35 s. Summed reported check times were 7.39 and
7.51 s versus 7.32 and 7.42 s, respectively. The prepared runs observed
222 `nnf-pos` roots with one pending and 18 `nnf-neg` roots with one
pending; the gated runs observed 210 and 18 roots respectively, with none
pending. A separate broad Skolem retry certified 23 of 24 in 14.60 s, with
220 `nnf-pos` roots and 18 `nnf-neg` roots, one pending for each.
Proof shapes differed between binaries, so neither the elapsed times nor
outer-root counts isolate a per-step change. In particular, the mixed
definition/Skolem variant of query 16 was not certified by that fallback.
Logs are under
`/home/nbjorner/z3-independent-nnf-skolem-gated-02/pulse-measure`.

After adding combined replay, two alternating pairs certified all 24 queries
in both versions: 13.27 and 12.67 s before, 12.97 and 12.97 s after, with
summed check times 7.29 and 7.17 s before, 7.34 and 7.28 s after. The
earlier version observed 210 and 226 `nnf-pos` outer roots, the combined
version 226 in both runs, and all observed 18 `nnf-neg` roots with none
pending. Different proof shapes limit the timing and count comparison; these
runs do not establish
whether the mixed query-16 variant is certified. A captured query-16 proof
had no definition introductions and was already certified by the prior
Skolem fallback. Six basic controls matched between versions; two prior
solver-timeout controls were not repeated. The separate field route still
certified all 25 generated QF_FF controls, which are not a representative
SMT-LIB cohort. Results are under
`/home/nbjorner/z3-independent-combined-replay-01`. The final extracted build
also certified all 24 queries in 13.42 s, observing 226 `nnf-pos` and 18
`nnf-neg` outer roots with none pending; its logs are in
`/home/nbjorner/z3-independent-combined-replay-02`.

After adding the dependent retry, two alternating Pulse pairs each certified
24 of 24 queries. Elapsed times were 13.08 and 12.79 s before, 12.89 and
12.79 s after; summed check times were 7.32 and 7.26 s before, 7.39 and
7.24 s after. Each run observed 226 `nnf-pos` and 18 `nnf-neg` outer roots
with none pending. These timings do not establish an improvement on this
session or certification of the previously observed mixed proof variant.
Six basic controls matched between versions; the separate field route
certified all 25 generated QF_FF controls, not a representative cohort.
Results are under `/home/nbjorner/z3-independent-combined-dependent-01`.

After adding combined binder replay, two alternating `PulseCore.Semantics`
pairs took 13.05 and 12.67 s before, 13.79 and 13.14 s after. The first
pair reported 24 certified UNSAT proofs and two solver-unknown results before,
versus 25 certified and one unknown after; the second reported 24 certified
and two unknown in both. The observed `nnf-pos` outer roots were 226 in both
old runs and 234 and 219 in the new runs; `nnf-neg` totals were 18 before
and 19 and 18 after, with no pending NNF roots. Solver outcomes and proof
shapes varied, so these results do not isolate a coverage or timing change.
One paired `Checker.Match-5` run remained partial with five obligations in
both versions; each observed 52 `nnf-pos` outer roots with none pending and
one pending `nnf-neg` root. Six basic controls matched; the separate field
route certified all 25 generated QF_FF controls, not a representative
cohort. Results are under `/home/nbjorner/z3-independent-combined-binder-01`.

The definition-free dependent retry certified a synthetic proof needing the
larger dependent context while rejecting a nonfresh witness. In two
alternating `PulseCore.Semantics` pairs, both versions certified 24 proofs
and reported two solver-unknown results; old times were 12.96 and 12.79 s,
new times 12.76 and 12.86 s. Old runs observed 219 `nnf-pos` outer roots,
new runs 220; each observed 18 `nnf-neg` roots, with none pending. Two
`Checker.Match-5` pairs remained partial with five obligations and one
pending `nnf-neg` root in each run, taking 14.02 and 13.90 s before versus
13.80 and 13.97 s after. Proof shapes differ, and these small samples do not
establish a performance improvement. Six basic controls matched; the
separate field route certified all 25 generated QF_FF controls, not a
representative cohort. Results are under
`/home/nbjorner/z3-independent-definition-free-dependent-01`.

The definition-free dependent/binder retry certifies a synthetic mixed proof
that neither prior replay certifies. A broader initial retry left
`Checker.Match-5` partial and increased its time from 13.94--14.11 s to
19.72--19.73 s. Match-5's larger dependent context does not differ, so the
final gate skips that retry. In two alternating final pairs, Match-5 remained
partial with five obligations and one pending `nnf-neg` root, taking
13.89--13.99 s before and 13.76--13.81 s after. Both versions observed 52
`nnf-pos` roots with none pending. `PulseCore.Semantics` certified 24 proofs
and reported two solver-unknown results in every run; times were 13.03--13.10 s
before and 12.74--13.11 s after. The old runs observed 217 `nnf-pos` roots,
the new runs 194, and each observed 18 `nnf-neg` roots; none were pending.
These are outer roots from different proof shapes, not a controlled
per-inference performance comparison. Results are under
`/home/nbjorner/z3-independent-definition-free-binder-03`. Six basic
controls matched their previous verdicts; 25 generated QF_FF controls matched
on the separate field route and are not a representative cohort.

In the targeted `Checker.Match-5` proof, expanded binder elaboration selected
two entries and reduced three expanded-document obligations to one
`quant-intro` obligation. The original root coverage gate also failed on
three binder certificates, including the remaining entry; their outer
formulas were scoped and supported. That investigation did not certify the
proof. Details are in
`/home/nbjorner/z3-independent-nnf-next-01/match-coverage.stderr`.

The remaining certificate has 150 steps. Its rule checks succeed, but the
fourfold scope-work budget runs out while checking the judgment at step 126.
The eightfold bound validates the whole scope pass without changing its
typing, scope-demand, or step-work checks. With `--skolem-replay`, two
alternating Match-5 pairs now certify the proof and its pending `nnf-neg`
root: the old checker reported five pending obligations in 19.50 and 19.51 s,
while the new checker certified it in 18.04 and 18.17 s. Each run observed
52 `nnf-pos` roots and one `nnf-neg` root. In `PulseCore.Semantics`, the old runs reported 21
certified, three partial and two solver-unknown results; the new runs reported
22 certified, three partial and one solver-unknown. Times were 13.18--13.57 s
before and 13.70--13.77 s after. Since solver outcomes and proof shapes
differed, these counts do not establish a checker-coverage gain. A synthetic
wide-sort control exceeds the old bound and replays within the new one; bad
scope and oversized controls remain unreplayed. Six basic controls retained
their prior verdicts, and 25 generated QF_FF controls matched on the separate
field route; these are not representative cohorts. Results are under
`/home/nbjorner/z3-independent-binder-8x-01`.

The definition route now also tries the selected-binder check for
definition-free proofs with a `quant-intro` root, even if the dependent
context is unchanged. Two alternating Match-5 pairs changed from five pending
obligations in 13.66--13.95 s to certified in 18.76--18.87 s. The pending
`nnf-neg` root was discharged; both versions observed 52 `nnf-pos` roots and
one `nnf-neg` root. `PulseCore.Semantics` took 13.31--13.39 s before and
12.99--13.07 s after. The old runs certified 25 proofs with one solver-unknown,
while the new runs certified 24 with two solver-unknown; generated proof shapes
also differed. These paired results are not a controlled comparison of
individual inference costs. Two `Checker.Prover-5` pairs reported five
certified and one partial proof before versus six certified after, taking
38.51--38.54 s before and 41.44--41.55 s after. Both versions reported four
`nnf-neg` roots with none pending; old runs observed 95 `nnf-pos` roots and
new runs 91, also with none pending. Proof shapes differed. Six basic controls
preserved their verdicts; 25 generated QF_FF controls matched on the separate
field route, not a representative cohort. Results are under
`/home/nbjorner/z3-independent-definition-quant-binder-01`.

Definition replay now skips definition preparation when the original document
has no definition entry. A verified lemma shows that Skolem elaboration cannot
introduce such an entry, so the eligibility gate is unchanged. In two
alternating Match-5 pairs, both versions certified the proof with 52 `nnf-pos`
and one `nnf-neg` root, none pending; times were 18.65--18.78 s before and
17.72--18.10 s after. One Prover-5 pair certified all six proofs in both
versions, taking 41.89 s before and 39.27 s after; both observed 91 `nnf-pos`
and four `nnf-neg` roots, none pending. `PulseCore.Semantics` certified 24
proofs and reported two solver-unknown results in every run; times were
13.02--13.03 s before and 12.91--12.97 s after. Old runs observed 217
`nnf-pos` roots and new runs 209; each observed 18 `nnf-neg` roots, none
pending. Proof shapes differed, and these small samples do not establish a
general speedup. Six basic controls matched, as did 25 generated QF_FF
controls on the separate field route; these are not representative cohorts.
Results are under
`/home/nbjorner/z3-independent-skip-empty-definitions-01`.

`Z3ClauseProof` elaborates native clause trails using the independent document
and proof syntax, without importing the legacy semantic checker.
`Z3NativeProof` now marshals native proofs through those independent syntax
modules, including the finite-field tag interface `Z3FiniteFieldTags`, and
its dependency closure excludes `Z3ValueTheory`.
`Z3BinderScopeSyntax` owns the bounded binder scope guard, and
`Z3BinderScopeIndependent` proves its structural guarantees without the
legacy carrier. `Z3BinderScope` retains the bridge to the unified checker.
`Z3NnfReplay` uses the independent unified syntax and binder scope proofs;
its replay and sort-indexed soundness no longer import legacy values.
`Z3DocumentSyntax` contains document records, rule-name recognition and the
ground-table, expression well-formedness, assertion-scope and logical-declaration
guards independently of legacy values.
`Z3DocumentPreparation` collects definitions, reconstructs fresh-bit equations,
expands binder certificates, gathers Skolems and prepares document inputs and
proof entries without the legacy carrier.
`Z3DocumentReplay` implements the default diagnostic traversal independently,
with entry checking supplied by the existing checker. Document diagnostics are
represented in the independent syntax layer; the sorted checker no longer
imports the legacy unified or document checker.
`Z3TheoryNormalizeSyntax` isolates constructor replacement from the legacy
normalization semantics. The full `Z3SortedProof` dependency closure no longer
imports `Z3ValueTheory`; neither does the gated `Z3SortedRootDocument`
soundness proof.
`Z3DocumentScope` proves that recursively listed terms in a ground table are
scoped, independently of legacy values. The document checker retains its
existing conditional scope checks; it does not require table completeness.
`Z3DefinitionScope` proves that document-collected definitions are scoped
without importing legacy values.

`Z3ClausalSemantics.fst` states clause and unit-resolution soundness over
`expr -> GTot bool`, without a concrete value type. The legacy resolution
layer adapts `interpretation value` through a ghost Boolean valuation and
proved equivalences, preserving its original predicates and API. The sorted
datatype layer uses the same clausal membership and consequence proofs with
its sort-indexed truth valuation. No executable equality on functions or
Ghost-to-Tot conversion is introduced. Theory-specific and whole-document
legacy soundness contracts have not yet migrated.

`Z3ObservationalSemantics.fst` separates same-model observational agreement
from the concrete value domain. It accepts a ghost denotation on an explicit
expression domain; Boolean observations compare truth, while other sorts
require value identity. Recovering value identity from Boolean observations
requires Boolean completeness. `Z3ObservationalProof` proves proof-term
soundness for an abstract carrier with per-environment obligations
(`lemma_oproof_sound_at`) without importing legacy values.
`Z3ObservationalSyntax` owns the exact observational declarations and
modus-ponens recognizer, with a carrier-independent proof for its result on
an explicit expression domain. The unused concrete-value proof-term obligations
and soundness wrappers have been retired; `Z3ObservationalEquality` retains
the legacy adapters still used by production. Scoped sorted evaluation and the inhabited core kernel
use the shared relation; sorted NNF observational conclusions are connected
to their equality propositions through this bridge. This does not claim
general model-extension equivalence or remove the remaining legacy imports.

`Z3ClauseSyntax`, `Z3DatatypeSyntax`, and `Z3ExprScope` separate canonical
clause constructors, datatype recognizers, and scoped-expression predicates
from their legacy soundness contracts. The original APIs remain compatibility
aliases. The transitive verification closure of `Z3DatatypeValue`,
`Z3DatatypeSignature`, `Z3SortedInteger`, and `Z3SortedSemantics` no longer
imports `Z3ValueTheory` or its array/sequence/bit-vector value companions.
Dependency-isolation regressions check this with F* itself. Whole-document
and theory-specific legacy proofs still retain the concrete value domain;
this is not its removal from the complete checker closure.

`Z3ExprBinding` owns de Bruijn lifting and `Z3Substitution` owns
sort-preserving, capture-avoiding substitution. Their soundness lemmas
are generic over `interpretation value` for an arbitrary `Type`, including
ghost function carriers for nested arrays; they require quantifier
extensionality, not legacy Boolean or theory-model contracts.
The native instantiation and lambda checkers, typed quantifier kernel, and
sorted quantifier replay use this shared foundation. `Z3Definitions`,
`Z3QuantifierPull`, and `Z3BinderSubstitution` retain compatibility adapters;
unused-binder elimination and the other legacy theory contracts have not
migrated. Dependency guards and substitution regressions cover this boundary.
Acceptance algorithms and supported-sort gates are unchanged.

`Z3SortedQuantifier` is now transitively independent of `Z3ValueTheory`.
It uses `Z3ExprScope`, `Z3ExprBinding`, and `Z3Substitution` directly for
scoping, lifting, and explicit-variable-map instantiation, and
`Z3ClauseSyntax` for canonical Boolean declarations. `Z3Definitions` and
`Z3BooleanRewrite` retain adapters for their original syntax APIs. This
removes legacy model contracts from the typed quantifier proof closure,
not from the whole document checker or other theory-specific proofs.
`Z3SortedBinding` proves scope and evaluation preservation for general
capture-avoiding substitution, including open arguments and nested
heterogeneous binders. The sorted quantifier substitution lemma uses this
foundation; its executable instantiation acceptance gates are unchanged.
`Z3QuantifierInstantiationSyntax` owns the legacy executable recognizer;
its original soundness module re-exports it. Before the switch, an all-input
F* proof established correspondence with the old implementation.
`Z3QuantifierVacuitySyntax` similarly separates unused-binder recognition and
lowering from the legacy semantic proof in `Z3QuantifierVacuity`.
`Z3QuantifierVacuitySemantics` proves lowering and environment agreement for
arbitrary value carriers and quantifier-extensional interpretations, including
assignment equivalence when the carrier is inhabited.
`Z3QuantifierVacuityScope` proves that successful lowering preserves sorts and
scope across a compatible removal, including beneath nested binders. It relates
lowering to typed substitution and derives sorted evaluation preservation under
matching typed environments. It also proves that the complete single-binder
removal step preserves scope and sorts, and relates typed binder tuples before
and after removal.
`Z3QuantifierVacuitySorted` proves soundness of the exact removal, step, and
equivalence algorithms in sorted models, including removal of the final binder
and congruence beneath applications and quantifiers, without depending on
NNF replay. Default document
soundness still uses its original legacy proof.
`Z3QuantifierNnfSyntax` and `Z3QuantifierPullSyntax` separate the existing
quantifier dual and pull normalizer from their legacy soundness proofs; their
recognition behavior and fuel limits are unchanged.
`Z3CommutativitySyntax` likewise separates the existing commutativity
recognizer from its legacy soundness proof. `Z3SortedCommutativity` proves
that recognizer sound at every typed scope in sorted models.
`Z3IntegerDivisionSyntax` isolates the existing division recognizers from their
legacy value-model proofs in `Z3IntegerDivision`.
`Z3IntegerRewriteSyntax` does the same for integer rewrite recognition.
`Z3ConditionalRewriteSyntax` isolates conditional rewrite recognition while
retaining its existing legacy soundness bridge.
`Z3ArithmeticFactorSyntax` separates factor recognition from its legacy
value-model proof.
`Z3LpReplaySyntax` separates LP replay decisions from their legacy soundness proofs.
`Z3SortedQuantifierInstantiation` proves the exact recognizer sound for
scoped formulas, including substitutions beneath nested binders; the
quantifier-elimination assumption is established by inhabited typed root
models.
The legacy instantiation recognizer accepts some unscoped formulas: for
example, a canonical `or` declaration with an empty domain applied to two
arguments. `Z3QuantifierInstantiationTests` preserves this boundary. A
sort-indexed document route must account for such accepted inputs rather than
silently replacing that recognizer with a stricter scoped check.
The same test constructs an unscoped instantiation node and an incomplete
expression-table document which both the default checker and its indexed
version accept with zero obligations; the indexed diagnostic agrees.
Including the malformed application or a quantifier in that table makes the
document reject. This is a document-API counterexample, not evidence that the
native marshaller produces such a table.
`Z3GroundScope` proves independently of legacy values that a term is scoped
when every subexpression is listed in a locally well-typed ground application
table. `Z3QuantifierInstantiationTests` connects that result to the document
ground-table predicate and the original formula of a prepared entry.
`Z3SortedInstantiation` proves scope and sort preservation for explicit-variable
instantiation. `Z3DefinitionSyntax` owns the existing definition data, scope and
expansion algorithms without depending on legacy values, and
`Z3DefinitionExpansionScope` proves the expander preserves scope and sorts when its
definitions satisfy a typed condition. `Z3DefinitionRecognition` owns definition
and axiom recognizers, and `Z3DefinitionRecognitionScope` proves their constructor
provenance; both are legacy-independent. `Z3BvFreshSyntax` owns fresh-bit
reconstruction and `Z3BvFreshScope` proves generated projections have the same
provenance, without legacy values. `Z3DefinitionScope` connects these results to
document collection, so the condition holds for every successful
`document_definitions` result. The prepared-entry theorem then covers both
expander implementations, conditional on the original formula being scoped.
Native table completeness remains unproved.
`Z3LambdaSyntax` separates lambda-view, beta, and extensionality recognition
from the legacy lambda semantic contracts; `Z3LambdaRewrite` re-exports
those recognizers and retains its existing soundness adapters.
`Z3SortedLambda` and `Z3SortedLambdaEquality` prove scoped lambda-view, beta,
and extensionality soundness for these exact recognizers, including open
arguments and nested arrays, under explicit operator laws for supported
sorts. Existing typed root models satisfy the select and extensionality laws
for datatype-free array sorts, proving direct-lambda beta and extensionality
for those inhabited models without the constant-array law. A separate
standard-model construction supplies the constant-array law by choosing its
otherwise-uninterpreted application; the law does not follow from every
existing root model. These proofs are not yet connected to the document
checker or general rewrite replay.

`Z3DistinctAst` and `Z3SortedDatatype` are also transitively independent
of `Z3ValueTheory`. `Z3DistinctAst` owns distinct expansion and axiom
recognition; the legacy adapter retains their semantic proofs. Before the
switch, all-input parity of the recognizers was verified in F*.
`Z3BooleanSyntax` owns native Boolean classification
and bounded node traversal; `Z3BooleanRewrite` retains its compatibility
APIs and legacy soundness proofs. The sorted datatype proofs use
`Z3ExprScope`, `Z3ClauseSyntax`, and `Z3BooleanSyntax` directly. This is a
dependency separation, not a change to datatype coverage or acceptance.

`Z3SortedSkolem` and `Z3SortedDependentSkolem` are transitively independent
of `Z3ValueTheory`. `Z3SkolemSyntax` owns witness/dependency records,
capture-avoiding witness substitution, definition recognition, freshness,
and context ordering, together with their syntax-only lemmas.
`Z3Skolemization` retains compatibility aliases and its legacy choice-model
proofs. The sorted proofs use `Z3ExprScope` and `Z3Substitution` directly;
their eligibility, dependency limits, and choice assumptions are unchanged.

`Z3PolynomialSemantics` owns numeric polynomial denotation and certificate
algebra, and `Z3ArithmeticSyntax` owns the unchanged executable arithmetic
recognizers. Sorted integer arithmetic, division, Real linear/product proofs,
and `Z3TypedRoot` use these independent foundations and `Z3ExprScope`.
Their transitive closures exclude `Z3ValueTheory`, the legacy arithmetic
embedding/rewrite modules, and `Z3Definitions`. `Z3TypedRoot` still uses the
generic array and width-indexed bit-vector theories for its carriers.

`Z3BooleanRewriteSyntax` owns Boolean flattening, cuts, equivalence, and
search. `Z3BooleanRewrite` re-exports this API and retains only its legacy
semantic adapters. `Z3SortedBooleanRewrite` proves the exact algorithms
sound under scoped, sort-indexed evaluation, including reflexive equality
before the depth/boundary checks and the existing search budgets.
The observational and Boolean syntax/proof regression closures are also
independent of legacy values.

`Z3ArraySyntax` and `Z3ArrayEqualitySyntax` own the unchanged array
recognizers and rewrite search; the latter retains the one-dimensional
Int-array gate and 64-step default search. The production array modules
delegate their executable algorithms to these foundations.
`Z3SortedArray` derives the native array axioms and the complete unchanged
array equivalence search from sort-indexed read/write/extensionality laws,
with explicit per-sort support. Generated contractions, read expansions,
and merged ITEs preserve scope, sort, and that support constraint.
Its algebra has a full ghost-function-space implementation over arbitrary
index and element types, including nested array values. These proofs do
not yet replace every lambda proof or wire the root model's
currently free const-array and array-ext operators to their theory laws.
`Z3SortedArrayEquality` proves the exact Int-only unequal-default rule:
a semantic bound supplies an untouched integer index above the finite store
chains, and sorted arithmetic establishes that the defaults differ.
Its additional contract is only the primitive Int-array constant operator
law; the earlier array-model contract is unchanged.

`Z3BvSyntax` and `Z3SortedBv` provide independent executable foundations and
sort-indexed proofs for addition normalization and the complete word/order
rewrite, extract, and exhaustive families. These standalone proofs are not a
new production route; fresh-model replacement remains separate work.

`Z3SortedFiniteField` proves PAC replay, rewrite equivalence, and exhaustive
clause soundness from scoped, sort-indexed evaluation and primitive
residue-ring operator laws, including composite moduli. Its tests prove
all-input correspondence with the legacy PAC, rewrite-equivalence, and
exhaustive checkers, preserving premise support, witness rejection, replay
order, and work limits. The correspondence tests deliberately retain the
legacy checkers as oracles; the new semantic module itself does not import
them. These proofs are not yet a production route.

The older concrete example interpreters, pattern-matched example checker,
and five rewrite-synthesis wrappers have been retired. They were outside
the registered checker/test manifests and both native backend dependency
closures. Their historical results remain in
[the Pulse report](PULSE_PROOF_CHECKER_REPORT.md) and
[the QF_AX/QF_UF experiment](QF_AX_QF_UF_BENCHMARK_REPORT.md).
The generic theories, Pulse calculi and tests, native rewrite checkers, and
legacy value contracts used by production remain.

The following groups describe the main components, not a strict layering
of all imports.

| Component | Modules and role |
|---|---|
| Shared semantic foundation | [`Z3AstTheory.fst`](Z3AstTheory.fst) supplies expressions, well-formedness, and evaluation; [`Z3OperatorTags.fst`](Z3OperatorTags.fst) supplies operator tags. [`Z3ValueTheory.fst`](Z3ValueTheory.fst) retains the legacy concrete value domain. |
| Equational calculus | [`Z3ProofTheory.fst`](Z3ProofTheory.fst) defines proof terms, `fact`/`facts_of`, leaf obligations, and soundness. [`Z3ProofJustifications.fst`](Z3ProofJustifications.fst) handles modus ponens, unit resolution, and elimination rules. |
| Carrier-independent clauses | [`Z3ClausalSemantics.fst`](Z3ClausalSemantics.fst) proves clausal soundness over ghost truth valuations; [`Z3ResolutionProofTheory.fst`](Z3ResolutionProofTheory.fst) preserves the legacy interpretation API through proved adapters. |
| Carrier-independent observations | [`Z3ObservationalSemantics.fst`](Z3ObservationalSemantics.fst) defines observational agreement on scoped ghost denotations; [`Z3ObservationalSyntax.fst`](Z3ObservationalSyntax.fst) owns exact declarations and recognition; [`Z3ObservationalProof.fst`](Z3ObservationalProof.fst) provides abstract-carrier proof soundness. [`Z3ObservationalEquality.fst`](Z3ObservationalEquality.fst) retains the legacy adapters used by production. |
| Preprocessing rules | [`Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst) and [`Z3PreprocessingProofTheory.fst`](Z3PreprocessingProofTheory.fst) formalize substitution, quantifier/connective laws, kernel rules, and pipeline composition. These rule families are not all implemented in Pulse. |
| Sort-indexed datatype model | [`Z3DatatypeValue.fst`](Z3DatatypeValue.fst) builds finite well-sorted constructor trees over arbitrary sort-indexed base carriers and derives datatype laws, typed environments, and sort-preserving evaluation. [`Z3DatatypeSignature.fst`](Z3DatatypeSignature.fst) validates native schemas and supplies canonical constructor/tester/selector dispatch with arbitrary argument-dependent wrong-selector interpretations and a total interpretation witness. |
| Typed canonical core model | [`Z3CoreModel.fst`](Z3CoreModel.fst) states `core_model i dom`: model-owned sort domains (typing fixes only `Bool`, to Boolean values, but integer `+`/`*` must return `VInt`, so the Int domain contains those images, and canonical equality must decide value identity wherever it is applied), environments typed against a scope of sorts, application and binder typing, the connectives keyed only by the typed predicates of [`Z3CanonicalOps.fst`](Z3CanonicalOps.fst), equality required to decide value identity only on scoped terms under typed environments, integer `+`/`*`, and the ground bit-vector contracts. `lemma_typed_eval` proves that every scoped term, open or under binders, takes a value of its sort. `lemma_core_inhabited` gives a hypothesis-free model: the standard ground interpretation with integer arithmetic. [`Z3CoreKernel.fst`](Z3CoreKernel.fst) proves, for every node for which the default kernel's `check_node_with_context` returns `Some` by assertion, hypothesis, lemma, reflexivity, symmetry, transitivity, congruence, commutativity, `iff~`, `mp`, `mp~`, unit resolution, and/not-or elimination or iff-true/false, or as a theory lemma or rewrite whose conclusion the bounded bit-vector evaluator decides, that the returned checked fact holds in every core model under every environment typed for a scope its judgments and premises are scoped in, given that its premises and the assertions hold. `Some` is not zero obligations: theory-lemma and rewrite nodes (which may have premises) can be returned with a pending obligation, even when false, and their guarantee comes from the evaluator condition in `core_rule`. It is a per-node theorem; no document-level theorem exists, and no F* lemma establishes the scope of document entries (ground-table documents rely on the native side listing every subexpression). The kernel's Boolean dispatch (`Z3ProofTheory.is_not`, resolution complements and clauses, `mp`, elimination rules, and the quantifier, finite-field, integer-division and factoring recognizers) accepts only canonical connectives. The seven connective conjuncts of the legacy `model_sound` are keyed the same way, but every core model satisfies only the six non-equality contracts and its typed canonical equality, not necessarily the re-keyed untyped `eq_sound` (`Z3CoreModelTests.core_without_untyped_equality`). Closed instances of the former name/tag and datatype-name clashes take the values of their own theory in the witness core model. `model_sound` still has no model: its open-environment, untyped binder and array/numeral obstructions remain. Quantifier truth, lambda/array semantics, real arithmetic, datatypes and finite fields are not part of `core_model`; quantifier and binder rules, definitions, the other rewrite and theory checkers and Skolemization are not covered. [`Z3CoreModelTests.fst`](Z3CoreModelTests.fst) instantiates the theorem on accepted closed and open-scope nodes with premises satisfiable in witness core models, shows that the typed environment and `core_rule` are needed, rejects look-alike connectives, and records two legacy obstructions as finite clause instances with satisfiable drop-one controls: the `array_model` store clause and the `numeric_operators` numeral clauses are jointly unsatisfiable at the closed term `(store a 0 1/2)`, and every model of the untyped quantifier contract with `arithmetic_model` and `eq_sound`, if one exists, falsifies the valid `forall x:Int. x + 0 = x`. |
| Ghost semantics and classical standard model | The interpretation fields of [`Z3AstTheory.fst`](Z3AstTheory.fst) and `eval` are ghost (`GTot`); the production `value` type, its `bool` and `Tot` array payloads, and every executable checker function are unchanged, and F* rejects ghost results in executable code. Proofs that run an executable evaluator on a ghost valuation use a proved-equal ghost twin or an executable valuation computed in a ghost context (`Z3BoundedBoolEquiv.geval`, `freeze`). [`Z3GhostStandardModel.fst`](Z3GhostStandardModel.fst) builds, with `FStar.IndefiniteDescription.strong_excluded_middle` and no added axiom or hypothesis, one interpretation that is a `Z3CoreModel.core_model` (with the ground bit-vector contracts), satisfies the legacy untyped canonical `eq_sound` on every value including arrays, gives `forall`/`exists` their classical truth over exactly the value lists typed for the reversed binder list, has standard Bool/Int/`(Array Int Int)`/bit-vector domains and computes integer numerals. [`Z3GhostStandardModelTests.fst`](Z3GhostStandardModelTests.fst) evaluates valid, mutated, satisfiable and unsatisfiable Int formulas, `[Int; Bool]` binders and their swapped form, numerals, array equalities and an array quantifier, with mutation controls. Lambdas (opaque values), Real, datatypes, finite fields, sequences and nested arrays are not modeled; the untyped `boolean_model` and hence `model_sound` still have no model; apart from quantifier instantiation (next row), no rule outside `core_rule` and no document theorem rests on this model yet. Development code that computes with expression values uses the executable [`Z3AstTotEval.fst`](Z3AstTotEval.fst), equal to ghost `eval` on quantifier-free expressions. |
| Typed quantifier instantiation | [`Z3TypedQuantifier.fst`](Z3TypedQuantifier.fst) states `quantifier_model i dom`: one interpretation and one domain assignment that satisfy `core_model`, typed `forall`/`exists` over exactly the value lists typed by the reversed binder list, and quantifier extensionality. `core_model` itself is unchanged. `Z3GhostStandardModel.lemma_quantifier_model` proves that the classical model satisfies all three jointly, with the same interpretation, domains and projection; extensionality is proved from its quantifier field, opaque lambda branch included, and is not a lambda (beta) law. [`Z3QuantifierKernel.fst`](Z3QuantifierKernel.fst) proves the unchanged executable decision `Z3QuantifierInstantiation.check` sound in every such model, under every environment: the evaluated closed arguments are typed by `L.rev bs`, the `forall` is eliminated at exactly those values, and the existing capture-avoiding substitution theorem relates the body there to the instance. For an instantiation node, `check_node_with_context` returns `Some` with pending obligation 0 exactly when `check_step` accepts it, and with pending 1 otherwise, also for false conclusions and always for `Equal` conclusions; observational conclusions and nodes with premises are rejected. The node theorem requires pending 0 and gives the returned fact, which has no hypotheses. `lemma_typed_check_node_sound` extends the core theorem to core rules plus checked instantiations. The legacy `lemma_check_sound` still requires the untyped `boolean_model` and `forall_elimination_model`, has no model, and is not used. [`Z3QuantifierKernelTests.fst`](Z3QuantifierKernelTests.fst) computes accepted and rejected actual nodes (Int, Bool, `[Int; Bool]` and two Int binders, nested binders, `BV2`) and checks them in the classical model: instances follow from true quantifiers, several rejected nodes returned with pending 1 have false conclusions, capture, shadowing, unscoped, wrong-order, wrong-sort and wrong-arity mutations are not checked, and the untyped elimination contract fails there while the typed one holds. Quantifier introduction and the other binder rules, definitions, Skolemization and the document layer still rest on `model_sound`. |
| Contextual datatype kernel | [`Z3SortedSemantics.fst`](Z3SortedSemantics.fst), [`Z3SortedDatatype.fst`](Z3SortedDatatype.fst), and [`Z3SortedProof.fst`](Z3SortedProof.fst) check native datatype proof DAGs against one checked schema and derive zero-obligation unsatisfiability of the original assertions in the typed interpretation. Native documents with datatype metadata use this path without a legacy fallback; [coverage and theory boundaries](OCAML_CHECKER_REPORT.md#concrete-sort-indexed-datatype-semantics) remain explicit. Typed-root prototype branch only (no route uses it): [`Z3SortedRoot.fst`](Z3SortedRoot.fst) proves that the Sorted layers agree with every [`Z3TypedRoot.fst`](Z3TypedRoot.fst) root model, and [`Z3SortedRootDocument.fst`](Z3SortedRootDocument.fst) derives the Sorted quantifier laws from that root model's R1, restates `lemma_check_document` for every root model and adds an off-route certification gate that also checks typing and root coverage of every document term the checker reads (assertions, entry formulas, instantiation arguments; the canonical wrappers and instances the kernels build internally are not gated, and coverage restricts only the SMT reading, not the root-class falsity proof); [`Z3SortedRootDocumentTests.fst`](Z3SortedRootDocumentTests.fst) runs actual documents through it: 9 positive documents (B1–B9) falsified in every root model plus 4 certified variants (D8 and D10 pairs, F1, F2). No route calls the gate, so a native Sorted ACCEPT is not `RootCertified`; other legacy ACCEPTs, the default route and the uninhabited legacy `model_sound` are unchanged. Native front-end translation (assertions, schema, `define-fun`), native datatype id/tag fidelity and the full-function-space array/lambda and `FStar.Real` parameterization remain trust points, not a theorem about every SMT model. The sorted kernel also replays typed integer Farkas certificates and, on the native sorted route, elaborates certified closed Skolem steps into Hilbert-epsilon choice equations over one joint witness tuple ([`Z3SortedSkolem.fst`](Z3SortedSkolem.fst), `check_document_epsilon`). `Z3SortedRootDocument.fst` keeps the consumed `ArithmeticFarkas` coefficients and `Skolemization` label in its read view and proves that, in every root model, an epsilon verdict `Some 0` makes the original assertions not all true (`lemma_root_check_document_epsilon`, with the off-route gate `check_root_document_epsilon`); closed Skolem steps inside the NNF certificates the kernel replays are collected into the same epsilon context, and their dependent Skolem functions into a dependent context on top of it ([`Z3SortedDependentSkolem.fst`](Z3SortedDependentSkolem.fst), next row); top-level dependency-bearing Skolem steps stay pending. |
| NNF certificate replay | [`Z3NnfReplay.fst`](Z3NnfReplay.fst) replays, inside `Z3SortedProof.check_node_cached` (one extra disjunct, so the single diagnosed check of both native front ends sees it), the binder certificate of a premise-free `QuantifierIntroduction` node whose root entry is `nnf-neg` or `nnf-pos`: the polarity-aware local NNF rules of `src/ast/normal_forms/nnf.cpp`, `refl`, `trans`, `monotonicity`, closed `sk` steps whose choice equation is an assertion of the (epsilon-elaborated) document, and open (dependent) `sk` steps whose universal closure is one ([`Z3SortedDependentSkolem.fst`](Z3SortedDependentSkolem.fst): one joint witness tuple per argument tuple; tests in [`Z3NnfSkolemTests.fst`](Z3NnfSkolemTests.fst)). `lemma_replay` proves every replayed conclusion true in the Sorted model from the universal and existential quantifier laws only; `Z3SortedRootDocument` derives both from R1 of one inhabited typed root model, keeps the certificate in its read view and gates its internal terms. See [NNF certificate replay](#nnf-certificate-replay-sorted-route). |
| Typed Real arithmetic and ITE laws | [`Z3SortedReal.fst`](Z3SortedReal.fst) (Real carrier and laws over the Sorted interpretation), [`Z3SortedRealLinear.fst`](Z3SortedRealLinear.fst) (linear normal forms, typed Int/Real Farkas replay, Real rewrite equivalence incl. Real equations), [`Z3SortedRealOrder.fst`](Z3SortedRealOrder.fst) (the Real equality/order atoms of the `real_order` clause check), [`Z3SortedRealExtension.fst`](Z3SortedRealExtension.fst) (Skolem overrides keep the laws) and [`Z3SortedRealRoot.fst`](Z3SortedRealRoot.fst) (the laws from R2 of every root model) add the `real_farkas` and `real_rewrite` disjuncts of `Z3SortedProof.check_node_cached` and the gated Real leaves of the quant-intro replay; `Z3NnfReplay.ite_rewritten` replays three sort-generic `ite` laws (on quant-intro leaves and, through the ungated `ite_rewrite` disjunct, on closed premise-free `rewrite` steps). See [Typed Real certificates and ITE rewrite laws](#typed-real-certificates-and-ite-rewrite-laws-sorted-route). |
| Typed Int division laws | [`Z3SortedIntDivision.fst`](Z3SortedIntDivision.fst) states the Sorted Int division laws (`division_laws`: for a NONZERO divisor the canonical `div`/`mod` are the Euclidean quotient `x / y` and remainder `x % y` of the arguments' Int values, in the same Sorted interpretation and Int carrier as every other Int law; a zero divisor has no law), at every scope and typed environment (`lemma_quotient_at`, `lemma_remainder_at`); [`Z3SortedDivisionExtension.fst`](Z3SortedDivisionExtension.fst) (Skolem overrides keep them) and [`Z3SortedDivisionRoot.fst`](Z3SortedDivisionRoot.fst) (derived from R2 of every root model; the standard root model satisfies R1-R6, the Real laws and these laws at once). Model-contract change: see [Typed Int division](#typed-int-division-laws-and-the-root-model-contract). |
| Clausal/resolution calculus | [`Z3ResolutionProofTheory.fst`](Z3ResolutionProofTheory.fst) embeds equational proofs via `REq` and adds propositional/clausal rules, hypotheses, lemmas, and explicit trusted obligations. [`Z3ResolutionProofCheckerTests.fst`](Z3ResolutionProofCheckerTests.fst) exercises this calculus. |
| Clause-trail elaboration | [`Z3ClauseProof.fst`](Z3ClauseProof.fst) performs reverse unit propagation over active clauses and emits ordinary hypothesis, unit-resolution, and lemma steps. The existing document kernel checks these steps; literal IDs and propagation results are not trusted. Deletions remove one matching active clause. [`Z3ClauseProofTests.fst`](Z3ClauseProofTests.fst) covers positive and negative elaborations. |
| Full-DAG kernel | [`Z3UnifiedProof.fst`](Z3UnifiedProof.fst) uses checked premise judgments rather than synthetic rewrite/trusted leaves in the legacy recursive proof types. Supporting modules include [`Z3ObservationalEquality.fst`](Z3ObservationalEquality.fst), [`Z3Commutativity.fst`](Z3Commutativity.fst), [`Z3BooleanRewrite.fst`](Z3BooleanRewrite.fst), and [`Z3ArrayLemma.fst`](Z3ArrayLemma.fst). Observational equality is a separate judgment, not object-language equality. |
| Destructive equality resolution | [`Z3QuantifierDer.fst`](Z3QuantifierDer.fst) verifies guarded `forall`/`exists` variable elimination, with an occurs check, binding-sort checks, and capture-safe substitution. Closed original input facts may be used in binder certificates because their truth is environment-independent; definition expansion is applied consistently to parent conclusions and hidden certificates. |
| Skolemization | [`Z3Skolemization.fst`](Z3Skolemization.fst) represents each binding block by a joint Hilbert-choice tuple and its fresh function symbols by tuple coordinates. It verifies substitution, dependencies, acyclic interpretation extension, and preservation of fresh original inputs. A block none of whose variables occurs in its body needs no choice tuple and is checked structurally by `vacuous`. The unified kernel checks `sk` observations in this chosen interpretation, not as arbitrary fixed-model equalities; choice and the existing semantic-model contract remain explicit hypotheses. |
| Binder certificates and instantiation | The unified kernel checks hidden `proof-bind` DAGs using an all-environments invariant before lifting body relations through `forall`, `exists`, or `lambda`. [`Z3BinderSubstitution.fst`](Z3BinderSubstitution.fst) proves capture-avoiding substitution beneath nested binders and arbitrary unused-variable thinning; [`Z3QuantifierInstantiation.fst`](Z3QuantifierInstantiation.fst) checks native substitution parameters against this foundation. [`Z3QuantifierNnf.fst`](Z3QuantifierNnf.fst) derives quantifier duality. See [coverage and limits](OCAML_CHECKER_REPORT.md#binder-and-quantifier-proof-support). |
| Quantifier pulling | [`Z3QuantifierPull.fst`](Z3QuantifierPull.fst) derives same-kind binder flattening, quantifier negation, and capture-safe n-ary `and`/`or` pulling from the existing quantifier semantics. The unified `pull-quant` rule also checks open formulas in binder certificates; unsupported shapes or exhausted normalization fuel retain obligations. |
| Quantifier reductions and lambdas | [`Z3QuantifierReduce.fst`](Z3QuantifierReduce.fst) checks distribution and binder-aware endpoint equivalence; [`Z3DestructiveEquality.fst`](Z3DestructiveEquality.fst) checks guarded equality elimination; [`Z3LambdaRewrite.fst`](Z3LambdaRewrite.fst) checks extensionality and capture-safe beta/constant-array rewriting under explicit lambda interpretation contracts. |
| Shared theory normalization | [`Z3TheoryNormalize.fst`](Z3TheoryNormalize.fst) combines proved local rewrites with bottom-up congruence for rewrites, NNF, `def-axiom`, and actual-premise `th-lemma` implications. Newly generated terms are normalized again with decreasing fuel, including nested constructor field equalities. Bounded constructor-equality propagation rewrites actual premises and conclusions outside binders. [`Z3BvLemma.fst`](Z3BvLemma.fst) and [`Z3DatatypeLemma.fst`](Z3DatatypeLemma.fst) add native bit-vector/datatype semantic bridges. Coverage is bounded and conditional, not general bit-blasting or datatype theory completeness. |
| Imperative checking | [`Z3PulseProofChecker.fst`](Z3PulseProofChecker.fst) and [`Z3PulseJustificationChecker.fst`](Z3PulseJustificationChecker.fst) implement equational and justification specifications in Pulse, including verified heap mutation and traversal counts; [`Z3PulseProofCheckerTests.fst`](Z3PulseProofCheckerTests.fst) includes acceptance/rejection examples. |
| LRA certificates | [`Z3LraFarkasTheory.fst`](Z3LraFarkasTheory.fst), [`Z3PulseLraChecker.fst`](Z3PulseLraChecker.fst), [`Z3PulseLraCheckerTests.fst`](Z3PulseLraCheckerTests.fst), and [`Z3PulseLraCheckerParsed.fst`](Z3PulseLraCheckerParsed.fst) provide a separate Farkas-certificate theory/checker path. |
| Integrated arithmetic certificates | [`Z3LinearArithmeticTheory.fst`](Z3LinearArithmeticTheory.fst), [`Z3LinearArithmeticAst.fst`](Z3LinearArithmeticAst.fst), and [`Z3LinearArithmeticEmbed.fst`](Z3LinearArithmeticEmbed.fst) provide exact polynomial operations, certificate checking, and the AST semantic bridge used by the unified kernel. |
| Factored sign rewrites | [`Z3ArithmeticFactor.fst`](Z3ArithmeticFactor.fst) checks the arithmetic rewriter's `p = 0 ~> f = 0 or g = 0`, `p >= 0 ~> ((f >= 0) = (g >= 0)) or (f = 0 or g = 0)`, and negated `p <= 0` steps over Int or Real. It requires `p` and `f * g` to have the same integer-coefficient polynomial normal form, computed with the [`Z3NlaLemma.fst`](Z3NlaLemma.fst) multiplication over opaque atoms, and non-constant factors. Division, `to_real`, and uninterpreted terms stay atoms, so no field law is used. Soundness needs only the existing `numeric_model` and Boolean contracts. [`Z3ArithmeticFactorTests.fst`](Z3ArithmeticFactorTests.fst) decides closed positive and negative instances. |
| Conditional comparison rewrites | [`Z3ConditionalRewrite.fst`](Z3ConditionalRewrite.fst) checks rewrites with conditional subterms by replacing the first guard with `true` and `false` on both sides outside binders and folding each branch. Besides conditionals with literal guards and constant equations, the fold decides comparisons whose linear normal form is constant (such as `(>= 0 1)`) with [`Z3ArithmeticRewrite.fst`](Z3ArithmeticRewrite.fst), and drops literal arguments of `and`/`or` when [`Z3BooleanRewrite.fst`](Z3BooleanRewrite.fst) confirms the result. This covers the arithmetic rewriter's lifting of a numeral-branch conditional out of a numeric comparison, such as `(ite c 0 x) >= 1 ~> (not c) and (x >= 1)`, also after a numeral addend was moved across. Soundness uses only the existing numeric and Boolean model contracts. |
| Bit-vector extraction rewrites | [`Z3BvExtract.fst`](Z3BvExtract.fst) checks the bit-vector rewriter's steps that move an extraction into its argument: `((_ extract h 0) (bvadd x1 ... xn))` and `bvmul` to the sum or product of the extracted low bits, `((_ extract h l) (ite c t e))` to `(ite c ((_ extract h l) t) ((_ extract h l) e))` with the same guard, and `((_ extract h l) (concat x y))` to the bits of `y`, the bits of `x`, or the concatenation of the low bits of `x` and the high bits of `y`, keeping an argument whose bits are all taken. Sums and products are distributed only for `l = 0`, since higher bits depend on carries. Only binary concatenations are split. Inner extractions may be composed with an extraction argument, as `mk_extract_proc` does. Widths come from the native declarations and are compared as integers; both sides must be closed. Soundness uses only the existing `bv_model` and `term_ite_sound` contracts. |
| Bounded bit-vector evaluation | [`Z3BvExhaustive.fst`](Z3BvExhaustive.fst) decides premise-free `th-lemma` and `rewrite` steps by enumerating values for structurally identified BV leaves. The fragment includes canonical Boolean connectives and equality, unsigned BV comparisons, numerals, binary `concat`, `extract`, `zero_extend` and binary `bvadd`. Connectives require the typed name, tag, domain, range and parameter predicates of [`Z3CanonicalOps.fst`](Z3CanonicalOps.fst); datatype declarations with connective names are not connectives. BV operations use the checked [`Z3BvLemma.fst`](Z3BvLemma.fst) recognizers. Unsupported Boolean terms and malformed evaluated declarations stay pending. The conclusion must be closed and ground, with at most 512 unfolded-tree occurrences and at most 12 total leaf bits, hence at most 4096 assignments. Leaves are enumerated, not assigned a presumed constant value. [`Z3StandardModel.fst`](Z3StandardModel.fst) proves that the ground Boolean/BV contracts have models: canonical connectives and BV-tagged heads with matching parameters are computed, and remaining heads use an arbitrary function of their argument values, with results coerced to their range sorts. This witness has no hypotheses. The direct evaluator lemmas prove `valid` and `equivalent` sound in every ground model, with standard-model corollaries. The legacy kernel theorem reaches them only through the uninhabited global `model_sound`; `Z3CoreKernel` instead proves theory-lemma and rewrite nodes whose conclusion this evaluator decides sound from the inhabited `Z3CoreModel.core_model`. No document-level theorem is claimed. Arrays, arithmetic, datatypes, finite fields, quantifiers, open terms and projection widths above 4096 are outside this model's theory claims. [`Z3BvExhaustiveTests.fst`](Z3BvExhaustiveTests.fst) covers accepted and rejected steps, bounds, malformed declarations, name/tag clashes, datatype names, witness values and countermodels. |
| Modular bit-vector sums | [`Z3BvAddNormalize.fst`](Z3BvAddNormalize.fst) decides premise-free `rewrite` steps `a = b` between sums of one bit-vector sort `BV<w>`: each side is read as the sum of its numerals modulo `2^w` and the sequence of its atoms (any other closed term of that sort, kept opaque), through nested binary and n-ary `bvadd` recognized by declaration kind, width parameter and argument sorts with the [`Z3BvExtract.fst`](Z3BvExtract.fst) and [`Z3BvLemma.fst`](Z3BvLemma.fst) recognizers. Both sides must have the same total modulo `2^w` and the same atoms in the same order, so `bvadd(bvadd(c1, t), c2) = bvadd(c3, t)` is decided for any `t` of any width up to 4096, with wrap-around and cancellation to the bare atom. Atoms are never evaluated, reordered or merged; a malformed numeral or sum declaration is neither read nor an atom; the tree has at most 512 occurrences and both sides are closed. Soundness is an induction on the sum using only the existing `bv_model` conjuncts for numerals, `operation` and `nary_operation` (through `model_sound`). [`Z3BvAddNormalizeTests.fst`](Z3BvAddNormalizeTests.fst) decides closed positive and negative instances (widths 1, 8, 32 and 66, wrap-around, cancellation, wrong totals, dropped, extra, replaced, reordered and merged atoms, sorts, malformed declarations, the size bound). |
| Finite-field rewrites | [`Z3FiniteFieldLemma.fst`](Z3FiniteFieldLemma.fst) decides `rewrite` steps over `FF<p>` terms by normalizing both sides to sparse polynomials modulo `p` (atoms are the maximal non-field subterms) and by rescaling equalities with checked factors. It uses only commutative-ring laws, never assumes `p` is prime, and relies on the explicit `ff_model` hypothesis conjoined into `normalization_model`. The native bridge marshals `FiniteField p` sorts as `FF<p>` and `ff` numerals/operators with `decl_kind` 300-304 (see [`FINITE_FIELD_REPORT.md`](FINITE_FIELD_REPORT.md)). Finite-field `th-lemma` steps are decided by bounded exhaustive evaluation or, for any modulus, by replaying the recorded `ff-pac` ideal certificate in [`Z3FiniteFieldPac.fst`](Z3FiniteFieldPac.fst) when it uses only definitions and positive premises; certificates that need the inverse witness of a disequality remain unmet. |
| Integer division | [`Z3IntegerDivision.fst`](Z3IntegerDivision.fst) checks guarded quotient/remainder identities, remainder bounds, and common-factor cancellation with positive numeral divisors. Native integer `div` and `mod` have distinct interpreted tags. Soundness assumes their standard nonzero-divisor semantics; division by zero remains unspecified. The Sorted route does not use this assumption: its guarded div/mod clauses read the derived `Z3SortedIntDivision.division_laws` (see the typed Int division section). [`Z3ArithmeticRewrite.fst`](Z3ArithmeticRewrite.fst) also checks binary-sum product expansion over integers and reals. |
| Gomory cuts | [`Z3LpGomory.fst`](Z3LpGomory.fst) reconstructs integer-split candidates from native LP row/bound data and requires both branches to derive the actual cut through the existing Farkas checker. Split exhaustiveness follows from integer semantics; no LP row, bound metadata, or foreign checker verdict is assumed. |
| Integer rounding cuts | [`Z3LpIntegerCut.fst`](Z3LpIntegerCut.fst) refutes a set of premises by Chvátal-Gomory rounding followed by a Farkas combination. A certificate is a list of rounded bounds `L <= k` and a final weight vector. Every bound and the final refutation are replayed through [`Z3LinearArithmeticAst.check`](Z3LinearArithmeticAst.fst) against the actual premise ASTs and the earlier bounds only, with one weight per premise or earlier bound plus one for the negated bound; that check rounds a strict inequality over Int terms (`a < b` to `a + 1 <= b`), so the rounding is checked, not trusted, and is unavailable for Real terms. Soundness uses only the existing `numeric_model` and Boolean contracts, exactly like [`Z3LpGomory.fst`](Z3LpGomory.fst). The untrusted candidate search handles the conclusion `false` only: it substitutes variables fixed or equated by unit-coefficient equalities, rounds each non-strict row whose atoms are all Int and whose coefficients have a common factor `g >= 2` not dividing the constant, and finds the final weights by Fourier-Motzkin elimination (cheapest atom first, one-sided atoms dropped). Every cap fails closed to a pending obligation: at most 32 premises, 8 bounds of at most 64 terms, 128 rows, 64 eliminations, 4096 row pairs in total, and magnitudes at most 2^128 for every coefficient, constant, denominator and weight, checked on the input rows and after every substitution or elimination. Systems that need a genuine Gomory or branching cut stay pending. [`Z3LpIntegerCutTests.fst`](Z3LpIntegerCutTests.fst) decides closed positive and negative certificates (too-strong and too-weak rounding, zero or negative divisor weights, non-cancelling rational weights, wrong weight lengths, forward references, permuted premises, Real sorts). |
| Typed proof documents | [`Z3ProofDocument.fst`](Z3ProofDocument.fst) performs transport-independent definition, scope, input, and topological validation; [`Z3ProofIndex.fst`](Z3ProofIndex.fst) supplies persistent caches. |
| Native Z3 integration | [`Z3Native.fsti`](Z3Native.fsti) and [`ocaml_runtime/Z3Native.ml`](ocaml_runtime/Z3Native.ml) expose foreign API views; [`Z3NativeProof.fst`](Z3NativeProof.fst) marshals expressions and proof DAGs directly into checker datatypes. |

## Reports

| Topic | Report |
|---|---|
| Equational proof calculus and soundness of smart constructors | [Rewriter proof theory](PROOF_REWRITER_REPORT.md) |
| Modus ponens, unit resolution, and elimination rules | [Proof justifications](PROOF_JUSTIFICATIONS_REPORT.md) |
| Preprocessing rules and composition | [Preprocessing proof theory](PREPROCESSING_PROOFS_REPORT.md) |
| Pulse implementations, concrete interpretations, verified matchers, and partial checking | [Pulse proof checker](PULSE_PROOF_CHECKER_REPORT.md) |
| Clausal/resolution rules and explicit trusted leaves | [Resolution checker](RESOLUTION_CHECKER_REPORT.md), [rule-by-rule scope](RESOLUTION_CHECKER_SCOPE.md) |
| Executable Farkas checking and real-proof parsing | [LRA Farkas checker](LRA_FARKAS_REPORT.md) |
| Exact arithmetic certificates in the unified kernel, coverage, and remaining formal limits | [Arithmetic certificate integration](ARITHMETIC_CERTIFICATE_REPORT.md) |
| Historical JSON interface, now removed | [Archived JSON interface](JSON_PROOF_CHECKER_REPORT.md) |
| Extraction, runtime shim, native executable, and measurements | [Standalone OCaml checker](OCAML_CHECKER_REPORT.md) |

Some reports also examine Z3's source implementation of the corresponding
rules. Those source-audit results are distinct from the semantic guarantees
of checking an input proof.

## Extraction and execution

The executable reads SMT-LIB, solves with statically linked Z3 and its
official OCaml bindings, and checks the resulting proof in one process.
There is no Python exporter, JSON document, external solver process, or
runtime F* invocation in this path.

From this directory, in a Windows C++20 developer PowerShell:

```powershell
.\tools\build_ocaml_checker.ps1 -RunTests
'(declare-const p Bool)(assert p)(assert (not p))' |
  wsl -e bash -c '~/z3checker/checker --stats'
```

Every build first builds and installs Windows Z3 from this checkout.
F* verification, Pulse tests, and extraction explicitly use the installed
`build\install\bin\z3.exe` and its detected `--z3version`, without disabling
version checks. `-Z3WindowsBuildDir` and `-Z3InstallDir` change the build
directory and installation prefix; `-CacheDir` selects the proof cache.
The WSL producer and official OCaml bindings are also rebuilt and installed
before linking from that installation. `-RunTests` verifies every registered
module and F*/Pulse regression and runs native bridge and CLI tests after these
installation steps; without it, only the registered production modules in the
F* dependency closure of the extracted checker are verified and no test is
built. See the [toolchain instructions](OCAML_CHECKER_REPORT.md).

[`Z3NativeProof.fst`](Z3NativeProof.fst) uses native AST identities for
expression/sort caches; declaration caches also include application arity.
Worklists traverse shared expression/proof DAGs without recursively
unfolding them, and repeated expressions reuse allocated algebraic values.
Native owners remain alive for the cache lifetime so Z3 cannot recycle
cached identities.

The build script links extracted code with static Z3, its official OCaml
bindings, Zarith, and the handwritten [`ocaml_runtime`](ocaml_runtime)
shim. Native interoperability, parsing/API views, ownership, extraction,
the compiler, and runtime remain trust boundaries; no theorem proves
correspondence of the foreign API to Z3's semantics.

An obligation-free closed false root produces `ACCEPT`; unsupported leaves
remain `PARTIAL`, and unsupported judgment shapes reject rather than being
relabeled or trusted. See the [executable report](OCAML_CHECKER_REPORT.md)
for prerequisites, exit codes, statistics, timeouts, and formal limits.
`--sorted-core` opts non-datatype documents into the existing sort-indexed
kernel as well. This mode has no legacy fallback: Boolean and EUF proofs
can certify under the inhabited typed interpretation, while unsupported
arithmetic, array, binder, and definition steps retain obligations or reject.
It is an incremental semantic-migration path, not a complete combined
SMT-LIB theory model. Statistics identify it as `semantics=sorted-core`;
datatype documents continue to use `semantics=sorted-datatype`.
`--interactive` instead evaluates complete stdin commands on a persistent
context and checks each UNSAT proof through `Z3_set_proof_check_callback`,
preserving push/pop, assumptions, and queries. Certification reports are
SMT-LIB comments, not replacements for the solver's result; only
`proof-check ACCEPT` is an obligation-free check. See the
[interactive protocol](OCAML_CHECKER_REPORT.md#interactive-certifying-smt-lib-session).

### Clausal SMT search proofs

With `proof=true`, set `smt.clause_proof=true` before initializing SMT
search to replace learned-clause proof DAG reconstruction with a typed
`proof-trail` of additions and deletions. The default is standard proofs.
Preprocessing proofs and local theory certificates remain enabled; this is
not an option to disable all proof AST allocation. Changing modes on an
already initialized incremental solver requires resetting it first.

Run `checker --clause-proofs` (also supported with `--interactive`) to select
this producer mode. Input and theory additions carry ordinary certificates;
learned clauses without certificates must pass reverse unit propagation.
The elaborator discharges the negated target literals and prunes unused
history before checking the ordinary document. Original assertion membership,
root closure, and all selected inference steps are still checked. Missing
or unsupported theory certificates cannot produce an obligation-free
`ACCEPT`; they remain explicit obligations or fail checking.

Resolution recognizes `true` and `false` as complementary literals as well
as explicit negation. The semantic proofs require the standard Boolean
constant interpretations. Native `true-axiom` leaves are checked as
tautologies, not accepted solely because of their rule name. These
extensions do not certify arbitrary NLSAT assumptions or nonlinear theory
lemmas: unsupported arithmetic inferences retain their obligations.

[`tools/test_native_checker.py`](tools/test_native_checker.py) and
[`tools/test_native_bridge.ml`](tools/test_native_bridge.ml) exercise the
direct/native path; `tools/test_*.smt2` remain input fixtures.
The old exporter, JSON parser/decoders, compatibility CLI, and generated
F* proof snapshots have been removed. The [JSON report](JSON_PROOF_CHECKER_REPORT.md)
describes only that historical implementation.
[`tools/parse_farkas.py`](tools/parse_farkas.py) handles the separate LRA
certificate examples. Typecheck individual F* modules using the command
in the [overview](README.md).

## NNF certificate replay (Sorted route)

Z3's NNF converter (`src/ast/normal_forms/nnf.cpp`) proves each step
`nnf-neg(parents..., (~ (not s) t))` or `nnf-pos(parents..., (~ s t))`;
`PR_NNF_NEG` in `proof_checker.cpp` is a `TBD` that returns true and is not
used as evidence. The native marshal (`Z3NativeProof.marshal_binder`, unchanged)
turns the sub-DAG below such a node into one binder certificate: entries in
post order, premise ids of earlier entries, and binder sorts plus the open body
proof for a binder rule whose only premise is `proof-bind`. The Sorted kernel
used to judge these nodes as premise-free propositional consequences, with
quantifiers as opaque atoms; it never read the certificate.

**Protocol.** The existing data suffices; no producer or format change.
`Z3NnfReplay.replay` reads a certificate only when its root entry is `nnf-neg`
or `nnf-pos`. It classifies every entry's formula, runs the existing scope
guard (`Z3UnifiedProof.binder_scopes`/`scope_entries_checked`: the root at
`[]`, the premise of an entry with sorts `bs` used at `S` at `L.rev bs @ S`,
`Var 0` the last binder, shared entries checked at every assigned scope) and
then checks the local rule of every entry the root uses. A negative step's
target is equivalent to the negation of its source; a positive child fact is
`c ~ r`, a negative one `(not c) ~ r` or the producer's skip `r ~ r` with
`r = mk_not(c)`. Connectives are recognized only through
`Z3SortedSemantics.classify` (name, domain, range, interpretation and
parameters).

| Constructor (children in producer order) | Status |
|---|---|
| `and`/`or`, n-ary, negative: dual connective over negative children | replayed |
| `and`/`or` positive (same connective) and `not` positive (negative child) | replayed; the producer emits `monotonicity` or no step for these |
| `not x`, negative: positive child (double negation) | replayed |
| `=>`, negative `(and a' b')` / positive `(or na' b')` | replayed |
| Boolean `ite`: `[P(c), N(c), Q(x), Q(y)]` to `(and (or nc' x') (or c' y'))` | replayed (both polarities) |
| Boolean `=` and binary `xor`: `[P(a), N(a), P(b), N(b)]`, equivalence/xor shapes | replayed (both polarities) |
| `exists`/`forall` with `proof-bind`: same kind (positive) or dual kind (negative) over the same binder list, body fact read at `L.rev bs @ S` | replayed |
| `refl`, `trans` (two premises, equal middle terms), `monotonicity` (same declaration, premises consumed in argument order) | replayed |
| closed `sk` (Skolem constants) whose equation `(= a b)` is an assertion; on the epsilon route the closed eligible definitions of top-level and inner `sk` steps form one context (`Z3SortedProof.epsilon_context`; when the merged context fails a gate the top-level context is used) | replayed in the choice extension |
| open `sk`: a Skolem FUNCTION of the enclosing binders (`(exists bs. B) ~ B[f(x1..xm)]`, or the negative form), accepted when a universal closure `(forall cb. (= a b))` of its exact equation (any binder list cb; the generated ones quantify over the dependency scope) is an assertion and its dependencies are typed at every assigned scope; on the epsilon route the closures of the certified dependent context (`Z3SortedProof.dependent_context`) are appended to the assertions | replayed in the joint dependent choice extension |
| negative `forall` | Skolemized by the producer (`sk` + `trans`), covered by the rows above |
| `rewrite` roots (a `quant-intro` root is replayed with scoped `rewrite` leaves: [Real and ITE leaves](#typed-real-certificates-and-ite-rewrite-laws-sorted-route)), labels (`rewrite` from `mk_iff_oeq`), `apply-def`/`intro-def` naming, lambdas, the `hnf.cpp` `nnf-neg` variant, any other entry name | PENDING |
| over budget, unclassifiable entry, failed guard or local check | PENDING |
| premise id that is not an earlier entry (forward, self, negative, or past the last entry) in an `nnf-neg`/`nnf-pos`-rooted certificate | rejected proof entry (`Malformed`) |

**Premise-id boundary (diagnostic contract change).** Before this replay, the
Sorted route never read a binder certificate, so an `nnf-neg`/`nnf-pos` node
whose certificate had an invalid premise id was judged like any other
premise-free node: accepted if `(= (not s) t)` (or `(= s t)`) was a bounded
propositional/datatype consequence, otherwise one pending obligation. Now
`Z3NnfReplay.replay` returns `Malformed` for such a certificate and
`check_node_cached` returns `None`: the document is rejected at that entry
(`proof-entry` stage), even if the old propositional test would have accepted
the conclusion. The change is structural only. It applies only to certificates
whose root entry is `nnf-neg` or `nnf-pos` (others, and an out-of-range root,
stay `Unreplayed`), and only to ids `p` of entry `k` with `p < 0` or `p >= k`.
Unsupported entries, unclassifiable formulas, guard or local-rule failures and
budget exhaustion are `Unreplayed`, and `Unreplayed` falls through to every
previous disjunct of `check_node_cached`. The native marshal numbers certificate
entries in post order, so it never produces such ids. Tests:
`Z3NnfReplayTests.b10_malformed`/`b10_shared`, the OCaml bridge group
`sorted-NNF-certificate-replay` and `Z3CherryTests.nnf_premise_boundary`
(forward, self, negative and missing ids malformed and their documents
rejected; valid earlier and shared ids replayed; an unsupported rule with valid
ids pending; a valid certificate document certified).

**Measured coverage (fstar-build, b3c1e0bac producer).** Over the 583
incremental F* query logs, the pending `nnf-neg` obligations drop from 5,655 to
213 (OCaml; Cherry 5,570 to 211) and `nnf-pos` from 5,948 to 5,820 (Cherry 5,841
to 5,670). Re-running the replay steps on the remaining certificates, almost all
of them stop at an open `sk` step: a Skolem function of the enclosing binders,
whose choice equation holds only in an argument-dependent choice extension (now
built, next paragraph; on the re-swept NNF-bearing files the pending NNF obligations
drop to 73 `nnf-neg` and 10 `nnf-pos` on OCaml, 70 and 10 on Cherry, see the OCaml
checker report). The rest stop at closed `sk` steps over the 4,096-node
definition budget, at `intro-def`/`apply-def` naming steps, or at the binder
scope guard by exhausting its work budget (with an unbounded budget the same
guard passes; most of its units are the characters of the marshalled
`sort!<id>:<name>` sort names, charged at every sort comparison); none at a
local NNF rule, a scope or premise mismatch, or a malformed certificate. See
[the native validation](OCAML_CHECKER_REPORT.md#native-validation-and-the-fstar-build-replay-b3c1e0bac-producer).

**Model and trust.** `Z3NnfReplay.lemma_replay` proves, for every entry and
every scope the guard assigned to it, that its judgment holds in the Sorted
model at EVERY typed environment of that scope, by induction over the actual
entries; a quantifier step reads its body only at the binder extensions of the
same environment. Its model hypotheses are `Q.forall_model` and
`E.exists_model`; `Z3SortedRootDocument` derives both from R1 of one root model
(`lemma_root_check_node`, `lemma_root_check_document`), so no binder-cache,
body or legacy `model_sound`/`boolean_model` assumption is used. Inner `sk`
equations are true only in the choice extension that
`lemma_check_document_epsilon` builds from the ORIGINAL model (eligibility,
disjoint witnesses, acyclic order and freshness in every original assertion
are the unchanged gates). `rule_shape` now keeps `QuantifierIntroduction`, and
`entry_covered` requires every entry formula and binder sort of a consumed
certificate to be supported and the certificate to pass the scope guard
(`certificate_covered`, `lemma_certified_certificate_node`).

**Dependent Skolem functions** ([`Z3SortedDependentSkolem.fst`](Z3SortedDependentSkolem.fst)).
An open `sk` step concludes `(exists bs. B) ~ B[f_k(x_1..x_m)/y_k]` at an
assigned scope; `Z3Skolemization.definition_of` gives its dependencies (index
and sort of each argument, in argument order) and witness functions. The
eligibility gate (`DS.eligible`) requires `SK.valid` (every witness has domain
= the dependency sorts and range = its bound sort, complete argument tuples of
any arity, no repeated dependency, the body reads only the dependencies,
witnesses fresh in the body), at least one dependency (the zero-dependency case
stays on the closed route), uninterpreted witness functions outside every theory
and datatype operator (`function_safe`), a dependency scope of at most 4,096
positions in which every dependency is typed, and a closed, Boolean,
in-context closure; the step's formula must fit the same 4,096-node expression
budget as a closed inner step (`SP.dependent_definition`), otherwise it stays
pending. `Z3SortedProof.dependent_context` collects the steps of
every consumed certificate in document order (`SK.add_definition`: duplicates
once, conflicting redefinitions fail), orders them from the reversed collection
(`SK.order_context`), requires the dependent list followed by the closed
epsilon context to be an ordered context (no cycle; every dependent witness
fresh in every later body, closed bodies included) and every dependent witness
fresh in every original assertion; otherwise no dependent definition is used.
The model (`DS.doverride`, `DS.build`): for each typed argument tuple ONE whole
bound tuple is chosen by the Root ghost choice for the joint predicate "the
body holds at every environment of the dependency scope with these argument
values", read in the pre-extension interpretation of that build step (the
closed epsilon extension of the original model plus the older dependent
definitions); every witness returns its coordinate of that same tuple.
`SP.full_extension` starts from the original model, adds the closed context and
then the dependent definitions one after another: one extension per document,
in which every node is re-checked. Proved: `DS.lemma_instance` (at every environment of the dependency
scope the source and the instance agree in the extension: open substitution
under binders `lemma_substitute`, a witness application evaluates to the
coordinate `lemma_select`, coverage coincidence `lemma_covered`),
`DS.lemma_closure`, `DS.lemma_build_context`, `DS.lemma_build_inputs`,
`DS.lemma_build_closed`, `SP.lemma_full_extension`; the replay reads a closure at
the step's scope by the cross-scope coincidence `DS.lemma_coincide`
(`NR.lemma_closure_edge`); `Z3SortedRootDocument.lemma_root_doverride` shows the
extension is again a root model, `lemma_root_epsilon_extension` that it keeps
the original assertions and makes the equations and closures root-true, and the
off-route gate also checks the generated closures' coverage. Every dependent
witness is fresh in every OLDER body (closed bodies included; newer bodies may
mention it) and in every original input, and witnesses are pairwise distinct;
these are exactly the truths transported across an extension. The witness
necessarily occurs in the consumed certificate terms downstream of its `sk`
step; those are re-proved in the one extension rather than imported. The replay matches an open step against ANY assertion of the closure
shape `(forall cb. (= a b))` with that exact equation, as the closed route
matches any assertion `(= a b)`: an original input of that shape is a hypothesis
of the refutation and is true in the extension like every input, so this is
sound; type, scope and shape are checked. Limits: the dependent context is
all-or-nothing (one conflicting, cyclic, non-fresh or mis-ordered dependent
definition anywhere in the document leaves every dependent step pending, the
closed context unaffected), and the pending obligation does not name the
dependent gate that failed.

**Resources.** All walks are loops. The guard keeps its bounds; the replay
charges one budget of `binder_work_limit n` units for the node count of each
used entry formula, the counts of its premises at every use and one unit per
assertion for each `sk` step (an open step scans the assertions for its
equation and then for its closure, and recomputes its definition to check the
dependency sorts at its scopes; the formula is charged once), before comparing
terms. Exhaustion is PENDING.

**Tests.** [`Z3NnfReplayTests.fst`](Z3NnfReplayTests.fst) replays every row
above (n-ary De Morgan, double negation, implication, Boolean equality, xor,
ite, constants and opaque atoms, positive steps, duality over `[Int; Real]`
with a shadowing inner `Int` binder in both directions, a shared entry at two
scopes), rejects the mutations (wrong sign, swapped/missing/reused children,
wrong connective, canonical-name lookalikes, wrong binder sorts/order, a
capturing index, wrong polarity under a binder, bad roots, forward/self/
negative/missing ids, the `hnf.cpp` variant, a `quant-intro` root, an `sk` step that is
not an assertion, an open dependent `sk`), and checks two actual previously
pending corpus certificates (FStar.Nonempty query 2 node 11; the 14-entry
FStar.Class.TotalOrder.Raw query 1 node 43 with an inner closed `sk`) in
refutations certified by the root gates, a false mutant on satisfiable inputs
with a proved standard-model counter-model, a malformed certificate that
rejects its document and a reused witness that leaves the inner step pending.
The `nnf-pos` steps are checked by the same rules with the positive polarity
(an `nnf-pos` root may contain `nnf-neg` entries and conversely): positive
Boolean equality, xor and ite, an `nnf-pos` root over a negative duality under
binders, and mutations (an implication read as a disjunction, a quantifier
kind change, a negative body fact, a dual connective, an extra child, swapped
branches, out-of-scope and wrongly sorted indices, a self reference) that
stay pending or malformed. The propositional mutants also come with proved
standard-root-model counter-models of their claims, and so does the
wrong-polarity duality under the heterogeneous binders `[Int; Real]` (section
H: pending in a would-be refutation of inputs true in a standard root model).
[`Z3NnfSkolemTests.fst`](Z3NnfSkolemTests.fst) covers the Skolem contexts:
the ordering contract of the closed context (section A), the dependent Skolem
functions on two actual residual certificates (FStar.Nonempty q2 n92 and
Pulse.C.Types.Scalar-1 q1 n85, pending without the closure and replayed with
it; the n92 refutation certified on the epsilon route, falsified in every root
model, with a standard-root instance), a relational two-witness definition, and
the dependent mutants (section C: argument swaps, missing, repeated and extra
arguments, a captured index, both polarities, freshness, reuse, cycles, the
closed route, the scope cap, reinterpretation, mixed closed/dependent order, a
satisfiable wrong-polarity refutation with a proved counter-model, an accepted
negative step, the scope gate, duplicates and a reverse-order chain).

Native tests: the OCaml bridge group `sorted-NNF-certificate-replay` requires
an NNF-rooted certificate in each producer proof of the synthetic probes and
none of them pending, and `test_native_checker.py`
(`test_sorted_route_replays_nnf_certificates`) requires `ACCEPT` for them in
batch and interactive mode on both backends. The first native run showed that
the original `ite`/`iff`/`xor` probes fixed their Boolean by a unit assertion,
so the preprocessor substituted it and their proofs had no NNF certificate
(the old checker accepted them too); they were replaced by probes without a
unit Boolean (and `xor` under a universal was added), on which the previous
checker reports one pending `nnf-neg`/`nnf-pos` obligation each.

## Typed Real certificates and ITE rewrite laws (Sorted route)

The Sorted kernel (`Z3SortedProof.check_node_cached`, used by `check_document_epsilon`, i.e. by both native
frontends whenever a query has datatype metadata or `--sorted-core` is given) checks Real arithmetic against a typed
Real semantics and replays three sort-generic `ite` rewrite laws. The default legacy route is unchanged.

**Semantics (design A).** `T.scalar_model` keeps its Int carrier; Real is added beside it.
[`Z3SortedReal.fst`](Z3SortedReal.fst) defines a Real carrier (an injection of the base Real values into
`FStar.Real.real`), the executable classification of canonical Real declarations (rational numerals `n/d` with
`d > 0`, n-ary `+ * -`, `/`, `to_real`, `<= < >= >`; exact declaration identity, interpretation tag, sorts and
parameters, never a name), the law predicate `real_laws s bc model other reals` over the existing Sorted
interpretation and the kernel-facing `real_model s bc model other = exists reals. real_laws ...`. The laws are, per
classified declaration: numerals denote `n/d`; `+ * -` denote the field operations; `x / y` satisfies
`(x / y) * y = x` only for a nonzero divisor (`x/0` is a free model choice, no div0 law); `to_real x` is the value of
`x` in the SAME integer carrier as the Int valuation; comparisons have their order truth. `real_primitive s` (Real is
not registered as a datatype sort of the checked schema `s`) is part of `real_laws`, so `real_model` can only hold
on schemas where the executed schema check opens the gate. [`Z3SortedRealRoot.fst`](Z3SortedRealRoot.fst) derives
`real_laws` with the identity carrier from R2 of EVERY root model over a Real-primitive schema
(`lemma_root_real_laws`, `lemma_root_real_model`), proves it jointly with R1–R6 in the standard root
(`lemma_standard_real_root`) and shows it is not vacuous: a Real variable valued 1/2 satisfies `0 < x` and `x < 1`
while the Int rounding `x <= 1 - 1` is false (`lemma_real_rounding_countermodel`). A checked schema that registers
a datatype named Real is accepted by `S.valid` but closes the gate (`lemma_real_datatype_refused`).

**Checks.** [`Z3SortedRealLinear.fst`](Z3SortedRealLinear.fst) proves the existing executable arithmetic against one
mixed numeric valuation (Int terms through the integer carrier, Real terms through the Real carrier):
`A.linearize` (Real `+ * -`, `/` only by a constant polynomial with a nonzero constant, `to_real`, other terms opaque
atoms), `A.literal`, `A.prepare_literal`, `P.accepts`, and the rewrite checks `constraint_of`,
`boolean_equivalent`, `numeric_equivalent` and binary `commuted_product` of
[`Z3ArithmeticRewrite.fst`](Z3ArithmeticRewrite.fst) (`real_equivalent`). Two disjuncts of `check_node_cached`,
tried after every previous Int path, read them:

| disjunct | accepts | contract |
|---|---|---|
| `real_farkas s node` | an `ArithmeticFarkas cs` node whose supplied weights `cs` refute exactly the node's literals (premise propositions positive, conclusion literals negated) by `LIN.check_numeric_contradiction`: `real_primitive s`, the 4096-node budget, every literal (zero-weight ones too) a closed Boolean formula, one weight per literal, `A.prepare`/`P.accepts` | `lemma_real_contradiction` |
| `real_rewrite s node` | a premise-free `RewriteRule` node `a = b` (closed) with `real_primitive s` and `LIN.real_equivalent a b` | `lemma_real_rewrite` |
| `ite_rewrite node` (no schema gate, tried last) | a premise-free `RewriteRule` node `a = b` (closed) with `NR.ite_rewritten a b` (the ITE laws below) | `lemma_ite_rewrite` (no hypothesis) |

Strictness is per literal: the Int strict-bound adjustment (`a < b` to `a + 1 <= b`) applies exactly to literals
whose sides are Int; Real strict literals stay strict; a contradiction at a non-positive constant needs a
NONZERO-weight strict non-Int literal (`lemma_zero_contradiction_needs_weighted_strict`); a zero weight contributes
the non-strict zero polynomial whatever its literal. As on the Int path, `A.weighted` reads a negative weight on an
inequality as its magnitude (sound: a non-negative multiple of a true inequality); such a certificate is accepted
exactly when its magnitudes form a valid certificate, so not every negative-sign mutant is refused. Int/Real mixing
is supported only through explicit `to_real` (each literal compares two terms of one sort).

**Theorem doors and their Root discharge.** The only new hypothesis is `RL.real_model s bc eq other`, required
exactly where a Real law is read: `SP.lemma_check_node_cached` (`real_node s node ==> real_model`; for a
quant-intro node also `real_primitive s ==> real_model`), `SP.lemma_entries` / `SP.lemma_check_document`
(`needs_real_semantics s entries ==> real_model`, where `needs_real_semantics` is `real_primitive s` and an
`ArithmeticFarkas` or `RewriteRule` entry or an entry whose formula is a closed Real order clause
(`real_order_entry`); for binder certificates `real_primitive s ==> real_model`) and
`SP.lemma_check_document_epsilon` (`real_primitive s ==> real_model`, transferred to the epsilon/dependent-Skolem
extension by `SP.lemma_full_extension_real_model`: a Skolem witness is never a classified Real operator,
[`Z3SortedRealExtension.fst`](Z3SortedRealExtension.fst)). Generic documents without Farkas, rewrite or binder
entries keep their unconditional statements. `Z3SortedRootDocument.lemma_root_check_node`,
`lemma_root_check_document` and `lemma_root_check_document_epsilon` (hence `lemma_root_certified` and
`lemma_root_certified_epsilon`) discharge the premise with `Z3SortedRealRoot.lemma_root_real_model` of the SAME
root model; `lemma_epsilon_real_laws` / `lemma_epsilon_real_agreement` show that the epsilon extension keeps every
canonical Real operator. The read view keeps `ArithmeticFarkas` coefficients and the `RewriteRule` label; coverage
needs no extension (coefficients are numbers; every literal and atom is a subterm of a covered entry formula).

**Quant-intro replay.** `Z3NnfReplay.replay_with real` takes the gate as a parameter; `Z3SortedProof` passes
`RL.real_primitive s`, and `replay` (every previous caller) is `replay_with false`. Under the gate a `rewrite` leaf
the previous checks refuse is replayed when `LIN.real_equivalent` decides it (`real_rewrite_ok`); its lemma
(`lemma_real_rewrite_at`) requires `real ==> RL.real_model`, so a test that sets the flag must supply the Real laws
(which contain `real_primitive`). Captured Pulse.Class.PtsTo q1 nodes 114 (`>` to `not <=`, the renormalized `>=`)
and 176 (binary Real `*` commutation) replay with the gate and stay pending without it
([`Z3SortedRealReplayTests.fst`](Z3SortedRealReplayTests.fst)). On the saved capture of that query (Marshal (schema, doc), sha256 `a3380b33...`, 208 entries; PARTIAL 15 with
the 9af checker), the same check now leaves 6 pending (5 `th-lemma`, 1 `rewrite`): the 7 Real Farkas steps are
accepted by `real_farkas` and quant-intro nodes 114 and 176 by the gated replay.

**ITE laws (S1).** `Z3NnfReplay.ite_rewritten` replays, at every result sort, `ite (not c) x y = ite c y x`,
`ite c1 x (ite c2 x y) = ite (or c1 c2) x y` and `ite c1 (ite c2 x y) y = ite (and c1 c2) x y` (with the
producer's one-level flattening of `and`), by exact structural identity and the canonical `ite` declaration
(`T.Choice`); `lemma_ite_rewritten_at` proves them in every Sorted model at every scope. A Real subterm is an
opaque operand of these laws. They apply on two paths: as `rewrite` leaves of a replayed `quant-intro` certificate
(at the leaf's binder scope, `rewrite_ok`), and as a premise-free top-level `rewrite` step with a closed equation,
the direct path `SP.ite_rewrite` (the same check at the scope `[]`). The direct path has no schema gate and no new
hypothesis: `lemma_ite_rewrite` is `lemma_ite_rewritten_at` at the scope `[]` and the empty environment, so the
node, document, epsilon and Root theorems cover it unchanged; the read view keeps the `RewriteRule` label (the
decision is unchanged on it) and the equation is a covered entry formula.
They are the replayed fragment of the captured Term-ITE leaves; the residual ITE shapes recorded on the captured
cohort stay pending (no law for them yet): 5 leaves `ite c1 (ite c2 t1 t2) t1 = ite (and c1 (not c2)) t2 t1`
(`bool_rewriter::mk_ite_core`, merge with a negated inner guard), 6 or-with-negation merges, and 1 leaf that
lifts an `ite` into a function application. The laws do not read the Real gate.

**Real equality/order laws.** Two more checks read the same Real laws (no new hypothesis, no new Root law).

- `SP.real_order` is the Real mirror of the Int `order_clause`: the producer's arith_eq_adapter (`th-lemma ... triangle-eq`)
  clauses over two Real terms x and y, `not (x = y) \/ c` with c one of `x <= y`, `x >= y`, `x = y` or the same on
  `x + (-1)*y` / `(-1)*y + x` against the numeral 0, and the three-literal `(x = y) \/ not c1 \/ not c2` with c1, c2 opposite
  bounds on x - y (any literal order). Formula-based like the Int check: the rule label, premises and payload are never
  read (any rule but the leaves and the lemma rule), the Root read view is unchanged and no term beyond the covered entry
  formula is consumed. x and y are arbitrary Real terms read only as their typed Real values and matched by
  expression identity (nothing is linearized or searched). The equation, comparisons, `+`, `*` and the numerals 0 and
  -1 are classified by their full canonical declaration (`RL.classify`: interpretation tag, domain, range, numeral
  parameters), never by name, so a counterfeit or twin declaration, a numeral written -2/2 and the Real `-` are
  outside the fragment; a strict comparison is not implied by an equation and is no bound. At most three literals, and
  the clause must pass `NR.shallow` (4,096 levels, 2^20 pops, iterative) before any comparison. The gate is the
  executed schema check `RL.real_primitive s`. Laws: `RO.lemma_real_offset`, `lemma_real_implied_by_equation`,
  `lemma_real_bound` (Z3SortedRealOrder) and `SP.lemma_real_equation_order`, `lemma_real_antisymmetric`,
  `lemma_real_order_clause`, `lemma_real_order` (every Sorted model satisfying the Real laws, hence every root
  model). It is a disjunct of `check_node_cached` next to `real_rewrite`, is part of `real_node`, and its entries
  are counted by `needs_real_semantics`.
- `LIN.real_equivalent` (the Real rewrite check, used by `SP.real_rewrite` and, through `real_rewrite_ok`, by the
  rewrite leaves of quant-intro certificates) also decides Real equations: the difference polynomials of the two
  equations are the same, opposite or proportional by a nonzero factor (`LIN.real_equation_equivalent`, the existing
  `RW.equation_equivalent` read on Real equations only), and an equation whose monomials all cancel is the canonical
  `true` or `false` (`LIN.real_constant_equation`). `LIN.lemma_real_equation`, `lemma_real_equation_equivalent` and
  `lemma_real_constant_equation` hold at every scope and typed environment, so the quant-intro replay is covered by
  the unchanged `NR.lemma_real_rewrite_at`. Budgets are unchanged (256 nodes per side, linearize fuel 64). The
  proportionality test (`RW.proportional_polynomial false`) reads only the integer NUMERATORS of the two difference
  polynomials and not their denominators. That is complete and sound for equations, not a limitation: a difference
  polynomial stands for its numerator divided by a positive denominator, so two equations are equivalent exactly when
  the numerators are proportional by a nonzero rational factor, whatever the denominators are (`c/2 = 1/4` and
  `2c = 1` have difference polynomials with denominators 8 and 1 and equal numerators and are accepted, while
  `c/2 = 1/4` and `2c = 1/2` are different equations, c = 1/2 against c = 1/4, and stay pending). The invariant is a
  theorem for every pair of positive denominators (`Z3SortedRealOrderTests.o6_equation_zero_rational`, from
  `RW.lemma_proportional_polynomial` and `lemma_denotes_zero`), and the tests (section O6) run the production helper
  on Real fractions: non-unit and mismatched denominators, positive and negative rational scales, both
  orientations, and the refusals of a changed constant, sign, ratio, a zero factor and strictness. Int equations,
  negated equations, `to_int`/`is_int` and nonlinear normalization are outside.

Tests: [`Z3SortedRealOrderTests.fst`](Z3SortedRealOrderTests.fst) (the hosted shapes, every refusal, the two-route
documents RootCertified and false in every root model, counter-models of the false mutants at concrete Real
environments in the standard root, the quant-intro leaf, the laws in every root model), OCaml groups
`sorted-real-order-clauses` and `sorted-real-equation-rewrites` (z3's own proofs, marshalled mutants, the depth bound
n = 4,093 / 4,094 / 200,000), Cherry `real_order_controls` and `real_equation_controls`. A valid clause written in an
unsupported shape (Real `-`, a bound not against the numeral 0, a strict literal, four literals) is a shape-refusal
control in these tests, not a false mutant.

**Unsupported (pending, with the rule's own diagnostic).** `to_int`, `is_int` (no interpretation tag in the
operator vocabulary), `div0`/Real division by zero, floor, Int `div`/`mod` at Real, nonlinear Real products
beyond binary commutation, n-ary factor permutations, `(x = y) = (x <= y and x >= y)` and other equality splits,
coefficient-free Real consequences (no recomputed Real certificate), mixed comparisons without `to_real`.
Tests: [`Z3SortedRealTests.fst`](Z3SortedRealTests.fst), [`Z3SortedRealDocumentTests.fst`](Z3SortedRealDocumentTests.fst),
[`Z3SortedRealReplayTests.fst`](Z3SortedRealReplayTests.fst), OCaml group `sorted-real-Farkas`, Cherry
`real_farkas_controls`, and `test_sorted_real_certificates_in_both_modes`; for the direct ITE path, section R6 of
`Z3SortedRealDocumentTests.fst` (the three laws at Bool, Int, Real, an uninterpreted sort, an array sort, a datatype
and under function applications, RootCertified and false in every root model; also certified with the Real gate
closed; branch, operator, guard, declaration and twin-constant mutants pending), OCaml group
`sorted-direct-ite-rewrites`, Cherry `direct_ite_controls` and `test_sorted_direct_ite_rewrites_in_both_modes`.

## Typed Int division laws and the Root model contract

Until run e78cd96c the typed Root class (`Z3TypedRoot.root_model`, R1-R6) left the canonical Int `div` and `mod` free at EVERY
divisor, so `(or (= d 0) (>= (mod x d) 0))` was false in some root models (retained countermodel: `mod` the constant -1 and
d = 1, `Z3SortedDivisionRoot.mod_minus_one`). The contract is now narrowed to SMT-LIB's own semantics and nothing beyond:

- `Z3TypedRoot` has two more operator classes, `IntDiv` and `IntMod`, for the canonical declarations only
  (`canonical_int_division`: the exact name `div`/`mod`, the kind tag `Z3IntegerDivision.op_idiv` 33 / `op_mod` 34, the domain
  `[Int; Int]`, the range Int and no parameter). A twin with another name, tag, arity, sort (a Real division, a sort merely named
  Int) or a parameter, and the Real division tag at Int, stay `Other` (free), pinned in `Z3TypedRootTests.int_division_classes`.
- At a NONZERO divisor R2 fixes the value: `div` is F*'s `x / y`, `mod` is `x % y` (Euclidean: `x = y*(x/y) + x%y`,
  `0 <= x%y < |y|`, identical to Z3's `div`/`mod` for every divisor); at a ZERO divisor the value stays a free choice of the model
  (`uf.apply`), exactly as for Real division. Nothing is assumed about `div0`/`mod0`: no identity between a division and its alias
  is provable, and the guarded clauses are valid only under the guard.
- The class is smaller, so every theorem quantified over root models keeps its proof (a stronger hypothesis); the class stays
  inhabited: `lemma_standard_root` is unchanged (the standard model reads `interpreted`) and
  `Z3SortedDivisionRoot.lemma_standard_division_root` / `lemma_standard_joint_root` show that the standard root of EVERY
  uninterpreted carrier and free symbol satisfies R1-R6, the Real laws (when the Real gate holds) and the Sorted division laws at
  once. Epsilon/dependent-Skolem overrides only change tagless witness symbols, so they keep the laws
  (`Z3SortedDivisionExtension`, and `Z3SortedRootDocument.lemma_root_epsilon_extension` for the root laws).
- The Sorted layers (`Z3SortedInteger`, `Z3SortedSemantics`) are unchanged and still pass `div`/`mod` to the interpretation;
  `Z3SortedIntDivision.division_laws` is a hypothesis about that interpretation, DERIVED from R2 of the same root model
  (`Z3SortedDivisionRoot.lemma_root_division_laws`), never assumed. The legacy `Z3IntegerDivision.division_model` is not used.

**Guarded Int div/mod clauses.** `SP.division_order` checks z3's arithmetic div/mod axioms for a non-numeral divisor, the
producer's premise-free `th-lemma` clauses over two Int terms x and d, with q = `div x d` and m = `mod x d` the CANONICAL
declarations (`DV.classify`: exact name, kind tag, domain, range and parameters, never a name alone):

| template | clause |
|---|---|
| mod bounded below | `d = 0 \/ m >= 0` |
| mod bounded above, positive divisor | `d <= 0 \/ m + (-1)*d <= -1` (`AR.difference`: either operand order) |
| mod bounded above, negative divisor | `d >= 0 \/ m + d <= -1` |
| decomposition | `d = 0 \/ x = d*q + m` (and the sides of the equation swapped) |

in either literal order, with the guard against the canonical Int numeral 0, the bound against the canonical Int numeral -1, `+`
and `*` the canonical Int operators (two operands) and the guard's d the very d of the division. x and d are arbitrary Int terms
(an opaque application, a datatype accessor, a product), read only as their typed Int values in the same Sorted interpretation
and matched by expression identity. Formula-based: the rule label, premises and payload are never read (any rule but the leaves
and the lemma rule), the Root read view is unchanged and no term beyond the covered entry formula is consumed. Two literals, and
the clause must pass `NR.shallow` (4,096 levels, 2^20 pops, iterative) before any comparison. No schema gate: Int is never a
datatype sort of a checked schema. Laws: `SP.lemma_remainder_lower`, `lemma_remainder_upper_positive`,
`lemma_remainder_upper_negative`, `lemma_decomposed`, `lemma_remainder_decomposition`, `lemma_division_clause`,
`lemma_division_order` (every Sorted model satisfying `DV.division_laws`, hence every root model), from the atoms of
`Z3SortedIntDivision` (`zero_guard`, `sign_guard`, `remainder_arguments`, `quotient_arguments` and their lemmas at every scope)
and `DV.lemma_euclid`. It is a disjunct of `check_node_cached` next to `real_order`, is part of `division_node`, and its entries
are counted by `needs_division_semantics`.

Outside (pending): a clause with another guard or bound (a weaker guard such as `d <= 0 \/ m >= 0` is a VALID clause in an
unsupported shape), zero on the left of the guard, a commuted product `(div x d) * d`, summands exchanged, a strict bound, a
third literal, an unguarded alias of a division with its `div0`/`mod0`, a lookalike `div`/`mod` (no kind tag, a twin parameter,
another name, the Real division tag, a sort merely named Int) and a counterfeit guard `=` or numeral. The producer's other
div/mod lemmas (`(>= (+ x (* -1 (* (div x d) d))) 0)`, a `d = 2` substitution, five literals) are not in this fragment.

**Theorem doors.** `SP.lemma_check_node_cached` requires `division_node node ==> DV.division_laws s bc eq other`;
`SP.lemma_entries` and `SP.lemma_check_document` require `needs_division_semantics entries ==> DV.division_laws`;
`SP.lemma_check_document_epsilon` requires `DV.division_laws s bc eq other` and transfers it to the epsilon and dependent-Skolem
extension (`SP.lemma_full_extension_division`: a witness is never a classified division operator,
[`Z3SortedDivisionExtension.fst`](Z3SortedDivisionExtension.fst)). Documents without a guarded division clause keep their
unconditional statements. `Z3SortedRootDocument.lemma_root_check_node`, `lemma_root_check_document` and
`lemma_root_check_document_epsilon` discharge the premise with `Z3SortedDivisionRoot.lemma_root_division_laws` of the SAME root
model.

Tests: [`Z3SortedIntDivisionTests.fst`](Z3SortedIntDivisionTests.fst) (the five templates over opaque, compound and
uninterpreted-function operands in both literal orders checked by `division_order` alone; the refusals: missing or wrong guard,
wrong bound, mod and div exchanged, a guard on x, a wrong coefficient or operand of the decomposition, lookalike declarations,
the unguarded div0 alias; valid clauses in an unsupported shape as SHAPE controls, not false mutants; documents RootCertified on
both routes and false in every root model, the same documents with a wrong clause RootPending; the clause theorem in every root
model; counter-models of the false mutants in the standard root of an adversarial free choice at a zero divisor, at concrete
typed environments, and the positive instances), OCaml group `sorted-int-division-clauses` (z3's own proofs, marshalled
mutants, the depth bound n = 4,093 / 4,094 / 200,000), Cherry `int_division_controls`.

## Native LP inference certificates

Arithmetic equality propagation can also be checked without producer-supplied
weights. `Z3LpReplay.fst` constructs the two non-strict bounds of the actual
numeric equality conclusion. Bounded Fourier-Motzkin synthesis in
`Z3LinearArithmeticAst.fst` proposes exact Farkas weights for each bound;
the existing verified checker independently replays both certificates
against the original premises before the equality is derived. Synthesis
is limited to 32 literals, 16 elimination rounds, and 128 rows. Unsupported
inputs or exhausted search retain an obligation. Integer strict-bound
strengthening is not applied to reals, and no arithmetic hint or native
solver verdict substitutes for either replay.

Triangle-equality clauses accept either order of the opposing bounds,
including reversed equality operands. Both orientations use the existing
proved equality-to-bounds equivalence. These extensions retain the legacy
numeric-model limitations described above; they do not repair that model.

With proofs enabled, `theory_lra` exports supported
`lp::evidence_manager::proof_expression` derivations as native proof DAGs,
not just their flattened dependency sets. The arithmetic `th-lemma` hints
are `lp-input`, `lp-linear`, `lp-integer-tighten`, `lp-integer-lattice`,
`lp-gomory`, `lp-monomial-substitute`, `lp-monomial-interval`, and
`lp-discharge`. Each node carries its step index and has a shared
`lp-context` node as its first parent. Discharge additionally uses an
ordinary native `lemma` node to close the temporary hypothesis.

The context proves only `true`. Its declaration parameters carry an
explicit, versioned certificate; they do not assert its input facts.
The C++ checker replays the arithmetic rules, validates variable and
monomial definitions against the actual bound ASTs, and checks every
native inference's premise and conclusion formulas. Export rejects
unmatched open inputs, including recycled probe constraints, rather than
turning them into axioms. Unsupported evidence keeps an explicit
unsupported hint (or the existing independently checked linear Farkas
certificate), not a fabricated derivation.

External consumers can obtain the typed parameters through the native
declaration-parameter APIs. The version-1 context parameter layout, after
`arith, lp-context`, is:

| Field | Encoding |
|---|---|
| Header | Version `1`, variable count. |
| Each variable | Native expression AST, integer flag, linear definition length, then `(rational coefficient, stable variable index)` pairs. |
| Monomials | Count, then each column index, factor count, and factor indices. |
| Steps | Count, then each rule tag, conclusion fact, input index, assumption step, recipe ID, equation fact, pivot, monomial definition index, source, divisor, premise count, `(step, coefficient)` pairs, bound count, and `(column, lower-premise-position, upper-premise-position)` triples. |
| Root | Root step index. |

A fact contains the relation tag (`0` = `<=`, `1` = `<`, `2` = `=`,
`3` = `>`, `4` = `>=`), contradiction flag, rational right-hand side,
infinitesimal component (required to be zero), and a length-prefixed
linear left-hand side. Rule tags follow the hint order above, starting at
zero. Absent indices are `4294967295`. Premise references are topological;
used variable and rule-data references are range checked.
An `lp-linear` node also supplies local rational weights, after its
step index: one per arithmetic parent and, for a non-contradiction
conclusion, one for that conclusion. These account for denominator
clearing when native integer formulas are emitted.

[`scripts/check_lp_proof.py`](../scripts/check_lp_proof.py) independently
replays all these arithmetic rules with Python exact rational and ring
arithmetic. `check_lp_nodes(proof)` takes a native Z3Py proof; it does not
invoke a solver, simplifier, or the C++ evidence checker. Its command-line
driver first produces a proof from an SMT-LIB file, then reports checked
LP nodes separately from **unchecked non-LP nodes**. This is an arithmetic
subchecker, not a complete SMT proof checker or an F* soundness theorem.

The OCaml native bridge feeds local linear and input-conversion weights
to the existing verified Farkas kernel, which checks the actual native
formulas independently of the context certificate. Steps outside that
kernel's fragment, including integer cuts and monomial rules, remain
explicit obligations named `arith/lp-...`. Python/C++ replay coverage must
not be confused with obligation-free F*/Pulse checking.

## Experiments and coverage

| Experiment | Report and tools |
|---|---|
| Historical QF_AX/QF_UF proof production, rewrite-matcher coverage, timing, and follow-up matchers | [Archived benchmark report](QF_AX_QF_UF_BENCHMARK_REPORT.md); [`tools/analyze_benchmarks.py`](tools/analyze_benchmarks.py) remains for archived results; the exporter-dependent runner was removed. |
| Nine-logic SMT-LIB cross-cut, native coverage extensions, and producer updates | [Current cross-cut](SMTLIB_CROSSCUT_REPORT.md) includes the direct native interface; [arithmetic integration results](ARITHMETIC_CERTIFICATE_REPORT.md) preserve the earlier evaluation. |
| Occurrence coverage of clausal proof rules, distinguishing proved rules from trusted obligations | [Resolution report](RESOLUTION_CHECKER_REPORT.md) and [scope](RESOLUTION_CHECKER_SCOPE.md); [`tools/proof_rule_coverage.py`](tools/proof_rule_coverage.py) |
| Experimental rewrite-leaf tagging | [Rewrite-rule tags report](REWRITE_RULE_TAGS_REPORT.md); [`Z3RewriteRuleTags.fst`](Z3RewriteRuleTags.fst), [`tools/parse_rewrite_tags.py`](tools/parse_rewrite_tags.py) |

Rule-vocabulary coverage is not the same as complete semantic checking:
trusted rules and unmatched leaves must still be accounted for. Benchmark
reports record point-in-time measurements and follow-up results.

The rewrite-tagging call site was **reverted from master**. Its report and
F* lemmas document an experiment, not current proof-production behavior;
the captured local benchmark proofs are not reproducible with current
master's tagging behavior.

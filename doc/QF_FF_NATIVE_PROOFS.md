# Native certificate production: replacement contract for PR2

The replacement must produce evidence during the computation that establishes
UNSAT. A second solver that tries to reproduce the result is a baseline, not the
architecture. This document records the work still needed; the opt-in `native`
backend is not yet a certificate for arbitrary native `check-sat` execution.

## Port onto merged upstream Z3 (2026-10-14)

The certificate producer has been ported onto upstream `master` at `9e2d35b55`,
after the QF_FF solver merge. The field algebra now lives under `src/math/ff/`
and the SMT adapter uses `ff::solver` from `src/ast/ff/`. The certificate-specific
code builds on these interfaces; ordinary solving retains its existing defaults.

On the same 390 distinct FMCAD26 `FF_UNSAT_SMT` inputs, with a ten-second
whole-pipeline deadline, four workers and independent original-input, FFPacheck
and Carcara checks, the port produced 378 bundles and checked **377/390**. Its
checked-input set exactly matches the pre-merge native/circuits campaign. The
remaining outcomes are 12 unavailable and one timeout; the earlier campaign
had 11 unavailable and two timeouts. All 27 core and 11 proof acceptance checks
passed locally, including corruption rejection and C++/Python API tests. The
benchmark runner on this host used a local `ps` process-inspection shim because
`psutil` was unavailable. Production and checking stage times are comparable;
whole-pipeline supervisor times should not be used for a speed claim against
the earlier run. Earlier measurements below describe their historical revisions.

The regression suite used for this validation comes from the certificate branch.
Upstream keeps finite-field regressions in `Z3Prover/z3test`; the new proof tests
must be migrated there before the port can claim the same coverage in CI.

## Evidence and acceptance

The native certificate backend calls `engine::solve`; it does not reconstruct a second basis schedule. The evidence DAG is independent of its Alethe/PAC serialization. Every input is
bound to an original active assertion or to a checked local hypothesis. Derived
lemmas carry evidence; a dependency set alone is insufficient. Every split must
discharge all alternatives and local hypotheses before its parent closes.
Caching must retain and remap proof references, not merely premise indices.
No unsupported path may emit an apparently complete certificate.

The pipeline can independently select `--backend native` for native algebra and `--boolean-backend native` for native SAT; the legacy choices remain available as comparison baselines. The existing independent original-input checker remains mandatory. External
Carcara/FFPacheck acceptance is reported separately from original-input binding;
new field-specific rules require an implemented checker and cannot be admitted
as holes. Lean checking is not implemented by this work.

## Audited implementation paths

| Native computation | Recording status / required evidence |
| --- | --- |
| Wire elimination (`engine::eliminate`) | Implemented opt-in observer; exact substitution identity, including nonlinear definitions and repeated powers |
| Legacy basis (`engine::basis`, `reduce`, `batch_reduce`) | Implemented opt-in handles for actual scalar and sparse matrix operations, including fused/geobucket and packed/lazy variants |
| F4 basis (`ff_f4.cpp`) | Native engine invokes the recording backend and composes residual-input evidence with preceding substitutions |
| Basis reuse | Still refuses recording; cache entries need replayable, correctly scoped evidence |
| AST preprocessing (`ff_simplify_tactic.cpp`) | Rewrites, solved equations, zero-test rewrites and compact definitions need checked connections to original assertions |
| Uniqueness (`ff_unique_tactic.cpp`, shared `ff_unique.h`) | Ring recording covers class merges, assigned values, matching linear definitions, distinct-output zero tests and bounded Boolean-domain branches. Digit injectivity and coincident-output zero tests still need evidence |
| Bit reasoning (`propagate_bits`, `small_bits`) | Boolean premises, no-wrap bounds and exhaustive assignment coverage must be recorded |
| Finite-field roots and completion | Frobenius axioms, quotient/minimal-polynomial derivations, root completeness and branch closure need proof rules |
| Tiny-field search (`ff_tiny.cpp`) | Domain pruning and exhaustive closure need local explanations |
| Boolean combination | `--boolean-backend integrated` now records polynomial conflicts in a native `sat::extension` during one CDCL search. `incremental` retains the existing separate SAT/field sessions. Both export checked resolution; ordinary `ff_sat_tactic.cpp` and SMT equality-engine integration remain separate work |
| SMT combination (`theory_ff.cpp`) | Explanations must connect field lemmas to equality-engine/SAT premises with scope-safe evidence |
| BV fallback (`ff2bv_tactic.cpp`, theory fallback) | Check encoding equivalence, bit-vector/SAT refutation and premise connection, or explicitly refuse certificate production |

SAT witness probes do not need refutation certificates: they can only establish
SAT after independent model checking. Failed or incomplete probes cannot close
an UNSAT branch. Constant contradictions must retain the derivation of the
constant, including when an earlier transformation made the equation constant.

## Native SAT/theory conflict recording

Select the experimental integration with:

```sh
python3 scripts/ff_proof_pipeline.py problem.smt2 --out /tmp/ff-integrated \
  --z3 build/z3 --backend native --boolean-backend integrated \
  --carcara "$CARCARA" --ffpacheck "$FFPACHECK"
```

For the Boolean input profile this invokes `ff-integrated-certify` once. A native
SAT extension selects relevant field literals at a final check, normalizes them
through a shared AST cache, and invokes the existing recording algebra engine.
It records the polynomial refutation before adding the negated premise core as
an ordinary SAT clause after restarting at the root. CDCL propagates the new
clause and continues with its learned clauses. There are no opaque theory justifications.
Pure literal-conjunction inputs still use the cheaper standalone field command.

`(ff-integrated-certify :diagnostics true)` reports per-check equation/variable
counts, proof construction/serialization time and algebra resource counters on
the diagnostic stream. It leaves the certificate stream unchanged. Exhaustion
reasons distinguish polynomial terms, polynomial work, proof nodes, proof bytes
and normalization storage when those limits are reached; unclassified limits
remain `resource`. This option is off by default.

The producer registers positive equalities and explicit inverse-witness equations
for negative literals. These registrations are an internal protocol, not trusted
assertions about the original problem. The consumer binds every retained premise
and variable to the original Boolean/field term graph, checks its polynomial DAG,
and elaborates native clauses into explicit resolution. A native `unsat` response
alone cannot complete a bundle. Original-input checking, standalone FFPacheck,
and Carcara invoking FFPacheck remain mandatory. No new checker rule or Lean
acceptance is claimed.

AST normalization caches contain only declaration-dependent polynomials. Each
field check has fresh arithmetic/proof state and a compact variable map, using a
fresh traversal order so earlier assignments do not change variable ordering.
Proof factors are renamed back before serialization. Each command owns its SAT
state, clauses, AST cache and evidence; pop/reset or a failed command cannot
reuse stale field lemmas. Cancellation rejects incomplete output. An immediate
input-CNF contradiction bypasses SAT conflict analysis of an empty trail and is
still checked independently by the consumer.

The command is bounded by the existing polynomial work/term limits, 100,000 nodes
per field proof, at most 1,024 field lemmas, bounded normalization storage, a
100,000-clause/1,000,000-literal trace and 32 MiB output. Inconclusive theory
checks return unavailable, never SAT or an uncertified UNSAT. Theory checks
currently run at completed Boolean assignments; early theory propagation and
proofs for general SMT equality-engine combinations are not implemented here.
This does not enable native Z3 proof objects or cover every ordinary `check-sat`
UNSAT path.

The Boolean replay uses persistent two-literal watches over globally justified
clauses, with fresh assignments/reasons for every RUP query. Successful steps
still emit explicit resolution. It first tries a unit-propagation refutation
from the checked field lemmas; otherwise it replays the native trace. Both paths
share the existing 10-million-work budget. A 3,200-query differential regression
compares acceptance with an independent scan oracle and replays all generated
resolution steps as the clause database grows.

All 35 acceptance checks pass, including 38 externally checked integration
bundles, 27 exhaustive mixed SAT controls, seven certified small UNSAT cases,
two explicitly unavailable cases, eight corrupt native-response checks, scope
and work-budget recovery, and timer cancellation followed by another command
in the same process. The empty-trail regression was added after the cancellation
exercise exposed that producer crash.

## Shared uniqueness recording

The native certificate path now invokes the same propagation core as `ff-unique`
before entering `engine::solve`. Each union edge proves `v-parent[v]=0`, each
assigned value proves `root-value=0`, and canonicalization composes these
identities with exact substitution evidence. Old definition keys remain valid
identities and are reduced through the current class state before a merge.
For `a*y+r=0` and `b*z+s=0` with `-r/a=-s/b`, their normalized difference proves
`y-z=0` without globally expanding the circuit.

Zero-test matching also has a ring derivation. For a common monic expression `M`,
let the four proved equations be `A=y-c+alpha*z*M`, `B=t-c+beta*w*M`,
`C=(y-d)*M`, and `D=(t-d)*M`. Then

```
(y-d)*B - (t-d)*A - beta*w*C + alpha*z*D = (d-c)*(y-t).
```

When `d!=c`, multiplication by its inverse proves the equality. When `d==c`,
this identity is insufficient; recording deliberately skips that rule.
Digit inference remains disabled with an observer. Boolean branches now use the
ring discharge described below.
No new trusted checker rule or original-input axiom is introduced.

`ff-certify :backend native :unique false` disables this stage for ablation.
It is not yet a proof of arbitrary `ff-unique` tactic executions or normal
`check-sat`: the shared core's supported subset runs on normalized input
polynomials. Native AST preprocessing and full SAT/theory integration remain
separate open work. A stalled local attempt leaves input equations unchanged;
its work and valid unused DAG nodes remain charged to the same global budget.
The published `auto` reconstruction backend and normal solver defaults are
unchanged.

Regression coverage includes 69 independently checked uniqueness proofs (five
fields through 521 bits, non-unit pivots, repeated powers, reordered equations,
stale keys and zero tests), changed-premise rejection, SAT controls, incremental
scope checks, and C++ checks that close 24-layer circuits and zero-test examples
before elimination/F4/basis search. The complete acceptance suite remains
required after every implementation change.

## Discharging Boolean-domain branches

The same `unique_solver::search` used by normal uniqueness reasoning can now
record branches under a proved equation `q=x^2-x=0`. A class's Boolean flag is
insufficient: canonicalization must supply a derivation of that exact equation,
including any class aliases and non-unit scaling. Each child records its local
`x=0` or `x=1` hypothesis. If the two child refutations have the identities
`1=A0+B0*x` and `1=A1+B1*(x-1)`, removing their local hypothesis nodes gives
derivations of `A0` and `A1` from the enclosing scope's premises. Then

```
A0 + B0 * (x*A1 + B1*q) = 1.
```

This joins both branches using existing PAC addition/multiplication only. The
final DAG contains original input nodes, not branch assumptions; export rejects
any undischarged placeholder. Nested branches use the same identity recursively.
SAT or inconclusive children cannot close their parent.

The optional attempt is bounded to depth 8, 64 search nodes and at most 10,000
additional proof nodes (also at most half the remaining DAG-node allowance).
Branch discharge composes multiplier actions directly in the proof DAG: for
`1=A+B*h` and a target proof `T=0`, it produces `A=0` and `B*T=0` without
expanding `B`. Only the existing addition/monomial-multiplication rules are
emitted. Temporary traversal arrays are linear in the bounded DAG node count;
the 16 MiB estimated proof-DAG storage cap remains unchanged.
On local failure the attempt restores the root-scope proof prefix and residual
equations. Work and cancellation remain charged to the original allowance.
`:branches false` disables this attempt for ablation. This does not yet cover
arbitrary root sets or the bit-bound/digit rules of other native components.

Validation includes 29 independently checked branch proofs over fields through
521 bits, nested and aliased bits, missing-premise rejection, SAT and budget
controls, and external Alethe/PAC checks. C++ tests also assert that simple branch
fixtures close before native elimination or basis computation.

## Current measured acceptance

A complete paired run now checks **370/390** distinct FMCAD inputs versus
**369/390** with frozen `a2fe1485a`: one gain, no losses. Both configurations use
the integrated native backend, four workers and the same ten-second whole-pipeline
deadline, including original-input replay, standalone FFPacheck and Carcara calling
FFPacheck. The retained configuration produces 371 bundles versus 370. The
geometric-mean time ratio on the 369 common successes is **1.046**: a modest cost
for increased checked coverage, not a general speedup. The newly checked 06v/032t
Zokref determinism case takes 9.13 seconds; three further repetitions check it
in 9.14–9.22 seconds, while the baseline times out in all three. Both configurations
retain all six repeated completions of the two previously borderline successes.

The retained changes release normalized input subterms at last use, schedule the
untrusted producer DAG by dependencies, and inline bounded low-fan-out PAC steps.
PAC uses centered integer coefficients (for example, `-1` instead of `p-1`), with
unchanged modular arithmetic and checking. No arithmetic/checker limit is raised,
no external check is removed, and backend selection remains unchanged. Export
bytes remain implementation-specific; frozen scripts accompany every archived run.

The **20** remaining inputs comprise 15 Circ production deadline misses, three
native construction limits (two polynomial-size limits and one proof-store limit),
one independent-replay storage failure, and one exported bundle exceeding the
checking deadline. Input-normalization cleanup alone did not remove the replay
failures: dependency scheduling gets one through export, but it still exceeds the
whole-pipeline deadline. The other also reaches polynomial expansion limits when
diagnosed beyond its initial storage failure.

600 screening measurements rejected speculative early theory checks (five lost
successes, 36% slower on common successes), larger polynomial limits, proof-node
sharing/pruning and a ring-certified square consequence for coincident zero tests.
The latter three did not improve checked coverage beyond export-only changes.
Direct backward multiplier accumulation also exceeded the unchanged storage bound.
The sampled Circ problems generated 73–362 certified conflicts in nine seconds;
preserving Boolean-to-field range facts symbolically is a stronger next lead than
repeating algebra on complete assignments. Digit injectivity remains unimplemented;
the earlier ablation below did not identify it as the cause of these misses.

All **35** acceptance checks pass, including new shared-input lifetime, dependency
scheduling, signed-coefficient and diagnostic-stream regressions. The separate
`qf-ff-proof-frontier-20260930` archive contains 1,404 completed benchmark
measurements, frozen candidates, proof bundles, exact checker identities and the
rejected prototypes. A 569-row campaign interrupted by disk exhaustion is preserved
but excluded; the paired full run was restarted after content-verified compression.
No cvc5 or Lean rerun was performed, and these changes have not been pushed.

## Previous native integration measurement

The native SAT/theory integration with root restarts checks **369/390** distinct
FMCAD inputs, exactly the same successful inputs as the retained incremental
pipeline with watched replay. Both produce 370 bundles. The geometric-mean
whole-pipeline ratio is **0.994** on their 369 common checked successes: comparable
performance, not a demonstrated general speedup. Each run has one shared
10-second production-and-checking deadline and four workers. The 408 member paths
are deduplicated to 390 inputs. Original-input checking and both external checker
stages are included in the times.

The initial integration learned field clauses at the current decision level. It
checked 367/390, losing two near-deadline inputs relative to the retained best.
In three repetitions of each of those two inputs, that policy timed out 6/6;
root restarts checked 6/6 in 7.92–8.49 seconds. The existing incremental pipeline
with watched replay also checked 6/6, in 8.44–9.71 seconds. The subsequent full
390-input comparison confirmed that root restarts introduce no coverage loss.

An earlier three-way run in this round checked 368 with frozen `ca39e58c5`, 369
with watched replay and 367 with the initial integration. The watched variant
was 1.9% faster by geometric mean on the 367 common checked inputs. That extra
completion was already solved in the previous milestone's best run; it is a
near-deadline improvement, not a newly covered algebraic problem.

Retain watched replay in the existing incremental native mode and the new
integration as `--boolean-backend integrated`. Automatic backend selection is
unchanged. The integration has met coverage parity, but has not unlocked another
hard input. The same **21** remain: 15 production deadline misses, three native
proof-budget failures, two independent-checker storage limits, and one produced
bundle whose external checking exceeds the deadline. Native cancellation may be
reported as `unavailable` before the outer runner reaches ten seconds; the lower
count of outer timeouts is not increased coverage.

All 35 acceptance checks pass for the retained implementation, plus 20 consecutive
timer-cancellation/recovery trials. The final binary was rerun after the
cancellation-handler fix and again checked the same 369/390 inputs. Inputs, frozen
binaries/scripts, source patch, 2,340 full-corpus measurements, 240 screening
measurements, 24 borderline repetitions, checked figures and content-verified
compressed proof bundles are preserved in the separate
`qf-ff-native-integration-20260930` research archive. The comparison does not
rerun cvc5 or establish full reconstruction, theory-combination proof support,
or Lean acceptance.

## Earlier measured acceptance

The latest controlled full-corpus run checks **367/390** inputs versus 366 for
the frozen previous native pipeline, with one gain and no losses. On all 366
common successes the geometric-mean wall-time ratio is **0.939**. All four
configurations ran all inputs with the same ten-second whole-pipeline deadline,
four workers and unchanged independent/Alethe/PAC checkers. This is one timing
run, not a statistical confidence estimate.

The ablation checks 366 with immediate external-process completion notification
(ratio 0.956 versus baseline), and 366 with declaration reuse added (0.930 versus
baseline; 0.972 versus notification alone). Direct branch-multiplier composition
adds the 02v/032t random Zokref determinism case, with a ratio of 1.010 versus
that otherwise identical pipeline. These three improvements are retained.

There are 369 completed bundles; two exceed the checking deadline. The 23
unchecked inputs consist of three native construction-budget failures, three
independent-checker retained-term failures, and 17 timeouts. Full reconstruction
and ordinary SAT/theory callback integration remain unfinished. A proof emitted
by the native command is not counted as a checked bundle when export/checking
fails.

Substitution-term aggregation and indexed RUP replay did not improve a 60-input
screen (all 24 earlier misses plus 36 successes): time ratios were 0.989 and
1.050 respectively, with identical coverage. They were discarded. Canonical
polynomial evidence caching, larger branch bounds, and bounded producer-side
value deduplication did not add checked diagnostic results and were not retained.
Disabling digit-uniqueness inference preserved the ordinary search-node counts
on the sampled determinism misses (5 and 43 nodes). This does not establish that
digit rules are unnecessary in general; it does not justify implementing them
as the next fix for these measured failures.

All 34 acceptance checks pass, with six additional nonlinear Boolean-circuit
regressions, changed-premise rejection, declaration replacement/reset checks,
and external-process completion, output-limit and cleanup checks. Frozen source,
binaries, input identities, all receipts and figures are in the separate
`qf-ff-proof-optimizations-20260930` research archive. No new cvc5 or Lean run was
performed, and the published PR branches have not been changed by this milestone.

Previous milestone:

The preceding native pipeline checked **366/390** FMCAD inputs within the shared
10-second production/checking deadline, with four workers. A controlled
780-run comparison of producer-side DAG balancing against the preceding native
pipeline checks 366 versus 365: one gain, no losses, and a geometric-mean
wall-time ratio of 1.015 on 365 common successes. This is a single-run timing
measurement. Balancing is retained under the coverage/performance criterion.

The producer flattens only single-use arithmetic chains, preserves shared DAG
nodes, and balances addition trees. This reduces retained intermediate terms
without globally expanding polynomial multipliers. It is bounded and untrusted:
both unchanged and transformed certificates must pass the existing independent
input-bound verifier and external Alethe/PAC checks. No checker limit or rule
was changed. Tests include a valid proof exceeding the original retained-term
limit, malformed DAGs, changed premises, and raw/balanced native proofs.

The pipeline produces 368 bundles; two miss the checking deadline. The 24
unchecked inputs comprise seven native field-proof budget failures and 17
timeouts. Full reconstruction remains unfinished. The current success set
contains every success from the earlier 356-result published-PR2 comparison,
but this does not certify all ordinary solver paths or establish Lean checking.

The preceding 1,560-run comparison measured scoped field sessions, larger bounded
native work/lemma allowances and Boolean-branch recording: 365 checked versus
358 for the previous native pipeline, seven gains and no losses, with a time
ratio of 0.842. Disabling only branch recording checked 364; enabling it added
one result with a ratio of 1.010. Balancing recovers the single published-PR2
success lost in that preceding comparison. These are separate controlled runs;
their timing ratios must not be combined into a new measured speedup.

All 34 acceptance checks pass for the native branch/session implementation;
all eight proof acceptance checks pass again after balancing. On POSIX,
`--backend native` uses incremental SAT and scoped field sessions by default.
Explicit `native` Boolean search and `--no-field-session` retain one-shot
alternatives; default `auto` reconstruction is unchanged. Frozen inputs,
binaries, scripts, receipts and figures are retained in the separate
`qf-ff-proof-branches-20260930` and `qf-ff-proof-balancing-20260930` research
archives. No cvc5 comparison was rerun for these milestones.

Earlier measurements:

The subsequent persistent-SAT milestone passes all 34 acceptance checks. Its
full-corpus run checks 358/390 certificates in both one-shot and persistent
native modes, with exactly the same successful inputs. Persistent search is
12.9% faster by geometric mean on those 358 successes. It produces 360 bundles;
two do not finish checking before the shared 10-second deadline. Published PR2
checks 356 in the same run and harness. Against that baseline, persistence has
six gains and four losses, with a wall-time ratio of 1.008 on 352 common checked
inputs. This improves native proof throughput but is not a coverage-preserving
replacement for published PR2. It remains an explicit experimental option.

A diagnostic propagated polynomial multipliers backward through 108 existing
field-lemma proofs from a slow soundness instance. Exact algebraic cancellation
removed no premises. That measured case does not justify adding a multiplier
compression pass as the next performance change. Field-conflict selection and
the unsupported native inference paths remain open work.

For historical comparison (different run, before persistent SAT):

The shared-uniqueness milestone passes all 33 acceptance checks, plus the two
updated external Boolean suites (34 checked bundles each). On the complete
390-distinct-input FMCAD corpus, at a 10-second whole-pipeline limit and four
workers, native recording checks 355 proofs and published PR2 reconstruction
also checks 355: six gains and six losses. Native recording produces 358 bundles,
but three do not finish checking within the deadline. On 349 common checked
inputs, the geometric mean native/published wall-time ratio is 1.112.
Ordinary solving remains 390/390, with a before/after ratio of 0.997.

The earlier 55-case regression screen improved from 14 checked with the previous
native rewrite to 25 with shared uniqueness; the published baseline checks 20.
That selected screen does not establish a full-corpus advantage. A follow-up
ablation also identifies two cases where enabling uniqueness worsens Boolean
proof search. The implementation remains experimental; these results do not
justify replacing the published default. Detailed runs and figures remain in
the separate research archive, not in the solver source tree.

## Release gates

1. Add an independently checked regression for each supported inference and a
   tampered-premise/witness rejection test. Test scope changes, cancellation,
   resource recovery, SAT controls and all storage variants that carry proofs.
2. Audit every native UNSAT return and goal-closing statement. Require evidence
   at the closing boundary, not a later reconstruction attempt.
3. Run the full existing 390-distinct-input FMCAD corpus at the established
   10-second whole-pipeline limit against the frozen PR2 and cvc5 candidates.
   Report solver completion, proof production and checked proof completion
   separately; preserve all misses and checker failures.
4. Measure normal solving with recording disabled and proof-mode overhead.
   Publish replacement PR2 only with accurate scope, reproducible measurements
   and an explicit accounting of any remaining unsupported path.

Research results and transient proof bundles stay in the separate research
archive; only implementation, regressions and maintained documentation belong
in the solver PR.

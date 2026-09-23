# QF_FF performance round 8: root completion and bounded matrix growth

The retained default enables `ff.model_search`. On **1,256 inputs at ten seconds**,
it solves **888 versus 886** for the frozen previous default: two gains, no losses,
and no contradictory answers. Common-solve time increases **0.45%**.

The full comparison with pinned cvc5 main is paused at the user's request.
This round evaluates general Z3 improvements against the frozen round-7 default.
The updated CAV draft includes this paired study while preserving the older
full-corpus comparison as historical. See [paper reproduction](papers/qf_ff/README.md).

## Diagnosis

The corrected historical corpus has 51 cvc5-union-only cases. All 34 Small
cases exhaust an algebra budget before reaching root completion: 18 work,
15 matrix, and one polynomial-size limit. Thus stronger root completion alone
cannot address most current gaps. Direct algebra diagnostics use three seconds;
these are classifications, not a replacement for the ten-second default portfolio.

The cyclic five-variable Example is different: its basis finishes quickly but
needs a univariate consequence to exclude extension-field roots. The existing
optional minimal-polynomial operation solves it. The model-search option also
recovers the Montgomery2Edwards QED2 SAT query through additional witness probes.

## Independent candidates

| Option | General mechanism | Initial 113-input screen |
| --- | --- | --- |
| `ff.model_search` | Existing bounded quotient minimal polynomials and diversified SAT witness slices | 53 solved, two gains, no losses |
| `ff.root_completion` | Exposes minimal-polynomial completion independently of extra witness probes | 52 solved, one gain, no losses |
| `ff.quotient_field` | Reduces Frobenius field axioms in a certified small zero-dimensional quotient, then rebases | 51 solved, no gains or losses |
| Root plus quotient | Both mechanisms | 52 solved, one gain, no losses |
| Frozen baseline | Round-7 retained defaults | 51 solved |

No SAT/UNSAT disagreements occurred. All 23 SAT model runs from the existing-option
screen passed independent evaluation of original assertions. Screen timings are
exploratory: some development work overlapped them. They cannot establish a
performance-equivalence claim. Quotient completion remains opt-in without an
observed coverage benefit.

A further candidate, `ff.adaptive_matrix`, replaces the fixed 1,024 symbolic
reducer cap with a conservative 16 MiB symbolic-storage allowance. It preserves
reducer order and all column, polynomial-size, work and cancellation limits.
The allowance charges coefficients, monomial storage and copies, premise sets,
and row headers; it is not a bound on total solver memory. Matrix elimination
retains its separate storage guard. The old cap is unchanged when disabled.

The clean 113-input screen solves 51 with this option alone, identical to the
baseline. Combined with model search it solves 53, the same two gains already
provided by model search alone. There are no losses or contradictory answers.
The matrix option alone takes 13.518 versus 12.841 seconds summed across the
51 common solves (+5.3%); its geometric ratio on cases taking at least 50 ms
is 1.168. Without a coverage benefit it remains disabled.

## Resource experiments

Explicitly raising the algebra allowance from two to eight million work units
recovers one of the 34 Small gaps, a SAT case. Adaptive scalar recovery and
Gebauer–Möller pair selection with that allowance recover the same case only.
Compact matrices recover none. These are three-second algebra-only diagnostics,
not grounds to raise the default allowance and delay complete fallback globally.

A follow-up at ten seconds pairs the old matrix policy with eight million work
units against adaptive matrix admission with eight and 32 million units. All
three solve the same one of 34 Small gaps; there is no further coverage gain.
These calls use explicit local tactic parameters, preserving the requested
algebra budgets. This rejects the simple combination of a larger symbolic
reducer allowance and a larger work budget as a default improvement.

The first matrix diagnostic mistakenly used a global numeric setting with a
directly invoked tactic, which kept the tactic's local default. That file is
preserved and explicitly superseded by `matrix-diagnostics-v2.json`; v2 uses
local parameters and checks the effective work counters. Only v2 supports the
resource conclusions above.

## Correctness and acceptance

The final experimental binary passes all 16 regression commands, including independent
small-field enumeration, models, conflict cores, all solver interfaces,
incremental lifecycle, and local/global resource limits. A focused F3 example
has extension-field solutions but no base-field solution; the derived conflict
requires both original premises. Matrix-admission tests force more than 1,024
reducers, compare scalar ideal reductions, check premise necessity, and force
storage exhaustion followed by successful reuse.

Broader paired measurement uses the previous 1,126-input cohort plus all ten
Examples (1,136 inputs), and a separately hash-selected 120-input confirmation
cohort outside the previous cohort and development screen. This is selection
independent of outcomes, not an untouched external corpus. Retain a default
only with improved coverage, no unexplained losses, comparable timings,
validated SAT witnesses, and isolated slow-case repetitions.

Evidence: `tests/finite_field/results/performance-round8`. Proof reconstruction
remains v2; dependency sets are conflict explanations, not proof certificates.

## Interrupted measurement and runner repair

The first wider three-configuration run was interrupted after a host disturbance.
Two apparent losses used less than 0.1 seconds of solver CPU before their
10-second wall deadlines. A worker-supervision timeout killed only the worker,
leaving three solver processes orphaned; an exception also stopped journaling
while queued executor tasks continued. That run is preserved under `wide/` with
an interruption record and is excluded from default acceptance.

The runner now owns each worker/solver process group, terminates and reaps it
on outer failures, and records `infrastructure_error` separately from solver
timeouts. Journaling continues after per-case errors; a journal containing such
errors cannot be resumed and silently double-counted. Five focused tests cover
large-input delivery, forced outer timeout with an uncooperative solver,
ordinary solver timeout, worker startup failure, and durable error handling.
All pass. The two apparent losses were repeated three times with one worker:
all 18 baseline/root/model-search runs solve in about 0.03 seconds each.

The clean broad evaluation first tests `model_search`, which covers both screen
gains. Root-only completion remains an alternative if its extra witness probes
regress. The benchmark runner fix does not change solver timeout or RSS limits.

## Retained default and final paired comparison

| Cohort | Inputs | Baseline | Retained policy | Gains | Losses |
| --- | ---: | ---: | ---: | ---: | ---: |
| Previous cohort plus all Examples | 1,136 | 800 | 802 | 2 | 0 |
| Separate hash-selected confirmation | 120 | 86 | 86 | 0 | 0 |
| **Total** | **1,256** | **886** | **888** | **2** | **0** |

All 2,512 runs completed without an infrastructure error. The 886 common solves
sum to 227.992 seconds for baseline and 229.028 seconds for the retained policy,
a 0.45% increase. On common cases taking at least 50 ms in either configuration,
the geometric candidate/baseline ratio is 0.996. The confirmation sample adds no
new gains; it supplies a separate check against coverage regressions.

Three isolated repetitions confirm each gain. The cyclic Example remains a
baseline timeout and becomes UNSAT at a median 0.018 seconds. Montgomery2Edwards
remains a baseline timeout and becomes SAT at 0.026 seconds. MACI Merkle inclusion
is essentially unchanged: 4.681 versus 4.684 seconds.

Two short SAT regressions are real: `r_13_32_8_system14.smt2` goes from 0.036 to
0.125 seconds, and `BitElementMulAny@escalarmulany@circomlib.smt2` from 0.042 to
0.168 seconds. The retained policy therefore does not speed up every case. We
accept these bounded absolute costs for the two coverage gains and comparable
aggregate performance. Latency-sensitive callers may disable `ff.model_search`
and enable `ff.root_completion` alone, retaining the cyclic gain without the
extra witness probes. The apparent `deterministic_bvsgt_19` slowdown disappears
in isolation (0.031 versus 0.031 seconds).

`ff.quotient_field` and `ff.adaptive_matrix` remain disabled: correctness tests
exercise their deductions/admission changes, but the measured corpus supplies
no coverage benefit. Root-only completion remains independently available but
is redundant when model search is enabled. The underlying child-engine default
stays false and `configure_probe` does not propagate diversified model search;
otherwise bounded witness probes could recursively expand their search.

The broad measurements use the frozen experimental binary with explicit global
`ff.model_search=true`. The final source changes its public default to true;
regressions and representative default-interface replays validate that build.
This is a Z3-versus-Z3 improvement study, not a resumed full cvc5 comparison.

## Final-build validation and archived evidence

The retained build passes all 16 regression commands. New tests exercise an
exact F5 minimal-polynomial identity, scalar ideal membership, independently
enumerated premise necessity, guard cancellation, more than 1,024 matrix
reducers, and storage-failure recovery. Policy tests check default/on/off and
local/global settings across ff-solve, ff-sat, native SMT and QF_FF; native SMT
exposes theory-level counters, while tactic interfaces expose probe counts.
All **559 primary SAT model replays** pass independent evaluation of original
assertions. The final default agrees with the flag-enabled experimental binary
on all 27 representative inputs, including all ten Examples and 12 Poseidon
cases; their 30 single-query SAT model replays also validate. A separate
previous-default/final-default Poseidon comparison retains all 12 solves, with
all 16 SAT model replays validated. Multi-query Examples are compared by their
full answer sequences rather than being counted as single-query models.

Three additional matrix diagnostics confirm that extra reducers are actually
admitted (205 and 634 in two recorded cases), but matrix resource exhaustion
still ends the attempts even with a larger work budget. This remains a sparse
matrix storage/scalability limitation, not an additional root-completion win.

Final binary SHA256:
`4c63ed60034006639969127ed7f81deadf46b12c21955c106a61b09370efca8a`.
The evidence directory contains both binary identities, raw paired runs,
separate isolated repetitions, all model validations, test results, complete
queried inputs, source overlays, and the interrupted run with its exclusion
record. No cvc5 full-corpus comparison was resumed and no CoCoA dependency was
introduced.

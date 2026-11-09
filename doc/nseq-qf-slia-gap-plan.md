# QF_SLIA: closing the c3mv/master gap

Investigation date: 2026-11-04. Implementation has started with the P0
model-coherence increment below. Baseline sections describe the original
branch before these changes.

## Expanded evaluation and priorities (2026-11-08)

The primary gap population now comes from
[PR run 1294 versus matching master run 1277](https://z3prover.github.io/coz3/compare_stats.html?a=run-1294-qf-slia-gap-20261107-stats.md&b=run-1277-qf-slia-master-stats.md):
include every run-1294 TIMEOUT for which run-1277 returns SAT or UNSAT
with exit code zero under its configured `-T:5` limit. Do not restrict
master to 0.25 seconds, require a speed ratio, or cap the population.

This selects **6,012 inputs: 5,783 SAT and 229 UNSAT on master**.
Of these, 5,971 have reported master wall time at most five seconds;
41 have definite answers under `-T:5` with wall-time overshoot. Retain
those 41, report them separately, and adjudicate cutoff-sensitive results
serially rather than treating them as reliable timing wins.
If an apparent gain remains near the deadline after serial repetition,
compare completed work in a separate extended-limit diagnostic. Identical
completed resource/search counters without a material repeatable speedup
are a cutoff-only flip, not recovery credit. This diagnostic never changes
the primary five-second limit or clears a loss in the five-second gate.

| Population | Inputs | Evaluation role |
|---|---:|---|
| All timeout/master-definite gaps | 6,012 | Primary objective, no sampling cap |
| Prior acceptance panel | 5,035 | Historical, slow-but-solved, and c3mv-only controls |
| Accepted/repaired controls | 379 | Explicit expected answers: 377 SAT, 2 UNSAT; includes all 17 repairs |
| Union of these populations | 10,446 | Paired candidate acceptance sweep |
| Family/result/time/operator-stratified representatives | 76 | Diagnostic inference profiling only, not a substitute for the full population |

Only 601 of the new primary gaps were in the prior 5,035-input panel.
The expanded acceptance set therefore adds 5,411 previously uncovered
identities. Preserve identities and input hashes; record full-set and
per-family outcomes, introduced losses, all-input timing regressions,
and unmeasured residuals. Do not extrapolate parity from the diagnostic
panel or sum overlapping feature groups as independent gains.

Run 1295 subsequently completed for accepted head `e9728eebe`, with
5,994 timeout/master-definite gaps: 5,964 overlap the requested 1294
population, and 26 are outside the active 10,446-input sweep. Preserve
the current manifest and evaluate those 26 as a disjoint follow-up
before publication; report-to-report cutoff drift is not attributed
incremental solver improvement.

The report branch is `5c87a4a99`, but new local candidates are paired
against the immediately preceding accepted PR head `e9728eebe`.
The matching report-master executable is `9af2dac2e`; current upstream
master is a separate reference, not an interchangeable baseline.
Both report runs use `-T:5 model_validate=true`; local paired runs
also fix the SMT and SAT random seeds to zero.

### Recurring characteristics and implementation order

PyEx accounts for 4,386 gaps, including 4,369 SAT cases. Across the
whole population, 5,928 inputs contain positional operations, 3,777
contain replacements, 1,571 contain decimal conversions, and 644
contain regex membership. These are nonexclusive syntactic features,
not established causal classifications. Prioritize recurring SAT
construction and scheduling gaps over isolated UNSAT rewrites.

The first 76-case diagnostic reproduces the architectural gap: matching
master solves all 11 PyEx representatives (8 SAT, 3 UNSAT), while both
local nseq versions solve only one. On HTTP entry-disposition
`b18c860c...`, master returns SAT in 1.68 seconds with 272 fixed-length
and 37 length-coherence steps. The accepted nseq baseline times out
after 1,673 DFS nodes, below its 2,176-node fixed-length trigger, despite
16 nseq final checks. Master performs more Boolean decisions but uses
4.70 million resource units versus nseq's 20.75 million at timeout.
These counters identify delayed construction and expensive word search
as a concrete next hypothesis; they are not a chronological inference
trace or evidence that globally lowering the threshold is safe.
Substitution and rewriting also validate all 311 original conjuncts
with `value1 = "IJ=x"` and `value2 = "LV"` (both keys are
`"cache-control"`), without invoking a solver. This confirms a small
witness exists; it is not a model claimed to have been returned by master.
The next trace must distinguish scheduling from eligibility: the current
fallback requires relevant selected String terms, an unsigned lower bound
at most 20, and an available untried guarded length. It probes eligibility
before search but does not instantiate on every refuted arrangement.
Record those guard outcomes and repeated arrangement conflicts before
changing scheduling. Earlier global resource-to-fallback policies lost
protected repairs and must not be retried merely because this case is slow.

An independent, solver-free evaluator now verifies the same 311 original
conjuncts, including SMT-LIB substring/index bounds, first replacement,
quoted strings and Unicode code-point semantics. The witness has 18
distinct derived String terms: one empty, eleven length-one and six
length-two terms. Its top-level conjuncts separate the four declared
variables into independent syntactic components; `value1` and `value2`
both have direct positional parents and no conversion operators occur.
This does not establish post-rewriting relevance, dynamic bounds or
runtime eligibility. Across the cached diagnostic, all eight HTTP cases
time out below the trigger without reported nseq fixed-length axioms;
two MongoDB cases time out despite emitting them. Scheduling alone
therefore cannot explain the whole PyEx gap.

Distinguish two inferences before changing that schedule. In report
master `9af2dac2e`, `src\smt\theory_seq.cpp:381-399,535-585` propagates
decompositions for lengths whose arithmetic lower and upper bounds are
already equal, guarded by that equality. Its separate length-coherence
phase (`src\smt\seq_eq_solver.cpp:1051-1080,1122-1151`) makes guarded
empty/tail choices. nseq's current helper instead also enumerates
not-yet-fixed lengths and forces their bound phases, behind the DFS
head start. Trace the availability of exact zero/positive bounds
separately from guessed lengths. A focused next prototype may propagate
already-fixed short lengths without guessing new ones or moving the
existing speculative fallback earlier. Require evidence that such
eligible bounds are present and useful; do not infer this from the
concrete witness. Master's fixed-length statistic counts successful
passes, while nseq's counts emitted axioms, so their numeric magnitudes
are not directly comparable.

1. **Context-preserving positional/replacement simplification.**
   PyEx HTTP examples repeatedly split at `indexof`, replace a character
   in the prefix, and rejoin the suffix, then inspect the derived result.
   Investigate canonicalizing these relations before separate derived
   strings enter word/regex search. Any rule must preserve first-occurrence,
   absent-needle, and out-of-range substring behavior. Measure repeated
   chain depth, derived-term count, arithmetic propagation, and DFS work;
   do not infer a benefit from the presence of `str.replace` alone.
2. **Earlier guarded SAT construction, with component-aware eligibility.**
   nseq's fixed-length fallback is currently gated on whole-goal absence
   of conversions and a cumulative 2,176-node head start. Corresponding
   seq reasoning couples length assignments and character constraints.
   Determine where nseq has enough information but schedules construction
   late, and where the candidate model is genuinely unavailable.
   Test component-local opportunities rather than globally weakening
   purity or shortening the head start: coupled arithmetic, character
   constraints, snapshot invalidation, and scope rollback must remain
   guarded and model-validated. Preserve the previous 17 repairs.
3. **Complete cheap numeric-to-length inference before conversion search.**
   The shared `itos_axiom(s, k)` already relates decimal magnitude to
   output length; seq schedules it through length-limit propagation.
   nseq previously enqueued only the basic itos overload. This increment
   additionally calls `add_itos_axiom(n, 0)`,
   supplying `n < 10 => len(str.from_int(n)) <= 1` and the nonnegative
   nonempty bound without enumerating digits or arbitrary powers of ten.
   Negative integers produce the empty string, so the upper bound does
   not require proving digit validity or nonnegativity.

### Validated decimal-length increment

The expanded one-repeat 10,446-input matrix initially records 193 gains,
14 losses and 62 timing flags. The subsequent 754-input, three-repeat
serial gate includes every discrepancy, all 379 protected inputs,
122 prior quiet controls and 26 disjoint run-1295 holdouts. It retains
all protected answers and all 17 repairs, with no repeated losses,
material slowdowns, contradictory answers or errors. All 26 new
holdouts solve on both versions.

There are **172 repeatable timeout-to-UNSAT recoveries**: 70 CVC4 and
102 Trauc Conbyte cases. Baseline times out in all 516 repetitions;
candidate and matching report-master each return UNSAT in all 516.
Median per-input quiet timings are 5.035 seconds baseline, 0.034 seconds
candidate and 0.103 seconds matching master. Median resource counts
fall from 22,400,673.5 at baseline timeout to 9,824 at candidate
completion, versus master's 109,880.5. Candidate has no reported word
DFS on 139 of the recovered inputs. These are cohort measurements,
not a claim about all PyEx or the complete corpus.

The 21 raw SAT gains disappear under serial repetition. One formerly
lost PyEx input becomes an apparent serial SAT gain, but an extended
diagnostic confirms identical completed work and no material speedup;
it earns no recovery credit. The adjudicated hybrid panel contains
10,472 inputs, with 754 repeated overrides/holdouts and single-repeat
data elsewhere: 4,629 baseline and 4,802 candidate definite answers,
zero losses and zero material slowdowns. Its observed delta of 173
includes that uncredited cutoff flip; conservative credit is 172 UNSAT.

Within the 6,012 primary gaps, candidate solves 423, leaving 5,589
measured unresolved cases: 5,535 published-master SAT and 54 UNSAT.
The 41 master wall-time-overshoot cases remain separate; both versions
solve two and leave 39 unresolved. The 4,386 PyEx subset still has
4,168 candidate-unresolved cases, and its sole observed improvement is
the uncredited cutoff flip. The SAT objective therefore remains open.
There are 73,939 report identities outside the 10,472-input panel;
no extrapolation is made to them or to current tip master.

Focused modules, all 136 native modules, four conversion proof-generation
smokes, nine boundary/negative model checks, scoped guard rollback,
and basic CLI/Python checks pass. Proof generation is not external
proof certification. Preserve all 172 new UNSAT controls alongside
the previous 379 mixed-answer controls before the next prototype.

## Implementation progress

The first P0 increment is implemented; P0 is not yet closed.

- Export the SAT leaf's normalized lengths for all relevant sequence theory
  variables, not just uninterpreted stoi arguments. These remain candidate
  assumptions, not unconditional theory axioms.
- Normalize length queries when constructing fresh sequence values. Without
  normalization, the arithmetic-only backend can assign independent values
  to interpreted length expressions such as concatenations.
- Consult captured arithmetic-model function graphs bottom-up before
  evaluating numeric queries. Rewriting a substring of an abstract string
  model value into `str.at` can otherwise lose its function interpretation,
  returning either no length or an incorrect length. The broader sweep
  exposed eight additional Leetcode failures with this cause.
- Internalize stoi argument lengths and yield immediately after generating
  conversion-coherence axioms, before searching with the old assignment.

Release validation used the same five-second cap and `model_validate=true`
as the original investigation:

| Test set | Before | After |
|---|---|---|
| 290 published invalid-model inputs | 290 invalid models | 274 validated SAT, 1 UNSAT, 14 timeouts, 1 unknown; no invalid models |
| 37 diagnostic inputs | 3 solved, 6 invalid models, 17 timeouts, 11 unknowns | 9 solved, no invalid models, 12 timeouts, 16 unknowns |
| Three c3mv win controls | SAT, UNSAT, SAT | Unchanged; 0.027-0.040 seconds locally |

Five of the six sampled invalid models become validated SAT; the remaining
StringFuzz conversion case becomes unknown. One sampled addStrings timeout
also becomes UNSAT. The additional UNSAT in the 290-input sweep is Conbyte
`py-conbyte_z3seq/leetcode_int-validWordAbbreviation/37.smt2`; published
master timed out, and a local `seq` cross-check also timed out at 30 seconds,
so that result is not independently confirmed.

Added four focused integration cases in `src/test/seq_eq_facet.cpp`, checking
the actual assertions against the returned model: shared regex/arithmetic
lengths with conflicting scoped assignments and pop, substring predicates,
nested indexof/substring suffixes, and conversion-model coherence. The
conversion test permits unknown but rejects invalid SAT or UNSAT. Negative
controls reproduce invalid-model failures when length reconciliation is
removed or model queries are rewritten before consulting function graphs.

The final CMake/Ninja build passes; `test-z3 /a` passes all 116 tests.
CLI solving/help and Python bindings rebuilt against the current library
also pass smoke tests. Benchmark statistics and complete per-input results
are recorded in the session artifacts and benchmark database.

Remaining P0 work includes recovering the timeout/unknown cases and auditing
snapshot invalidation beyond the covered scope transitions. The broader
negative-containment and symbolic-head
work below remains open.

### P1a: empty-side disequations

Implemented nonempty-length propagation after disequation simplification.
When cancellation or a broadcast substitution leaves exactly one empty
side, `deq_propagation` asserts that the remaining token-length sum is
positive and discharges the disequation. Both the arithmetic constraint
and removal are trailed; the length constraint retains the disequation's
dependency, including any substitution dependencies.

The original Noetzli `str-pred-small-rw_99.smt2` now returns UNSAT within
the five-second budget, with three final checks and three DFS nodes,
instead of unknown. Regressions cover both orientations, direct emptiness,
prefix cancellation, substitution-created emptiness, zero and positive
lengths, conflict dependencies, and scope rollback. The regressions fail
before the change; the native suite passes all 116 tests afterward.
The 37-input diagnostic rerun has exactly one outcome change from P0:
Noetzli 99 becomes UNSAT in 0.029 seconds. The other 36 outcomes, including
all three winning controls, are preserved; no invalid models or errors
occur. Rebuilt CLI and Python smoke tests also pass.

### P1b: early short-string conversion bounds

Implemented static upper bounds in the shared regex-based stoi axioms,
using the existing maximum-length query. Statically empty arguments have
conversion value -1; arguments of maximum length one have conversion
value at most 9. The existing lower bound of -1 is preserved. These
unconditional facts do not require a concrete model length. Longer or
statically unbounded arguments retain the existing coherence procedure;
this change does not eagerly generate arbitrary powers of ten.

| Target | After P1a | After P1b |
|---|---|---|
| Trau addStrings/69 | UNSAT, 0.549 seconds | UNSAT, 0.031 seconds |
| CVC4 addStrings/440 | Five-second timeout | UNSAT, 0.029 seconds |

Both targets now finish with zero final checks and zero DFS nodes.
Case 440's reported memory drops from about 1,238 MB at timeout to 18 MB.
Three separately logged runs take 29-33 ms. The full 37-input diagnostic
matrix has 7 SAT, 4 UNSAT, 11 timeouts, and 15 unknowns: case 440 is the
only outcome change from P1a. All three winning controls are preserved
at 0.028-0.041 seconds; no invalid models or errors occur. The seven
conversion inputs also retain their original definite results under
the explicit `seq` engine.

New regressions reject impossible conversions of `str.at` and zero/one-
length substrings with search disabled by `max_conflicts=0`. The test
fails without the static bound. SAT regressions validate models for
non-digit and out-of-range conversions returning -1, digit 9, a two-digit
conversion returning 42, and a leading-zero conversion. All 116 native
tests and rebuilt CLI/Python smoke tests pass.

The sampled add_binary and restoreIpAddresses cases remain timeout or
unknown under nseq; wider character/conversion consistency is still open.
The scheduling yield requested alongside P1b was already implemented
in P0. Persistent regex-bound work is recorded below.

### P1c: persistent bounds before regex witnesses

Membership bound propagation now runs before membership witness search.
Previously, a failed exact-length guess could report a conditional
conflict before the persistent bound plugin ever ran. Denghang 53910
therefore excluded individual lengths instead of using its proven lower
bound to refute the joint regex language.

Reduced ChunkSplit 12 separately. Its empty-side disequality already
implied positive length in the local arithmetic facet, but the outer
arithmetic solver only knew nonnegativity. Forwarding that weaker outer
interval still allowed repeated unsuccessful guesses. Empty-side
disequality notification now also installs the dependency-tracked local
membership `x in re.+(re.allchar)` for strings. This excludes empty
witnesses without adding outer arithmetic decisions. Other sequence
sorts retain the existing arithmetic handling; the current nseq regex
backend does not support nested sequence alphabets.

| Target | After P1b | After P1c |
|---|---|---|
| Denghang instance53910 | Five-second timeout | UNSAT, 0.035 seconds |
| Norn ChunkSplit 12 | Five-second timeout | UNSAT, 0.027 seconds |

Both original inputs now require one final check and one DFS node.
Three separately logged runs take 30-43 ms for Denghang and 28-34 ms
for ChunkSplit. The 37-input diagnostic matrix has 7 SAT, 6 UNSAT,
9 timeouts, and 15 unknowns: these two recoveries are the only outcome
changes from P1b. All three winning controls remain solved in
0.026-0.037 seconds, with no invalid models or errors.

The broader 290-input former-invalid-model sweep has 274 validated SAT,
15 timeouts, and 1 unknown; zero invalid models or errors. The additional
timeout versus the recorded P0 sweep is validWordAbbreviation/37, whose
earlier UNSAT remains independently unconfirmed. The saved pre-P1c
P1b executable also times out on this input at five seconds, so this
outcome change predates P1c.

Three focused regressions cover lower and upper regex length bounds,
and the reduced ChunkSplit case with its weak outer bound. Each checks
UNSAT within a generous deterministic resource budget, then pops the
conflicting constraint and validates the SAT model. Negative controls
isolate both fixes: the lower-bound case exhausts its budget without
the ordering change; ChunkSplit still exhausts it with only that change.
A separate assumption/core check confirms the nonempty assumption is
necessary and that dropping it restores a valid empty-string model.
All 116 native tests and rebuilt CLI/Python smoke tests pass.

This increment does not change the existing one-shot bound cache or
close P0's broader snapshot audit.

### Broader regression repair and P2

A 786-input, five-second comparison against the original c3mv executable
exposed four regressions from the initial outer nonempty clause, and six
reproducible regressions predating P1b. Replacing the outer clause with
local string membership recovers the four P1c regressions. Deferring
membership witnesses until equations and disequations settle, and
avoiding eager conversion unfolding before cheap word refutations,
recovers three more older regressions.

Conversion refinement retains early handling for fixed values of short
arguments, including leading-zero and two-digit conversions. Otherwise
a finite word-search batch precedes numeric refinement; SAT leaves are
still checked for conversion coherence. Invalid conversions need no
positional expansion because the basic digit-language axiom already
characterizes value -1.

P2 now converts unresolved constant-character needles into local
complement-of-contains regex memberships once word equations settle.
Cheap matching and refutation run first, and symbolic needles retain
their conservative handling. Substitution dependencies and scope
rollback are preserved. Tests cover joint witnesses, occurrences across
token boundaries, dependency cores, needle substitutions, and pop.

The diagnostic set improves from 13 to 21 validated solves while
retaining the seven recovered regressions. Three older IP-parsing
regressions and one borderline case remain open at five seconds.
The larger subset is diagnostic evidence, not a claim that the full
QF_SLIA gap is closed.

### Validation after integration with c3mv

Integrated the independent membership-witness deferral and root-witness
cache updates, together with c3mv's newer master merge. The nested-sequence
assumption regression explicitly selects `seq`: its strict SAT/UNSAT
checks do not require unsupported nested alphabets in nseq's regex backend.
The combined Release build passes all 135 native tests and CLI/Python
smoke checks.

The fixed, overlapping 786-input subset uses 32 workers, a five-second
cap, and `model_validate=true`:

| Group | Inputs | Original c3mv | Before regression repair | Integrated state |
|---|---:|---:|---:|---:|
| Proportional corpus sample | 512 | 377 | 378 | 395 |
| Family-balanced master-only cases | 128 | 0 | 37 | 46 |
| Family-balanced c3mv win controls | 64 | 61 | 52 | 60 |
| Family-balanced former model errors | 64 | 0 | 47 | 46 |
| Existing diagnostics | 37 | 3 | 13 | 21 |
| Distinct inputs, all groups | 786 | 441 | 511 | 553 |

The integrated run takes 37.6 seconds and reports no invalid models.
It includes independent c3mv improvements, so the complete gain must not
be attributed to this PR alone.

The complete 290-input former-error sweep reports 271 validated SAT,
2 UNSAT, 16 timeouts, and 1 unknown; no invalid models or errors.
Both UNSAT cases, validWordAbbreviation/37 and /163, were master
timeouts. Independent `seq` checks also time out at 30 seconds, so
these UNSAT results remain independently unconfirmed.

### P3: regular literal exclusions and retry termination

Implemented on top of merged c3mv `bb451f2e0`. Once word equations settle,
membership propagation converts `x != literal` into a dependency-tracked
complement-of-singleton membership, provided `x` is a single String token
already governed by regular memberships. Both removal of the disequation
and installation of its replacement are trailed. This lets the joint
language solver choose a witness before disequation splitting introduces
unsupported symbolic-character heads.

An initial eager translation at disequality notification recovered 18
cases but regressed 11 Kaluza/PyEx cases. It was replaced by the guarded,
post-substitution policy above; all 11 regressions recover. Compound
strings, symbolic excluded values, and other sequence sorts retain their
existing disequation handling.

`mem_monadic_split` no longer advertises higher-cost offers after giving
up: its supported syntax and fixed budget do not change with cost.
Gave-up results remain unknown, not conflicts; successful iterators and
other plugins' higher-cost offers retain their existing behavior.

StringFuzz `regex-020-graft-graft.smt2` now returns validated SAT with
witness `"aaa"`. Five repeated runs take 29-50 ms, median 30 ms, versus
the saved baseline's three unknown runs at 182-381 ms, median 186 ms.
DFS nodes fall from 114 to 1, final checks from 2 to 1, and monadic split
attempts from 10,068 to zero.

All comparisons retain the five-second cap, 32 workers, and model
validation. Groups overlap:

| Group | Inputs | Merged c3mv solved | After P3 solved |
|---|---:|---:|---:|
| Existing quick subset | 786 | 553 | 569 |
| Transformed StringFuzz within that subset | 73 | 49 | 62 |
| Fresh transformed StringFuzz master-only sample | 128 | 16 | 75 |
| All published transformed StringFuzz c3mv wins | 146 | 146 | 146 |
| Generated-regex/regex-length/arithmetic controls | 3 | 3 | 3 |

The quick subset gains 16 solves with no losses in 36.2 seconds.
The additional 277-input StringFuzz/control comparison gains 59 solves
with no losses; baseline and modified runs take 6.8 and 5.7 seconds.
Its fresh loss sample excludes the quick subset and uses fixed seed
20261104. Across 1,281 distinct measured inputs there are no invalid
models, solver errors, or definite-result contradictions against the
baseline or published master where a definite comparison is available.
The 290-input former-error sweep retains 271 validated SAT, 2 UNSAT,
16 timeouts, and 1 unknown; the two previously unconfirmed UNSAT results
remain subject to the limitation noted above.

Focused regressions cover literal exclusions in both orientations and
assertion orders, guarded conflict cores, push/pop and validated models,
compound-string fallback, and a single failed split attempt for an
unsupported symbolic head. All 135 native tests and rebuilt CLI/Python
smoke checks pass. Per-input results, statistics, and the extra manifest
are retained in `p3-quick-v2`, `p3-errors-v2`, `p3-stringfuzz-baseline`,
`p3-stringfuzz-final`, and `p3-subset-manifest.json` session artifacts.

General symbolic-prefix derivative support is not implemented: unsupported
residual memberships still conservatively yield unknown. At P3 publication,
broader P2 PyEx sweeps, the P0 snapshot audit, three older IP-parsing
regressions, and P4's full-corpus comparison remained open.

### P4: full-corpus evaluation and routing review

The corpus evaluation and routing review are complete; the coverage and
win-retention acceptance criteria are **not met**. No solver code or
default routing was changed during this evaluation.

The candidate is P3 commit `757648a43539c833cdf60b2390ce0392624edf3d`
(default `nseq`). The reference is the original comparison report's master,
`9af2dac2eed3ff805f228ef481e2105b53767b19` (default `seq`), not today's
latest master. Both were built with MSVC 14.51.36231, CMake/Ninja Release,
and `/O2 /Ob2 /DNDEBUG`, then frozen with recorded executable SHA-256 hashes.

All 84,411 input paths match both reports. Input hashes were recorded and
checked, and original bytes were supplied on stdin without Windows text-mode
newline translation. Both variants used `-in -st -T:5 model_validate=true`.
The 168,822 invocations were deterministically interleaved with seed
20261105 across **32 total workers**, not 32 workers per variant.
The primary sweep took 5,817.5 seconds (96 minutes 58 seconds); no external
20-second watchdog fired. This is a matched local comparison, not a
direct speedup comparison with the published runner or a full-corpus
ablation of P3 alone.

| Result | Current c3mv/P3 | Report master |
|---|---:|---:|
| SAT | 29,681 | 43,241 |
| UNSAT | 32,402 | 32,159 |
| Solved | **62,083** | **75,400** |
| Timeout | 20,803 | 8,832 |
| Unknown | 1,525 | 179 |
| Errors / invalid models | 0 | 0 |
| PAR-2 mean seconds | 2.745 | 1.331 |
| Maximum reported memory, MB | 794.55 | 1,171.11 |

PAR-2 uses measured per-process wall time for solved cases and ten seconds
for every unsolved case. There are zero definite-result contradictions
against either the local reference or the published master where definite
answers are available. The former 290 invalid-model inputs now give
270 validated SAT, 2 UNSAT, 17 timeouts, and 1 unknown. Model validation
does not independently certify UNSAT; the two validWordAbbreviation
results retain the earlier independent-confirmation limitation.

There are 60,252 common solves, **1,831 current-only** solves, and
**15,148 master-only** solves: a net deficit of **13,317**.
The measured union is 77,231, with 7,180 unsolved by both. Neither the
matched master's 75,400 nor the published target of 76,514 is reached.

#### Retention and attribution

The candidate retains **1,467 of the 1,529 original c3mv-only wins
(95.9%)**. All 62 lost controls time out in the primary sweep.
Each was rerun twice with the original local c3mv binary, the saved
pre-P3 merged baseline, and the P3 candidate, with model validation:

- 37 solve in both original-binary repeats but time out in both pre-P3
  and P3 repeats: repeatable losses already present before P3.
- 16 are not solved by the local original binary in either repeat, so
  the published/local difference does not establish a source regression.
- 8 are mixed or recovered results at the cutoff.
- `20230403-webapp\str-rep\str_replace52.smt2` solves in the two pre-P3
  repeats at 5.04-5.12 seconds of wall time but times out in the two P3
  repeats at 5.06-5.09 seconds.

The last case and `str_replace193.smt2` were additionally checked three
times per baseline/candidate with an eight-second cap. All 12 runs solve
in 3.0-3.3 seconds under the lower contention of these 12 jobs, with
identical per-input resource counts, 6,120 DFS nodes, and 16 final checks.
These checks do not establish a stable P3 search regression, and do not
restore the 62 lost primary controls or clear the 37 inherited regressions.
Keep all 62 in the acceptance set rather than dismissing them as noise.

#### Remaining workload

| Family | Master-only solves |
|---|---:|
| PyEx | 12,932 |
| CVC4 Conbyte | 825 |
| Trau Conbyte | 546 |
| Transformed StringFuzz | 364 |
| Z3seq Conbyte | 247 |
| Z3str Conbyte | 97 |
| Noetzli str-term | 36 |
| Other families | 101 |

PyEx alone accounts for 85.4% of the remaining master-only solves:
the candidate solves 7,771/23,845 versus master's 20,424. Within PyEx,
`httplib2-entry-disposition` contributes 12,042 master-only cases,
`pymongo-mongoclient` 476, and `httplib2-normalize-headers` 325.

Lexical operator-presence bins identify where to investigate, not proven
causes or production routing predicates. The largest exact bin combines
containment, selectors, and replacement: 12,734 inputs, 1,038 candidate
solves versus 10,136 master solves, with 9,143 master-only and 45
current-only results. The containment-plus-selectors bin adds 3,909
master-only results. Replacement alone has not been established as the
cause. Conversely, pure-regex inputs contribute 820 current-only solves,
and word/length-only inputs contribute 288, with no master-only losses
in the latter bin.

A separate replay requested `:reason-unknown` for all 1,704 primary
unknown outcomes, inserting the query before exit. It reproduced 1,524
candidate unknowns reporting incomplete `theory nseq` and all 179
reference unknowns reporting incomplete `theory seq`; one candidate
replay timed out. These generic reasons do not identify a particular
unsupported facet. Diagnostic replays do not replace primary outcomes.

#### Routing decision

A 288-input pilot compared default `nseq` with explicit
`smt.string_solver=seq` on the **same frozen candidate executable**.
It used the same five-second cap and model validation, and reported
zero errors or definite-result contradictions:

| Sample | Inputs | Default nseq solved | Explicit seq solved |
|---|---:|---:|---:|
| PyEx master-only cases | 128 | 0 | 128 |
| Non-PyEx conversion master-only cases | 64 | 0 | 64 |
| Original c3mv-only controls | 64 | 61 | 0 |
| Pure-regex c3mv-only controls | 32 | 32 | 0 |

All 96 explicit-seq failures are timeouts. Its statistics show the seq
backend, not nseq final checks. Explicit seq is therefore a demonstrated
workaround for these sampled gaps, but a blanket switch discards the
sampled c3mv advantages.

Offline proxies using the separate reference executable reinforce that
tradeoff: routing selectors/conversions to the reference projects 76,412
solves but retains only 1,020 original wins. A one-second nseq-first,
reference-remainder portfolio projects 76,852 solves and 1,395 original
wins. These are **not measured routing or portfolio implementations**:
independent full-run timings do not establish a five-second combined
budget including restarts and parsing. Do not change defaults based on
these projections.

Next, resume bounded P2 work on representative entry-disposition failures,
tracing shared selector/replacement witnesses and their outer coherence
constraints. Use the 37 repeatable older losses and all original wins as
gating controls, preserving the model-coherence invariant. Any fallback
proposal needs a separately measured same-candidate, fixed-budget pilot
before a routing decision; it is not a substitute for the underlying fixes.

The session's `p4` artifacts retain `manifest.json`, frozen binaries,
`p4-full-v1-summary.json`, compressed per-file results, and `analysis.json`.
Every primary run is also in `z3agent.db`, with input hashes, statistics,
and compressed stdout/stderr. The retention, longer-cutoff, routing, and
unknown-reason experiments have separate manifests and results; none
overwrites the primary measurements.

### P2 follow-up: deferred character avoidance

The next bounded repair targets constructive negative containment in the
shared selector/replacement decompositions, without changing defaults,
length reconciliation, numeric-conversion scheduling, or search budgets.

An obligation can be scanned while word equations are pending and left
behind `ncontains_facet`'s cursor. If those equations later settle without
substituting into that obligation, the constructive regex conversion is
never revisited. Literal obligations are now rescheduled once the equations
are settled and cheap model completion has been attempted.

For a one-character needle, negative containment distributes exactly over
the haystack's concatenation: each sequence token excludes that character,
and each symbolic unit contributes a character disequality. The sequence
constraints retain the original dependency; character constraints are also
exported as assumptions so the outer model agrees. This avoids giving the
joint regex solver unsupported symbolic-character heads. Multi-character
needles retain the whole-haystack constraint, preserving matches across
token boundaries; symbolic needles retain their existing handling.

An initial unconditional rescan gained 211 solves on a 3,226-input paired
comparison but introduced 11 stable MongoDB/wordPattern losses. Changing
only the regex representation did not repair them. The guarded scheduling
policy keeps the cheap model-completion attempt ahead of rescanning and
restores all 11 losses. The results below measure that guarded policy,
not the rejected prototype.

Focused regressions cover deferred rescheduling without a substitution,
preserving the initial model-completion opportunity, dependency tracking,
scope restoration, and ASCII/non-BMP character exclusions. The existing
multi-character cross-boundary conflict remains a required control.
The earlier P4 table describes its frozen P3 candidate, not an extrapolated
full-corpus score for this follow-up.

The pre-integration paired comparison uses the frozen P3 executable and the patched
Release executable, recorded binary/source-patch hashes, original input
bytes, `-T:5 model_validate=true`, and 32 total workers. Groups overlap:

| Group | Inputs | Before solved | After solved |
|---|---:|---:|---:|
| Fresh entry-disposition master-only sample | 512 | 0 | 134 |
| Other PyEx master-only sample | 128 | 0 | 8 |
| Existing quick subset | 786 | 568 | 601 |
| P3 StringFuzz/control subset | 277 | 224 | 224 |
| All original c3mv-only controls | 1,529 | 1,466 | 1,470 |
| All former model errors | 290 | 272 | 272 |
| Distinct inputs, all groups | **3,226** | **2,261** | **2,439** |

The 6,452 invocations take 300.6 seconds and give **178 gains, zero losses**,
zero errors/invalid models, zero external watchdogs, and zero definite-result
contradictions against the paired baseline, local report-master executable,
or published master where definite. Subset PAR-2 mean falls from 3.158 to
2.674 seconds. Former-error outcomes remain 270 validated SAT, 2 UNSAT,
17 timeouts, and 1 unknown, with the earlier UNSAT-confirmation limitation.

The representative `d369e85...` entry-disposition case changes from unknown
at 936 ms / 661 DFS nodes to validated SAT at 161 ms / 36 nodes, with six
final checks in both cases. This repair addresses missed constructive
propagation, not just a timeout boundary.

Three of the 37 repeatable inherited losses, all MongoDB controls
(`29fe624...`, `caa9e0c...`, `cf2ac74...`), recover. Two additional paired
15-input checks reproduce all three recoveries at 1.77-1.81 seconds while
the baseline times out, and retain all 11 repaired prototype-loss controls.
The fourth original-win gain, ReDOS `28_attack.smt2`, is cutoff-sensitive:
the baseline also solves it in those lower-contention checks. Do not treat
that one result as a stable algorithmic recovery.

All 135 native modules pass, including the new scoped regressions.
CLI arithmetic/help checks and Python arithmetic, selector/replacement
model evaluation, and push/pop checks pass. The session's `p2-followup`
artifacts retain `p2-witness-v2` manifests/results/summary, exact source
patch and executable, native-test output, rejected probes, and repeated
retention checks; all paired invocations are logged to `z3agent.db`.

Before publication, the patch was integrated onto merged `c3mv` commit
`6cce6af3a59fd45a752d5f369f7c6b5959a5a1af`, including its independent
normalized-ground-prefix regex retry. Clean-base and patched Release
executables were rebuilt, frozen, and compared on the same 3,226 inputs
with the same five-second caps, model validation, and 32 total workers.
This comparison isolates the follow-up from the independent base changes:

| Group | Inputs | Current c3mv solved | Patched solved |
|---|---:|---:|---:|
| Entry-disposition sample | 512 | 0 | 134 |
| Other PyEx sample | 128 | 0 | 8 |
| Original c3mv-only controls | 1,529 | 1,467 | 1,469 |
| Former model errors | 290 | 272 | 272 |
| Distinct inputs, all groups | **3,226** | **2,262** | **2,438** |

The 6,452 invocations take 300.1 seconds: **177 gains and one loss**
(net +176), with zero errors/invalid models, external watchdogs, or
definite-result contradictions against the paired baseline, local
report-master, or published master. PAR-2 mean falls from 3.155 to
2.672 seconds. All 142 sampled PyEx recoveries remain.

The sole observed loss is the already cutoff-sensitive `str_replace52.smt2`.
Three additional paired eight-second rechecks, without benchmark contention,
all return model-validated SAT in 2.85-2.89 seconds. Both binaries use
6,120 DFS nodes and 16 final checks; no repeatable search regression is
established. The loss is retained in the primary five-second results.
All 135 native modules and CLI/Python smoke checks pass again on the
integrated tree. The `p2-publication-v1` artifacts record this comparison
and its reference audit; `p2-publication-cutoff-v2` records the rechecks.

The remaining 378/512 sampled entry-disposition failures are 376 timeouts
and 2 unknowns. Continue tracing those shared decompositions and candidate
feedback paths; the full PyEx gap, remaining inherited regressions, and
overall coverage target are not claimed solved by this bounded follow-up.

### Additional PyEx gains: bounded model-length witnesses

The next follow-up compares against the published repair in commit
`f221583e7ee6be9bad86b9077059c7550b9ac68a`, not against the older P3 baseline.
Two remaining failure mechanisms are addressed:

- When cheap model completion cannot construct any candidate, settled
  literal negative-containment obligations can remain behind their cursor.
  An explicit, trailed fallback now records that the attempt finished and
  allows constructive propagation to resume.
- Regex witness construction can eagerly adopt an incidental arithmetic-model
  length of hundreds of thousands of characters. For a model length above
  256, a speculative branch first bounds active membership variables to
  length at most 16. These are dependency-tracked assumptions, not facts.
  The original exact-length path remains the unchanged alternative.

The length-choice phase is trailed and cloned with the membership facet.
A pending choice is not considered a completed membership model. Focused
tests cover successful and rejected short guesses, a required 257-character
witness through the fallback, scope restoration, and empty completion
attempts. Solver budgets and routing remain unchanged.

A matched five-second, model-validated comparison uses 32 total workers and
3,738 distinct inputs, including 512 fresh PyEx holdouts excluded from the
earlier control subset. Groups overlap:

| Group | Inputs | Published repair solved | New repair solved |
|---|---:|---:|---:|
| Existing entry-disposition sample | 512 | 134 | 139 |
| Existing other-PyEx sample | 128 | 8 | 19 |
| Fresh entry-disposition holdout | 384 | 97 | 104 |
| Fresh other-PyEx holdout | 128 | 21 | 28 |
| All original c3mv-only controls | 1,529 | 1,470 | 1,470 |
| All former model errors | 290 | 272 | 272 |
| Distinct inputs, all groups | **3,738** | **2,557** | **2,590** |

The 7,476 invocations take 411.0 seconds: **33 gains, zero losses**, including
**30 PyEx gains** (12 entry-disposition, 18 MongoClient) and 14 gains on the
fresh holdouts. The other gains are two wordPattern cases and one
StringFuzz `str-term-small-rw` case. PAR-2 mean improves from 3.388 to
3.304 seconds. There are no errors/invalid models, external watchdogs, or
definite-answer contradictions against the paired baseline or either master
reference. Former-error outcomes, including the two independently unconfirmed
UNSAT results, remain unchanged.

Two further paired checks cover all 33 gains and the 11 sensitive prototype
controls. Every new candidate remains model-validated SAT, with zero losses.
The baseline recovers one different near-cutoff case in each check:
wordPattern `00b9b0d...` and MongoClient `a1d2f3f...`. Thus 31 gains,
including 29 PyEx gains, reproduce as wins in both checks; the primary
33-gain result is not relabeled.

The representative `2ba00d...` case previously asks for a 432,310-character
witness. In the matched run it changes from timeout at 5.12 seconds and
253 MB peak memory to validated SAT at 0.168 seconds and 21 MB. Three
additional quiet timing runs take 82-88 ms.

All 135 native modules pass. CLI arithmetic/help, Python selector/replacement
model evaluation, and Python's actual required-257-character fallback and
push/pop checks pass. Session artifacts retain `pyex-bounded-final-v1`,
the two `pyex-retention-repeat` experiments, the rejected probes, and their
source/binary/input hashes; invocations are logged to `z3agent.db`.
No full post-fix PyEx or QF_SLIA score is extrapolated from these samples.

### Additional PyEx gains: proved length-one alignment

This follow-up compares against the exact tree merged through #11560,
commit `b19247165ea8aeb6fd76fc05b4c4b9b042c74bd8`. Before Nielsen branching,
it can align an ordinary string variable with a literal or symbolic unit
at either end of a word equation. An arithmetic model only selects the
query: `solver_facet::implies` must prove equal lengths, and the substitution
joins the length proof's dependencies with the word equation's dependencies.
Solver routing and budgets are unchanged.

The shortcut is restricted to word-normalized equations: ordinary variables,
units, internal Skolems, and powers. Compound heads and equations containing
raw interpreted-selector tokens retain their original Nielsen treatment.
The regression traces cut immediately before raw `str.substr` tails, unlike
fast gains using normalized `seq.post` fragments. Preserving the original
search on these interpreted-selector equations repairs the observed losses.
This is deliberately narrower than arbitrary equal-length fragment alignment.

Focused tests cover literal/symbolic units, suffix alignment, proof-core
dependencies, push/pop restoration, both structural guards, and a model
whose matching lengths are not proved. All 135 native modules pass in
24.0 seconds. CLI and Python checks cover arithmetic, literal/symbolic
alignment in both directions, unequal lengths, push/pop, replacement-prefix
symmetry, selectors, and the required 257-character witness fallback.

The matched comparison uses original inputs, five-second caps, model
validation, and 32 interleaved workers. It includes every earlier alignment
input and 512 new PyEx holdouts disjoint from the preceding 4,762-case
experiment. Groups overlap:

| Group | Inputs | Merged c3mv solved | New repair solved |
|---|---:|---:|---:|
| Existing entry-disposition sample | 512 | 139 | 163 |
| Existing other-PyEx sample | 128 | 19 | 31 |
| All original c3mv-only controls | 1,529 | 1,470 | 1,471 |
| All former model errors | 290 | 272 | 272 |
| New entry-disposition holdout | 384 | 107 | 123 |
| New other-PyEx holdout | 128 | 32 | 40 |
| Distinct inputs, all groups | **5,274** | **3,006** | **3,141** |

The 10,548 invocations take 790.3 seconds: **138 gains and 3 losses**, a
net gain of 135 solved inputs. There are 137 PyEx gains and one
`redos_attack_detection` gain; gain answers are 135 SAT and 3 UNSAT.
The untouched holdouts contribute **24 gains and zero losses**.
PAR-2 mean improves from 4.554 to 4.415 seconds. There are no errors/invalid
models, external watchdogs, or definite-answer contradictions against the
paired baseline, published master, or 3,642 definite local report-master
references. Each new UNSAT gain also matches a definite report-master UNSAT.

Two further paired checks cover all gains/losses, all 18 losses of the
preceding candidate, all 33 previous bounded-witness gains, and 11 sensitive
controls: 203 distinct inputs per check. They reproduce 134 and 125 gains,
with **120 primary PyEx gains remaining gains in both checks**. Every one
of the **17 previously repeatable PyEx regressions is SAT in the primary
comparison and both repeats**; all 33 earlier gains remain solved throughout.
For example, `178055f7...`, formerly a five-second timeout under the rejected
candidate, is now SAT in 1.139-1.150 seconds in three quiet checks, versus
1.127-1.136 seconds for the merged baseline.

The three primary losses (`e75e2388...`, `f0d6f054...`, and
`str_replace52.smt2`) disappear as losses in both repeats. Repeat 1 has one
different cutoff loss, `str_replace193.smt2`; repeat 2 has zero losses.
Three quiet runs of each of these four cases are SAT for both binaries:
candidate medians are 2.662, 2.761, 2.899, and 2.950 seconds respectively.
Thus no repeatable loss remains on the tested sets; the primary result is
not relabeled as a zero-loss measurement.

The unrestricted 4,250-case experiment (149 gains, 19 losses) and the
variable-only 4,762-case experiment (116 gains, 18 losses, including 17
repeatable PyEx regressions) were rejected. Retaining Nielsen alternatives,
charging speculative cases to the depth bound, isolating arithmetic queries,
and preserving first-equation priority did not repair those regressions.
None of their extra backend APIs or iterator machinery is retained.

Artifacts retain `pyex-alignment-normalized-final-v1`, its two
`pyex-alignment-normalized-repeat` checks, quiet timings, rejected experiments,
and matching source/binary/input hashes; invocations are logged to
`z3agent.db`. Published through #11565 and squash-merged into `c3mv` as
`4f804bd483f1a41b2c90c09b3239d69b690881b7`; the merged tree matches the
validated feature tree. No full post-fix PyEx score is extrapolated from
these samples. GitHub CI is not fully green: native modules pass, but
investigated failures include an inherited `Solver.solutions` doctest
ordering difference, model-definition ordering, and the inherited
`4015.smt2` timeout.

### Additional PyEx gains: reuse indexof's right fragment

The next follow-up compares against the exact tree merged through #11565.
For an ordinary string variable `s` and a one-character literal `c`, let
`i = str.indexof(s, c, 0) + 1`. An extract `str.substr(s, i, len(s) - i)`
can reuse the existing `seq.idx.r(s, c)` when `str.contains(s, c)` holds.
Otherwise indexof is -1, so the extract is `s`. These two guarded
equalities replace the generic extract decomposition, avoiding another
prefix Skolem and a redundant word equation. The shared sequence axioms,
solver routing, and search budgets are unchanged.

The specialization is limited to word-level consumers. Length-only tails,
compound sources, and interpreted consumers retain their original
encoding. The consumer check follows concatenation parents transitively:
an immediate concat parent does not make a downstream extract, indexof,
or replacement safe for search scheduling. These guards protect search,
not the mathematical validity of the tail identity.

The less restricted direct specialization was rejected despite 269 gains
and four losses on 5,786 inputs. Three losses were repeatable: baseline
quiet medians 0.446/1.430/1.430 seconds became eight-second timeouts.
One tail had only length consumers; the other two fed interpreted
operations through concatenation. Removing forced equality phases,
reusing the existing contains predicate, and adding the exact tail-length
equation did not repair them. The final consumer-path and word-use guards
restore SAT in three quiet repetitions each, at candidate medians
0.450/1.460/1.453 seconds. The broader shared `seq.post` aliases and
one-way equality experiments were also rejected; none is retained.

Native tests cover early found/absent propagation, Unicode characters,
push/pop, compound sources, direct and indirect selector consumers, and
length-only consumers. All 135 native modules pass. Python checks cover
found/absent/end/empty tails, Unicode, nonzero offsets, multi-character
and empty needles, nonmatching cuts, incremental models, and bounded
decomposition/absence UNSAT checks. Prior alignment, selector,
replacement, and 257-character witness checks also pass.

The final matched comparison preserves all 5,786 preceding inputs and
adds 502 untouched PyEx inputs, disjoint from every earlier experiment
manifest. Only 118 eligible other-PyEx inputs remained, so the fresh
groups contain 384 entry-disposition and 118 other inputs rather than
the targeted 384/128. Original input bytes, five-second caps, model
validation, and 32 interleaved workers are unchanged. Groups overlap:

| Group | Inputs | Merged c3mv solved | Guarded repair solved |
|---|---:|---:|---:|
| Existing entry-disposition sample | 512 | 156 | 167 |
| Existing other-PyEx sample | 128 | 30 | 42 |
| All original c3mv-only controls | 1,529 | 1,472 | 1,471 |
| All former model errors | 290 | 272 | 272 |
| Untouched entry-disposition holdout | 384 | 112 | 114 |
| Untouched other-PyEx holdout | 118 | 31 | 43 |
| Distinct inputs, all groups | **6,288** | **3,416** | **3,577** |

The 12,576 invocations take 1,014.6 seconds: **167 gains and six losses**,
a net gain of 161 solved inputs. All gains are PyEx: 166 SAT and one
UNSAT, with the UNSAT matching the independent report-master run.
The untouched holdouts contribute **14 gains and zero losses**.
PAR-2 mean improves from 4.939 to 4.612 seconds. There are no errors,
invalid models, external watchdogs, or definite-answer contradictions,
including against 4,656 definite local report-master references.
Frozen source, binary, and input hashes match.

Two paired repeats cover all primary gains/losses, 120 prior
repeat-consistent alignment gains, the 17 repaired PyEx regressions,
all 33 previous bounded-witness gains, and 24 suffix regression controls:
343 distinct inputs per repeat. They produce 118 gains/zero losses and
114 gains/three losses, with **105 primary PyEx gains remaining gains
in both repeats**. Both repeats solve all 17 repaired PyEx cases, all
33 earlier gains, and all 24 suffix controls. The broad run retains
118/120 earlier alignment wins under the parallel cap; the two missed
cases are included in the quiet audit.

All six primary losses disappear as losses in repeat 1. Repeat 2 loses
`49e0625b...`, the previously cutoff-sensitive `f1d731d1...`, and
`str_replace193.smt2`. Three quiet runs per binary cover the union of
these losses and the two missed prior alignment wins: eight inputs.
Every run returns the same definite answer as the baseline, with
candidate medians 2.686-3.656 seconds. The two missed prior alignment
wins remain UNSAT, at 2.857/2.934 seconds versus baseline
2.898/2.886 seconds. Thus no repeatable regression remains on the
tested sets; the six primary losses are not relabeled as zero losses.

Artifacts retain `pyex-index-suffix-guarded-final-v1`, both
`pyex-index-suffix-guarded-repeat` checks, the two quiet audits, native
and semantic validation, and all rejected experiments. Invocations are
logged to `z3agent.db`. The guarded specialization is published through
#11572 targeting `c3mv`. No full post-fix PyEx score is extrapolated from
these samples.

### Additional PyEx gains: guarded finite-length expansion

Source-labelled traces of eight remaining PyEx gaps distinguish missing
active rules from delayed ones. Report-master solves all eight as SAT
in 32-144 milliseconds; the merged #11572 executable's explicit `seq`
backend reproduces these times. Before this change, default `nseq`
returns unknown on one and exceeds eight seconds on the other seven.
Master uses fixed-length character
expansion and length coherence throughout, one ternary alignment for
the MongoClient parsing case, eight quaternary alignments for header
normalization, and two guarded model-length cuts for authentication.
These are not all instances of the same model-based branching rule.

Supplying only source-string lengths from the validated master models
makes seven cases SAT in `nseq` in 42-510 milliseconds, without supplying
characters. Authentication still exceeds eight seconds in three runs;
supplying intermediate string-term lengths makes it SAT in 2.99-3.00
seconds. These stronger oracle-guided inputs diagnose search and
length-coherence gaps, not improvements on the original inputs.

The first implementation adds guarded finite-length expansion, without
changing backend routing or adding the general ternary/quaternary rules.
For lengths up to 20, a string is conditionally equated to its sequence
of indexed characters. The length cap limits this heuristic, not the
language accepted by the solver. Ordinary sources must feed a relevant
at, extract, or indexof; relevant at/extract terms are also eligible.
Only string alphabets are expanded.

The new fallback leaves a cumulative 2,176-node head start to the
existing search: 2,048 nodes plus one 128-node grace round, across final
checks rather than per SAT snapshot.
An unresolved leaf can request expansion earlier. Subsequent expansion
rounds yield after 128 nodes. String/integer conversions retain their
existing coherence-first scheduling instead of taking this fallback.
Length choices remain backtrackable SAT decisions, and the expansion
clauses are valid under their explicit length guards. The deduplication
cache and its retained expressions are trailed.

Eager expansion was rejected: the pilot gained 22 inputs but lost 43,
including established witness repairs. Arithmetic equality guards also
exposed an incremental re-internalization loop. Using paired lower and
upper guards, as in SAT-snapshot reconciliation, repairs that loop.
The first fallback scheduler displaced conversion coherence on
`leetcode_int-restoreIpAddresses/3055.smt2`; excluding conversion
workloads restores UNSAT at a quiet three-run median of 319 milliseconds.
The broad run of that rejected scheduler was stopped and is not an
acceptance result.

The 2,048-node scheduler's first complete 6,672-input comparison gained
74 inputs and lost two, with 60 PyEx gains remaining gains in two paired
repeats. Quiet testing exposed a real MongoClient slowdown: baseline
search finishes at 2,155 nodes, but premature expansion emits 107
axioms and increases its median from 2.405 to 2.978 seconds. Thus the
repeated parallel cutoff loss is not dismissed as timing noise.
A single grace round preserves the ordinary solve in the revised pilot.
Larger 3,072/4,096-node delays were rejected because the reduced trim
regression exceeds its resource budget. The native test budget is
unchanged; no diagnostic instrumentation remains.

All 135 native modules pass on the revised scheduler, including new
model and push/pop regressions. Previous suffix, Unicode, selector,
replacement, arithmetic, and 257-character semantic checks pass.
The revised 368-input pilot has 61 gains and one cutoff loss. Final
measurement freezes this exact source and preserves the original input
bytes, five-second limits, model validation, and 32 interleaved workers:

| Group | Inputs | Merged #11572 solved | Finite-length fallback solved |
|---|---:|---:|---:|
| Reused matched comparison | 6,672 | 3,693 | 3,755 |
| Additional unused entry-disposition holdout | 384 | 130 | 132 |
| Distinct inputs, combined | **7,056** | **3,823** | **3,887** |

The combined result is **69 gains and five losses**, net **+64 solved**.
There are 65 observed PyEx gains, including two on the unused holdout;
the remaining four gains are outside PyEx. Combined PAR-2 improves
from 4.875 to 4.815 seconds. There are no errors, invalid models,
external watchdogs, or answer contradictions, including against 5,424
definite local report-master references. Source, executable, and input
hashes match.

The first 384 added inputs were reused during scheduler tuning and are
not presented as an untouched final holdout. The additional 384 are
selected before seeing the revised broad result, disjoint from every
earlier follow-up manifest. No eligible unused other-PyEx cases remain.

Two paired repeats cover 362 inputs: all primary gains/losses, the
17 repaired PyEx regressions, 33 bounded-witness gains, 120 prior
alignment gains, 105 prior suffix gains, 24 suffix controls, and
11 sensitive controls. They produce 60 gains/one loss and 59 gains/one
loss. **55 primary PyEx gains remain gains in both repeats.** Both fresh
gains also remain gains in two additional repeats, giving **57
repeat-consistent PyEx gains**. All 17 repaired cases, 33 earlier
witness gains, and 105 suffix gains solve in every primary/protected run.

The primary run retains 119/120 prior alignment wins under the parallel
cap; the repeats retain 118/120. All five primary losses emit zero
fixed-length axioms. The original c3mv-only controls are 1,472/1,529
before and 1,471/1,529 after under this cap; the single lost control is
included in the quiet audit, rather than hidden by aggregate counts.

Three quiet runs per binary cover the union of primary/repeat losses,
missed prior wins, and the earlier MongoClient slowdown: nine inputs,
54 invocations. Every run returns the same definite answer, below five
seconds. Candidate medians are 2.584-3.312 seconds. MongoClient returns
SAT at 2.660/2.672-second baseline/candidate medians, with identical
2,155-node searches and zero expansion axioms. Thus its real slowdown
is repaired, and no repeatable loss of a definite answer remains on
the audited inputs. The five primary cutoff losses remain reported.

The exact final executable also solves five of the eight traced gaps
in three quiet repeats, with medians of 46 milliseconds, 1.966 seconds,
6.931 seconds, 2.110 seconds, and 1.604 seconds. Header normalization
still exceeds the report's five-second limit; the larger MongoClient,
remaining entry-disposition, and authentication representatives still
exceed eight seconds. General ternary/quaternary alignment and
model-directed length cuts remain unimplemented.

Artifacts retain `pyex-length-expand-final-v3`, its protected repeats,
`pyex-length-expand-fresh-v3` and fresh-gain repeats, the nine-case
quiet audit, `length-expand-exact-v3` representative measurements,
and `pyex-length-expand-final-v3-final-evidence.json`. Invocations are
logged to `z3agent.db`. This improvement is submitted together with
the delimiter-position cuts below. No full post-repair PyEx score is
extrapolated from these subsets.

### Additional PyEx gains: delimiter-position arithmetic

The next rule extracts a length consequence of master-style quaternary
alignment without introducing a fresh word witness or guessing an order:

```
x ++ unit(a) ++ y = p ++ unit(b) ++ q, a != b
    implies len(x) != len(p).
```

Different elements cannot occupy the same position in the equal words.
The AST manager must establish element distinctness; equal or merely
incomparable symbolic delimiters do not trigger this rule. It also
applies to generic sequences, not only strings.

Equation propagation adds the arithmetic fact after simplification and
before arithmetic propagation, with the originating equation's
dependency. Existing solver-facet deduplication and trailing manage its
lifetime. Only the first active equation is considered, preserving the
equation priority used by Nielsen splitting. No fresh string, backend
change, speculative substitution, or change to the finite-length
fallback's 2,176-node head start is involved.

Several stronger or earlier-scheduled alternatives were rejected.
Deterministic ternary-style substitution did not improve the large
MongoClient gap and could delay finite-length fallback. Fresh-variable
quaternary splitting looked promising in a 742-input pilot, with
16 gains and no losses. Its complete 7,056-input comparison instead
had **45 gains and 116 losses**. Proof-gated fresh alignment still had
14 gains and 115 losses in an expanded 885-input pilot. These are not
accepted improvements, despite attractive diagnostic timings.

Even the arithmetic rule needs disciplined scheduling. Scanning every
active equation produced 63 gains and four losses on 7,440 inputs,
including an unused 384-input holdout. Two matched repeats retained
43 primary gains. But quiet testing exposed a real MongoClient
regression: `3fabffc1` changed from a 2.412-second baseline median to
three eight-second timeouts. This global version was rejected.

Restricting the rule to the leading equation repairs that regression:
three quiet runs give baseline/candidate medians of **2.400/2.384
seconds**, identical **1,666-node searches**, and no finite-length
expansion. All six primary/repeat loss controls from the global version
solve in three runs per binary, each below five seconds.

The revised 923-input pilot has 28 gains and one non-PyEx cutoff loss.
It retains all 17 required repairs, 33 bounded-witness gains,
120 alignment gains, 105 suffix gains, 24 suffix controls, and
57 finite-length gains. All 116 losses from the rejected fresh-variable
version also solve. The exact revised source passes all 135 native
modules, 75 positional SAT/UNSAT/model/push-pop checks, and the existing
alignment and guarded-suffix semantic suites. Focused native tests
check equation dependencies, rollback, incomparable delimiters, and
deferral behind an earlier equation.

Final measurement compares against the accepted finite-length
executable, not the published suffix baseline. It freezes original
inputs, five-second caps, model validation, and 32 interleaved workers:

| Group | Inputs | Finite-length baseline solved | Leading-equation cuts solved |
|---|---:|---:|---:|
| Expanded matched comparison | 7,440 | 4,001 | 4,031 |
| Additional unused entry-disposition holdout | 384 | 128 | 132 |
| Distinct inputs, combined | **7,824** | **4,129** | **4,163** |

This is **35 gains and one cutoff loss**, net **+34 solved**.
There are 33 observed PyEx gains and two non-PyEx cutoff gains.
Combined PAR-2 improves from 5.045 to 5.019 seconds. There are no
errors, invalid models, external watchdogs, or answer contradictions,
including against 6,192 definite local report-master references.
Earlier accepted main/holdout definite answers also agree. Source,
executable, and input hashes match.

The expanded comparison includes the rejected global rule's 384-input
holdout; those inputs are now reused, not presented as untouched.
The new holdout is selected before the revised broad result, disjoint
from all earlier follow-up manifests. No eligible unused other-PyEx
cases remain.

Two paired repeats cover 380 inputs: every new primary/fresh gain and
loss, plus all protected repairs and prior gain families. They have
23 gains/two losses and 28 gains/one loss. **16 primary PyEx gains and
two fresh gains remain gains in both repeats**, giving **18
repeat-consistent PyEx gains**. All 18 are UNSAT, with the new inference
active; these are not claimed as new SAT witness gains.

All 17 required repairs, 33 bounded-witness gains, 120 alignment gains,
105 suffix gains, 24 suffix controls, and 11 sensitive controls solve
in the primary run and both repeats. Under the parallel cap, the
finite-length gain controls retain 56/57, 53/57, and 55/57; every miss
is included in quiet verification rather than hidden by the net gain.
The original c3mv-only controls improve from 1,470/1,529 to 1,472/1,529
in the broad run.

Three quiet runs per binary cover the union of final primary/repeat
losses, missed protected controls, and losses from the rejected global
version: **11 inputs, 66 invocations**. Every run returns the same
definite answer below five seconds; the slowest individual run is
3.470 seconds. Candidate medians range from 2.400 to 3.446 seconds,
with none more than 10% slower than baseline. The former real
MongoClient regression now has 2.424/2.400-second medians and identical
1,666-node searches. The single primary cutoff loss remains reported.

Artifacts retain `pyex-positional-first-bounds-final-v2`, its two
protected repeats, `pyex-positional-first-bounds-fresh-v2`, the quiet
audit, and `pyex-positional-first-bounds-final-v2-final-evidence.json`.
The source-patch SHA256 is
`65e190d3afb9892318e23d0d4fa37743dd4c590859b49f7dab8d4a014f38a6ef`;
the executable SHA256 is
`440158a741715d39c6f0974626ca088a1eaed27260cf54f776dd8f4511a490ce`.
Invocations are logged to `z3agent.db`. This improvement and the
finite-length fallback are submitted together to `c3mv`. No full post-repair PyEx
score is extrapolated from these subsets.

### Additional PyEx gains: share indexed containment witnesses

The next structural bottleneck is duplicate positive-containment
decompositions. `indexof(s,t,0)` already uses `seq.idx.l(s,t)` and
`seq.idx.r(s,t)` to describe its first occurrence, but nseq's positive
`contains(s,t)` assignment independently introduces two fresh fragments.
Nielsen search then has to align the two descriptions of the same
occurrence before it can construct a coherent model.

The candidate reuses the indexof fragments when the zero-offset index is
already internalized and the source is an uninterpreted constant. The
containment dependency and ordinary equation trailing are unchanged.
Otherwise the original fresh-fragment path is preserved. No new index
term is internalized, no model value becomes an unconditional fact, and
neither the backend routing nor the finite-length head start changes.

There is a second scheduling guard: retain the original decompositions
when another uninterpreted source has an internalized zero-offset search
for the same needle. This preserves the order of parallel delimiter
pipelines. The check scans the needle's equivalence-class root parents;
it does not assert any additional semantic restriction.

The atomic-source restriction is important. Sharing on interpreted
selectors as well produced a 929-input pilot with 38 gains/four losses,
but quiet checks exposed genuine slowdowns: MongoClient `81656a27`
increased from 2.442 to 3.021 seconds, and entry-disposition `95ac7403`
from 2.712 to 4.491 seconds. That broader rule is rejected. Restricting
sharing to atomic sources restores these controls near baseline while
retaining the large diagnostic improvements.

The atomic-only prototype completed 7,824 inputs with 4,158 to 4,219
solved (64 gains/three losses), plus one gain/no losses on a disjoint
384-input entry-disposition holdout. Two protected repeats left 53
repeat-consistent PyEx gains. All 12 quiet controls solved below five
seconds, but the Leetcode `numUniqueEmails` control `a05695bb` slowed
from 2.378 to 2.756 seconds. This fails the 10% median guard and is not
accepted. The parallel-source guard restores its original 2,285-node
search and 539 expansions: matched quiet medians are 2.618/2.605 seconds.

| Diagnostic | Published source | Both sharing guards |
|---|---|---|
| Entry-disposition `8066c768` | Eight-second timeout | Validated SAT, 2.665 seconds |
| Header normalization `a7f9d65a` | SAT, 4.261 seconds | Validated SAT, 0.358 seconds |
| URL authentication `ff8a7323` | SAT, 1.463 seconds | Validated SAT, 1.467 seconds |
| MongoClient `c6ee2cf4` | Eight-second timeout | Eight-second timeout |
| WWW authentication `bddfe21d` | Eight-second timeout | Eight-second timeout |

These are diagnostic timings, not a full PyEx score. The normalization
case drops from 2,331 to 171 DFS nodes without finite-length expansion.
A reduced normalization regression returns unknown in the published
solver at one million resource increments and validated SAT with sharing
at about 712,000. Native tests cover that budgeted regression, repeated
and overlapping occurrences, distinct offsets, and model validity after
push/pop. All 135 native modules, the 75 positional semantic checks,
the alignment/index-suffix suites, and CLI/Python smoke tests pass.

Other tested alternatives are not retained: preserving the arithmetic
base cache across temporary-assumption queries had six gains/seven
losses on 929 inputs; model-guided fixed-length ordering regressed two
diagnostics severely; moving empty Nielsen alternatives behind fresh-tail
extensions exhausted an existing native-test resource budget. Restricting
that reordering to finite block prefixes produced only eight gains/four
cutoff losses in its pilot, with modest search reductions. Constraint
hashing and avoiding unchanged token-vector trails produced only small
diagnostic overhead reductions and are also omitted from this change.
Deferring containment entirely to the existing indexof axioms did not
repair the email slowdown. Restricting sharing to sources with assigned
negative-containment parents lost the budgeted normalization regression;
that restriction is also rejected.

The guarded candidate's 441-input protected pilot has 42 gains/two
cutoff losses. All 36 quiet inputs (216 invocations) agree, finish below
five seconds, and stay within the 10% median guard, including every
missed protected gain.

Final acceptance against the published `f68efde30` executable:

| Selection | Inputs | Before solved | After solved | Gains | Losses |
|---|---:|---:|---:|---:|---:|
| Full measured union | 7,824 | 4,109 | 4,156 | 50 | 3 |
| Newly preselected entry-disposition holdout | 384 | 125 | 127 | 2 | 0 |

These are matched five-second runs with model validation, not a full
PyEx score. The primary net gain is 47. Two 427-input protected matched
repeats retain 35 consistent new PyEx SAT gains. The holdout's two UNSAT
cutoff gains do not repeat and are not included in that count. All six
primary UNSAT gains and both holdout UNSAT gains agree with independent
definite results from the frozen report-master.

The final quiet audit covers 41 inputs and 246 invocations, including
every primary/repeat loss, missed protected gain, and prior witness-sharing
control. All answers agree, all runs finish below five seconds (maximum
3.812 seconds), and the worst candidate median increase is 2.74%.
After quiet recovery, all 17 required repairs, 33 bounded gains, 120
alignment gains, 105 suffix gains, 24 suffix controls, 57 length gains,
18 positional gains, and 11 sensitive controls are retained. The 1,471
previously solved original c3mv-only controls are also retained: 1,470
in the primary run and `28_attack` recovered quietly. There are no
errors, invalid models, answer contradictions, or external watchdogs.
All 135 native modules, semantic suites, and CLI/Python smoke tests pass.

Artifacts retain `pyex-contains-index-distinct-sources-final-v1`, its
two protected repeats, `pyex-contains-index-distinct-sources-fresh-v1`,
the final-evidence, protection-recovery, and original-win-recovery JSON
audits. The source-patch SHA256 against `f68efde30` is
`7045adaf42e3d23eac396e0c2173094b2f7b665c79b500f7724dabb2a5bdadb3`;
the executable SHA256 is
`f655dc08c1157b698ba34e4a8e9164e9fccdcf5027704e08c128d0ec4f872552`.
Benchmark invocations are logged to `z3agent.db`. Full PyEx parity with
report-master remains unestablished.

The two remaining hard diagnostics still illustrate why node count
alone is a poor effort bound: ordinary search can spend eight seconds
below the existing 2,176-node finite-length head start.
With the guarded candidate, MongoClient `c6ee2cf4` consumes about
14.85 million resource increments at 1,486 nodes; WWW authentication
`bddfe21d` consumes 7.90 million at 1,562 nodes. Neither expands lengths.
A next experiment should use a soft resource-count ceiling at search-tree
yield points, alongside the node ceiling, and accumulate ordinary-search
work across final checks. `reslimit::count()` provides that measure
without pushing a nested cancellation limit. Reaching the soft ceiling
must remain an unresolved search result, never an UNSAT fact, and must
not reset outer cancellation. This is a proposed experiment, not part of
the current change.

## Baseline and scope

Sources:

- [CoZ3 comparison](https://z3prover.github.io/coz3/compare_stats.html?a=run-1278-qf-slia-c3mv-stats.md&b=run-1277-qf-slia-master-stats.md)
- [c3mv report](https://z3prover.github.io/coz3/run-1278-qf-slia-c3mv-stats.md):
  `c68a06bc4f45e3e2b4a6ebb391cb6a9f4ee0d6f8`
- [master report](https://z3prover.github.io/coz3/run-1277-qf-slia-master-stats.md):
  `9af2dac2eed3ff805f228ef481e2105b53767b19`
- Inputs: `QF_SLIA.tar.zst` from
  [SMT-LIB release 2025](https://zenodo.org/records/16740866).

Both reports use `-T:5 model_validate=true`, the same input preset, and
`rise-runner-2`. All 84,411 input paths match.

| Result | c3mv | master |
|---|---:|---:|
| SAT | 27,842 | 44,243 |
| UNSAT | 32,132 | 32,271 |
| Solved, exit 0 | 59,974 | 76,514 |
| Timeout | 21,484 | 7,709 |
| Unknown | 2,663 | 188 |
| Error | 290 | 0 |

Master solves 18,069 cases that c3mv does not: 15,456 c3mv timeouts,
2,369 unknowns, and 244 errors. Conversely, c3mv solves 1,529 master
timeouts. The net solved-count deficit is 16,540. There are no SAT/UNSAT
disagreements among pairs with successful, definite results.

All 290 errors explicitly report an invalid model, not a crash.
Of these, 244 are master-solved and 46 are master timeouts.
14,499 of the 18,069 master-only solves finish below one second in the
published master run; these are not predominantly near-timeout noise.

| Master-only solves by family | Count |
|---|---:|
| Reynolds/PyEx | 14,637 |
| full_str_int/Conbyte, all four encodings | 2,081 |
| StringFuzz/transformed | 885 |
| Reynolds/Kaluza | 205 |
| Leetcode | 137 |
| Noetzli rewrite verification | 79 |
| Denghang | 23 |
| Norn | 13 |
| Jiang | 5 |
| ReDoS | 2 |
| Webapp | 2 |

Within PyEx, 13,535 losses come from the three
`httplib2-entry-disposition` encodings alone. Across all losses,
15,085 inputs contain `str.contains`, 15,068 contain `str.indexof`,
16,707 contain `str.substr`, and 2,212 contain `str.to_int`.
These feature counts overlap and do not assign every case to one cause.

## Controlled reproduction

Rebuilt the Release CMake/Ninja `shell` target on Windows and verified
that `z3 -version` reports the exact c3mv hash above. The existing build
had stale generated parameter headers shadowing the current source
headers; those build artifacts were moved aside before the successful
build.

Selected 37 inputs spanning the dominant loss families, invalid models,
and three c3mv win controls. Ran each with the same executable and
`-T:5 model_validate=true -st`, changing only `smt.string_solver`.

- `nseq`: 17 timeouts, 11 unknowns, six invalid models, and three
  successful win controls.
- `seq`: all 34 selected loss/error inputs solve, with validated models
  where applicable, in 0.032-0.328 seconds. All three win controls time out.
- Disabling `seq.monadic_leaf`, enabling `seq.mem_monadic_endgame`, or
  enabling `seq.eq_approx` recovers none of eight selected difficult
  inputs, tested with each option separately.

These are within-c3mv engine comparisons, not a locally rebuilt exact
master comparison. Published master results supply that baseline.
Windows timings should not be equated numerically with the CoZ3 runner.
The qualitative outcomes reproduce the gap, including the opposite
direction on the win controls. Selection is diagnostic, not a random
sample from which recovery counts can be extrapolated.

The default changes from `seq` to `nseq` in
`src\params\smt_params_helper.hpp:158`; dispatch is in
`src\smt\smt_setup.cpp`. This explains why the same invocation exercises
different architectures. The latest equation-abstraction integration is
opt-in (`seq.eq_approx=false`); enabling it is not a general remedy here.
No commit-by-commit regression bisection was performed.

## Root causes and supporting experiments

### 1. Outer arithmetic and leaf string models are not reconciled

**Confirmed correctness defect; fix before tuning performance.**

In Kaluza `21393.corecstrs.readable.smt2`, the generated model has
`I0_2 = 0` and a one-character `T4_2`, violating the asserted equality
`I0_2 = str.len(T4_2)`.

In Norn `ab/norn-benchmark-139.smt2`, the leaf chooses `var_4 = "ab"`,
but the outer model has `v = 1`, violating
`2*v = str.len(var_4) + 2`. The leaf arithmetic model uses `v = 2`.
Adding the entailed bound `v >= 2` changes the result from invalid model
to validated SAT in 0.035 seconds.

StringFuzz `regex-033-reverse-reverse-fuzz.smt2` illustrates conversion
coherence too: the outer interpretation allows the numeric comparison,
but the final strings yield `m = "0"` and make
`str.len(x) < str.to_int(m)` false.

The integration only exports selected assumptions, power exponents, and
lengths of uninterpreted stoi arguments before accepting a leaf:
`src\smt\theory_nseq.cpp:764-914`. General witness lengths and evaluated
conversion values are not uniformly reconciled. Model construction uses
the leaf arithmetic model for fresh lengths and membership witnesses:
`src\smt\theory_nseq.cpp:639-762`.

This identifies a broken integration invariant, not one proven common
line-level defect behind all 290 invalid models.

### 2. Negative containment has no general constructive completion

**Confirmed incompleteness on a tiny SAT instance; dominant workload fit.**

This returns unknown immediately with nseq and SAT with seq:

```smt2
(set-logic QF_SLIA)
(declare-const s String)
(assert (>= (str.len s) 2))
(assert (not (str.contains s ",")))
(assert (not (str.contains s "=")))
(check-sat)
```

In the original PyEx `e2e1ebaf...` input, terminal search nodes have no
active equations or disequations, but retain negative-containment
obligations over a substring or a symbolic-character/substring
concatenation. The solver returns unknown after only 12 DFS nodes.
Other PyEx cases spend the timeout exploring thousands of decompositions.

`src\ast\seq\seq_ncontains_facet.cpp:165-280` performs token matching and
a length gate, then leaves unresolved obligations pending. There is no
registered negative-containment splitter in
`src\smt\theory_nseq.cpp:159-195`. The model-completion fallback is
one-shot, requires usable character values, and is length-capped at 256:
`src\ast\seq\seq_eq_facet.cpp:1054-1240`.

An equivalent all-regex encoding of a reduced PyEx prefix/absence
condition validates in 0.031 seconds. Merely adding an absence regex
while retaining `str.at` still returns unknown in that reduced example:
symbolic-character/equation integration must be addressed as well.
Not every PyEx timeout has been individually attributed to containment.

### 3. Empty-side disequations can become stranded after substitution

**Concrete stuck state with a directly matching missing code path.**

Noetzli `str-pred-small-rw_99.smt2` reduces to:

```smt2
(set-logic QF_SLIA)
(declare-const x String)
(declare-const z Int)
(assert (not (= (= x (str.substr "A" z z)) (= x ""))))
(check-sat)
```

This is UNSAT: `str.substr("A", z, z)` is empty for every integer `z`.
Nseq returns unknown in 0.044 seconds; seq proves UNSAT in 0.033 seconds.
The terminal node contains `epsilon != str.substr("A", z, z)` while the
arithmetic facet has length zero for the substring.

`deq_propagation` does not discharge/refute this using arithmetic length,
and `deq_split` explicitly skips empty sides:
`src\ast\seq\seq_eq_facet.cpp:900-978`. The initial notification path
already handles syntactically empty disequations by adding a positive
length constraint (`src\smt\theory_nseq.cpp:322-347`), but an empty side
created later by substitution is not covered there.

### 4. Regex length guesses enumerate instead of using a persistent bound

**Confirmed by an entailed reformulation and propagation-order evidence.**

Denghang `instance53910.smt2` requires a sanitized string longer than 20.
The joint regex language admits only the short alternative `"ls "`;
the other alternative contains a forbidden quote. Master and seq prove
UNSAT quickly, but nseq times out.

At five seconds nseq performs 1,601 final checks and reports 1,600 theory
conflicts, with one DFS node per solve. No membership-bound propagation
calls are recorded. Adding the entailed membership

```smt2
(assert (str.in_re X ((_ re.loop 21) re.allchar)))
```

changes nseq to UNSAT in 0.036 seconds.

`mem_propagation` tries a concrete length from its local arithmetic model
and reports a conflict conditional on that exact guess:
`src\ast\seq\seq_mem_facet.cpp:687-783`. The bound-to-regex plugin runs
after it (`src\smt\theory_nseq.cpp:163-164`), so an early conflict
prevents the persistent lower bound from being installed. Rejecting
lengths one at a time does not establish a global upper bound.

Norn `ChunkSplit/norn-benchmark-12.smt2` exhibits a related repeated
outer-search pattern: 1,082 final checks and 1,081 theory conflicts.
Its exact learning/progress issue still needs a separate reduction.

### 5. Short-string conversion bounds arrive too late or are unavailable

**Confirmed missing effective propagation on two Conbyte UNSAT cases.**

Conbyte `addStrings/69.smt2` (Trau encoding) and `addStrings/440.smt2`
(CVC4 encoding) each time out with nseq and solve with seq in about
0.04 seconds. Adding only the universally valid lemmas

```smt2
(assert (<= (str.to_int (str.at s i)) 9))
```

for their existing terms makes nseq prove UNSAT in 0.037 and 0.034
seconds. `str.at` yields either empty, a non-digit, or one decimal digit;
its conversion is therefore -1 or between 0 and 9.

`src\ast\seq\seq_stoi_facet.h:91-146` installs the numeric upper bound
only after obtaining a concrete argument length. Also,
`src\smt\theory_nseq.cpp:801-832` continues into tree search even when
the coherence pass just injected new outer axioms. The latter is a
scheduling issue to test, not yet an experimentally isolated cause.

The same bound does not solve the sampled `add_binary` timeout and
unknown. Those require further character/conversion consistency work;
do not generalize the two-case recovery to all 2,081 Conbyte losses.

### 6. Disequation splitting introduces unsupported symbolic regex heads

**Confirmed terminal shape; explains a separate class of regex unknowns.**

StringFuzz `regex-020-graft-graft.smt2` is just `x in a*`, `len(x)=3`,
and exclusion of `"abb"`, `"bab"`, and `"aab"`. The obvious model is
`"aaa"`, yet nseq returns unknown. Three repeated runs take 184-191 ms.

Its terminal nodes contain memberships such as
`unit(symbolic_char) ++ tail in a*` and corresponding exact-length
memberships. Disequations have already been discharged.
The monadic engine cannot directly decide arbitrary symbolic units;
the derivative scan computes a residual but does not replace a partially
consumed membership when it encounters a remaining sequence token:
`src\ast\seq\seq_mem_facet.cpp:613-682`.

Further, an unsuccessful split can leave `has_more=true` even when
retrying at another cost cannot help, for example on the gave-up path
of `mem_monadic_split` (`src\ast\seq\seq_mem_facet.cpp:1133-1160`).
The generic cost loop repeats all eligible plugins
(`src\util\stx_search_tree.h:1000-1045`). This case records about
10,000 calls to several split plugins for just 114 DFS nodes.
That is dispatch work, not 10,000 successful splits.

## Implementation sequence and acceptance criteria

| Priority | Work | Acceptance |
|---|---|---|
| P0 | Reconcile every shared string witness with outer arithmetic/character/conversion values before returning FC_DONE. Export required candidate equalities with dependencies; invalidate stale candidates on relevant changes. Audit fresh-value and snapshot paths. | All six sampled invalid models validate; then all 290 report errors are either valid definite results or explicit unknown, never invalid SAT. Include scopes and conflicting outer assignments. |
| P1a | Handle empty-side disequations after substitution, with the appropriate nonempty-length constraint and dependency. Use known zero/positive lengths in equation/disequation propagation. | Noetzli 99 becomes UNSAT; tests cover both orientations, cancellation-created empty sides, and scoped dependencies. |
| P1b | Add cheap static stoi bounds for `str.at` and other bounded-length terms; specialize empty/one-character conversions. Yield to the outer core after adding coherence axioms before searching a stale assignment. | Both addStrings examples solve without supplied lemmas. Separately measure add_binary and restoreIpAddresses; preserve -1, leading-zero, and out-of-range behavior. |
| P1c | Install proven membership length bounds before guessed-length witness search, or make witness search wait for bound propagation. Feed lower/upper intervals to the joint language solver; learn interval/global conflicts rather than excluding one arbitrary length at a time. | Denghang 53910 solves without the extra assertion, with a bounded number of final checks. Reduce and address ChunkSplit 12 separately. |
| P2 | Make literal-needle negative containment constructive: use complement-of-contains regex constraints and joint witness candidates, or an equivalent sound dedicated procedure. Normalize shared indexof/at/substr decompositions and check the candidate against all facets. Keep symbolic needles guarded, not silently satisfied. | The tiny negative-containment example and original PyEx unknowns become validated SAT. First measure all 13,535 entry-disposition losses, then all 14,637 PyEx losses; preserve PyEx UNSAT cases. |
| P3 | Support symbolic-character guards/residual memberships, or try a jointly validated regex witness before decomposing disequations into symbolic heads. Distinguish unsupported, budget-exhausted, and genuinely higher-cost split offers to avoid futile cost retries. | StringFuzz 020 becomes validated SAT; broader transformed StringFuzz losses improve without losing generated-regex wins. Plugin attempts fall with no change to completeness/fallback semantics. |
| P4 | Re-run the entire matched corpus, then review default/auto routing using measured features. Keep explicit seq as a baseline/workaround; consider bounded fallback only if needed, not as a substitute for correctness fixes. | Zero invalid models and zero definite-result contradictions. Reach at least master's 76,514 solved count while explicitly tracking retention of the 1,529 c3mv-only solves. |

P0 is a prerequisite for accepting any SAT-performance improvement.
P1a/P1b/P1c are bounded independent fixes after the model invariant is
understood; P2 has the largest measured workload opportunity. Do not start
by raising the depth cap, increasing regex budgets, or enabling all
experimental plugins: the observed failures include immediate unknown,
invalid models, and non-progressing outer search, not just exhausted budgets.

For each change, add focused regressions in the existing facet and nseq
integration tests. Distinguish proven bounds from model guesses and
retain their dependencies through substitutions, learned conflicts,
push/pop, and candidate rejection. Use model validation throughout.

Measure targeted cases at five seconds first. Use longer limits and
multiple seeds only to investigate remaining failures. For the final
corpus comparison, use the same runner, build configuration, timeout,
and validation settings as the baseline, and record per-file outcomes,
wall time, memory, final checks, DFS nodes, unknown reason, successful
splits, and plugin attempts. Report losses and wins separately, not just
aggregate speed or averages over solved cases.

The successful-result union of the published runs is 78,043 cases. This
is a useful coverage reference, not a promise that a sequential portfolio
or any one proposed change attains it within five seconds.

## Reproduction inputs

Paths below are relative to `non-incremental\QF_SLIA` in the archive.
The investigation's complete 37-case manifest and raw statistics are
retained separately as session artifacts.

| Mechanism/control | Input |
|---|---|
| PyEx timeout | `20180523-Reynolds\pyex\peterc-pyex-doc-cav17-zz\httplib2\httplib2-entry-disposition\d369e85c3433285431b761ad13aac0d78ab4ff70a83a18839e9afe6b.smt2` |
| PyEx stuck negative containment | `20180523-Reynolds\pyex\peterc-pyex-doc-cav17-z3\httplib2\httplib2-entry-disposition\e2e1ebaf6541fb472e8efa8476632c2c3a19455690731f6e838eb7bd.smt2` |
| Symbolic regex heads | `20230327-stringfuzz-lu\transformed\z3str2\regex-020-graft-graft.smt2` |
| Conversion timeout | `20230327-stringfuzz-lu\transformed\z3str2\regex-032-translate-fuzz.smt2` |
| Conversion invalid model | `20230327-stringfuzz-lu\transformed\z3str2\regex-033-reverse-reverse-fuzz.smt2` |
| Kaluza invalid model | `20180523-Reynolds\kaluza\unsat\big\21393.corecstrs.readable.smt2` |
| Norn invalid model | `2015-Norn\ab\norn-benchmark-139.smt2` |
| Empty-side disequation | `20190311-str-small-rw-Noetzli\str-pred-small-rw\str-pred-small-rw_99.smt2` |
| Substring invalid model | `20190311-str-small-rw-Noetzli\str-pred-small-rw\str-pred-small-rw_620.smt2` |
| Conbyte digit bound, Trau | `2019-full_str_int\py-conbyte_trauc\leetcode_int-addStrings\69.smt2` |
| Conbyte digit bound, CVC4 | `2019-full_str_int\py-conbyte_cvc4\leetcode_int-addStrings\440.smt2` |
| Remaining binary-addition timeout | `2019-full_str_int\py-conbyte_cvc4\leetcode_int-add_binary\69.smt2` |
| Length-guess enumeration | `20230329-denghang\instance53910.smt2` |
| Repeated final checks | `2015-Norn\ChunkSplit\norn-benchmark-12.smt2` |
| Keep: generated-regex SAT | `20230327-stringfuzz-lu\generated\variants\03f131c3.smt2` |
| Keep: arithmetic/equation UNSAT | `2018-Kepler\quad-264-5-1-unsat.smt2` |
| Keep: regex-length SAT | `20230327-stringfuzz-lu\generated\regexlengths\regex-lengths-00351-19.smt2` |

For a selected input `$case`, compare the two engines in PowerShell:

```powershell
.\build\z3.exe -T:5 model_validate=true -st smt.string_solver=nseq $case
.\build\z3.exe -T:5 model_validate=true -st smt.string_solver=seq $case
```

For an unknown, set `$env:NSEQ_DUMP_UNKNOWN='1'`. For a small search-tree
trace, set `$env:NSEQ_DOT_FILE` to an explicit output file and
`$env:NSEQ_DOT_MAX_NODES='250'`. Use `-v:11` with model validation for
the failed assertion and evaluated values. Tracing changes timing, so
keep diagnostic runs separate from timed comparisons.

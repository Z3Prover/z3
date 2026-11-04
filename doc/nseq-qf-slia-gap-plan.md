# QF_SLIA: closing the c3mv/master gap

Investigation date: 2026-11-04. Implementation has started with the P0
model-coherence increment below. Baseline sections describe the original
branch before these changes.

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
negative-containment, regex-bound, static digit-bound, and symbolic-head
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

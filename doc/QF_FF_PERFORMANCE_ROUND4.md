# QF_FF: measured optimization experiments

This round tests the performance leads from the paper-artifact and real-circuit
comparison. It compares the pre-change Z3 executable with isolated changes before
selecting the defaults. Proof reconstruction and certificates remain v2 work.

## Method

The main selection contains 328 inputs: all 100 sequential bit-sum queries and
all 32 arithmetic-shift queries, plus 64 CirC determinism, 40 CirC soundness,
40 pure-field translation-validation, 20 small-field algebra, 8 QED2,
16 mixed translation-validation inputs, and all 8 imported real-circuit queries.
The other families were selected deterministically by input hash, round-robin
across the historical Z3 outcome categories. This intentionally includes hard
cases; its aggregate solve rate is not an estimate for the full 4,212-case corpus.

Every primary run uses a fresh process, a 10-second wall-clock limit, a 4 GiB
sampled resident-memory limit, and eight concurrent workers. Parsing and process
startup are included. Configurations are rotated within each case. Compilation
and regression tests run outside the timed comparison. These are local throughput
measurements, not machine-isolated latency measurements. Input assertions are
unchanged; the artifact-specific `QF_BVFF` logic spelling is adapted to `ALL`.

The 76-input, two-second exploratory screen is stored separately and is not
mixed into the primary results. A separate 10-second follow-up checks the
substitution and pair-order experiments. Incremental basis reuse is an API
microbenchmark, because the public artifact inputs are independent single checks.

The frozen baseline is the executable used for the earlier paper comparison:
SHA-256 `ded108b8c0b65169bf8b64c2444e80e7b5f76f6ea527fb8c1ebbe3ca6d86439a`.
This round does not rerun cvc5 performance. In particular, it does not substitute
cvc5 1.4.0 timings for the earlier 1.3.4 artifact measurements.

## Experiments

1. **Repeated bit propagation.** Alternate polynomial elimination with no-wrap
   bit-sum deductions. Preserve Boolean digit variables in wide/nonlinear
   definitions, and cancel matching non-bit polynomial tails to expose equal
   encodings at later circuit layers. Boolean domains, contiguous powers of two,
   and `2^width <= p` are required. Original premises are retained in conflict
   dependencies. The algebraic justifications are comments beside each rule.
2. **Substitution-growth guard.** Estimate the term expansion of substituting a
   multi-term definition and leave the equation in place above 256 predicted
   terms. This tests a conservative heuristic, not shared polynomial DAGs or
   every possible substitution policy.
3. **Basis pair ordering.** Schedule pairs by increasing LCM degree with a
   deterministic priority queue. Retain all pairs and the existing product
   criterion. This is a scheduling experiment, not an F4 implementation.
4. **Native SMT routing.** After the pure-field algebra tactics, try native SMT
   theory combination before committing to whole-problem bit-blasting. The native
   theory retains its exact BV fallback when algebra is inconclusive.
5. **Basis reuse.** Reuse an exact, bounded basis within a persistent native SMT
   solver. Cache identity includes the prime, every input polynomial, and every
   premise-index dependency; no context-owned AST pointers or approximate keys
   are used. Changed disequalities are still reduced separately. This does not
   yet incrementally extend bases for approximately similar equation sets.

## Results

The primary paired comparison completed all 984 runs. It found no definite-answer
contradictions and no loss of an input solved by the frozen baseline.

| Family | Inputs | Baseline | Repeated bits | Bits + native routing |
| --- | ---: | ---: | ---: | ---: |
| Sequential bit sums (entire family) | 100 | 25 | 100 | 100 |
| Arithmetic shifts (entire family) | 32 | 0 | 31 | 31 |
| CirC determinism (sample) | 64 | 21 | 42 | 42 |
| CirC soundness (sample) | 40 | 13 | 13 | 15 |
| Mixed translation validation (sample) | 16 | 11 | 11 | 13 |
| Pure-field translation validation (sample) | 40 | 20 | 20 | 20 |
| Small-field algebra (sample) | 20 | 13 | 13 | 13 |
| QED2 (sample) | 8 | 5 | 5 | 5 |
| Real-circuit output determinism | 8 | 2 | 3 | 3 |
| **Selected total** | **328** | **110** | **238** | **242** |

Repeated bit propagation adds 128 solved cases. Native routing adds four more:
`sound_bvlshr_2`, `sound_bvsub_2`, and two CirC translation-validation queries.
The 64-bit arithmetic-shift query remains unresolved; the no-wrap premise must
not be weakened to force that case through the bit recognizer.

Hermez fee computation changes from a 10-second timeout to UNSAT in 0.40 seconds.
Dark Forest whitelist (0.33 seconds) and MACI Merkle inclusion (2.25 seconds)
remain solved. Dark Forest move, MACI signature, and Plonky2 inverse, multiply-add,
and reduce still time out. These are the imported monolithic output-determinism
queries, not end-to-end execution of Picus or SNARK proof generation.

The 11-case follow-up at 10 seconds confirms the rejected prototypes: the
256-term growth guard solves 3/11 versus 4/11 without it, losing Hermez to a
timeout. LCM-degree pair scheduling solves the same 4/11, and changes two
small-field runtimes from 0.53/0.58 seconds to 1.06/1.00 seconds. The two-second,
76-case screen reached the same qualitative conclusion. Both prototypes have
been removed from the active solver; their source snapshot and measurements are
retained. This evidence rejects those particular heuristics, not growth control
in general, other pair heuristics, shared DAGs, or F4.

## Correctness and integration

All 78 primary SAT models were retrieved outside timing and checked by an
independent Python evaluator against every original assertion. All passed.
Of the 132 new answers, 131 agree with at least one definite cvc5 answer from the
earlier corpus run; none contradict one. Hermez has no definite cvc5 reference
in that run. No independently checked UNSAT certificates are claimed.

Semantic regression testing exposed an equality-class model-construction bug
when the new native route handled a field-valued conditional. A relevant root
can inherit its theory variable from another class member. The native checker
now records both the member and root values, retaining their equality premise.
A dedicated conditional-model regression covers this path. This integration fix
is included in the final executable verification below.

The C++ finite-field tests and all eleven Python suites pass. These include 150
randomized formulas checked against exhaustive enumeration and cvc5 1.4.0,
22,560 rewrite evaluations, 240 enumerated root/factor formulas, 904 algebraic
root/exclusion checks, guarded bit-decomposition and core checks, mixed-theory
models, large-field Poseidon combinations, cancellation, forced BV fallback,
incremental assumptions, push/pop, and reset. The benchmark model evaluator also
passes 6,460 exhaustive BV checks. Detailed commands and output are retained.

## Incremental basis reuse

Three fresh-process repetitions per setting run 2,000 incremental checks on
`x*x + y*y = 5, x*y = 2`, varying an uninterpreted integer-valued observer of `x`
under push/pop. Every returned model is validated outside the timed interval.
The numbers below are medians of the accumulated `check()` time for the last
1,999 checks; construction, Python assertions and model validation are excluded.

| Field | Cache off | Cache on | Reduction |
| --- | ---: | ---: | ---: |
| F97 | 0.1720 s | 0.1546 s | 10.1% |
| F65537 | 0.1721 s | 0.1546 s | 10.2% |
| BN254 scalar field | 0.2445 s | 0.1906 s | 22.0% |

Each enabled run records 1,999 hits after its initial miss. This is a deliberately
small reuse microbenchmark, not evidence of a 22% improvement on arbitrary ZK
circuits. The cache is retained, with an `ff.basis_cache=false` opt-out. It stores
at most four entries; each input and output is capped at 2,048 terms and 16,384
combined term/monomial/provenance units. Entries survive pop only because reuse
requires exact polynomial, field and premise-index equality; reset clears them.
The independent cache regression checks changed constraints and cores, resets,
and identical coefficient shapes over fields with different satisfiability.

## Final executable verification and retained changes

The final executable was rerun on all 328 selected inputs with the same
10-second/4 GiB/eight-worker protocol. Every status matches the primary native
routing variant: **216 UNSAT, 26 SAT, 86 timeouts**. All 26 final SAT models also
pass independent evaluation. The frozen baseline hit the memory limit on 112
selected inputs; the final executable hits it on none within the 10-second
window. The 86 remaining timeouts are still unresolved and may consume more
memory at longer limits.

The 12 symbolic Poseidon scaling cases (two/four permutations, free inputs,
partial inputs and equivalence, BN254/BLS12-381) remain **12/12** for both builds.
Three isolated fresh-process repetitions give a geometric-mean final/baseline
time ratio of **0.997**, with individual median ratios between 0.959 and 1.039.
This shows no material additional Poseidon speedup in this round. Every SAT
witness passes the independent R1CS evaluator.

Retained defaults are repeated bit propagation, native SMT routing, and bounded
exact basis reuse. The growth guard and LCM-degree pair ordering are removed.
F4, shared polynomial DAGs, and incremental extension of similar bases were not
implemented by these experiments. The remaining hard real circuits still need
further profiling and backend work.

The final binary SHA-256 is
`9876bedaa258cc3173f5307f584e0e66762baab5104c0ad1ba9b56106ab70f76`.
Raw measurements, exact inputs, experimental/final source snapshots, validation
outputs and reproduction instructions are in
[performance-round4](../tests/finite_field/results/performance-round4/README.md).

## Remaining cvc5 advantages

Joining the final Z3 results by exact input hash to the earlier cvc5 1.3.4
10-second results leaves **10 distinct inputs** solved by GB or split while
Z3 times out. The known incorrect split answer is excluded by the existing
adjudication. This is the updated selection, not a rerun of the whole corpus.

| Family | Selected inputs | Final Z3 | cvc5 GB | cvc5 split | Reference-only inputs (union) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Small-field algebra | 20 | 13 | 11 | 15 | 4 |
| Mixed BV/FF soundness | 40 | 15 | 18 | 5 | 3 |
| Arithmetic shifts | 32 | 31 | 0 | 32 | 1 |
| QED2 | 8 | 5 | 4 | 4 | 1 |
| Mixed translation validation | 16 | 13 | 11 | 10 | 1 |

The small-field gaps are four systems over F211. The soundness gaps are
`sound_bvashr_4`, `sound_bvudiv_3` and `sound_bvurem_3`; GB solves all three,
while split solves the first. Split also solves `deterministic_bvashr_64` and
`Num2Bits@bitify@circomlib_8`. GB solves one additional mixed CirC
translation-validation query. Higher aggregate coverage does not imply that
one solver's solved set contains the other's.

There are no remaining reference-only inputs in the selected CirC determinism
sample (Z3 and split both solve the same 42/64), sequential bit sums (both
100/100), or pure-field translation-validation sample. The other 545 CirC
determinism inputs have not been rerun with the final Z3, so the older full-family
coverage gap cannot yet be declared closed.

A new isolated check used three fresh-process repetitions of all three solvers
on three inputs with large apparent historical timing gaps. On
`i_13_8_4_system21.smt2`, medians are **0.2609 s for Z3, 0.0654 s for GB and
0.0220 s for split**: approximately 4x and 12x faster than Z3, respectively.
The large historical bit-sum timing gaps did not persist in isolation:
`bitsum_2_layers_5` takes 0.0251/0.0275/0.0366 s, and `bitsum_15_layers_1`
takes 0.0252 s for Z3 versus 0.0196 s for split (GB times out). Thus the
small-field speed gap is confirmed, while large speedup claims based on the
earlier concurrent bit-sum timings would be misleading.

Exact remaining cases are in `cvc5-remaining-gaps.json`; all 27 new isolated
timing runs are in `cvc5-timing-gaps.json` under the result directory. These
cvc5 performance results concern 1.3.4; the 1.4.0 correctness checks do not
constitute a full 1.4.0 performance comparison.

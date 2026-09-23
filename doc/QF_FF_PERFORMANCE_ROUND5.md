# QF_FF performance round 5: general algebra and mixed-theory search

## Scope and retained implementation

This round addresses small-field polynomial systems and mixed BV/field search.
There is no dispatch on benchmark names, exporter names, particular circuit
operators, or individual prime moduli.

- Native wire normalization records the transitive definitions actually used by
  each constraint. Bit propagation similarly retains the contributing equations,
  constant pins and Boolean-domain premises. These narrower explanations give
  SAT stronger conflict clauses without changing their logical justification.
- For primes below 2^32, `ff.batch=true` uses bounded F4-style symbolic
  preprocessing and sparse modular Gaussian elimination. Products of two
  canonical coefficients fit in uint64; larger fields retain arbitrary-precision
  polynomial reduction. Degree-ordered batches, the completed-pair chain
  criterion and basis autoreduction reduce duplicate work. Retiring a row always
  retains its remainder, preserving the generated ideal.
- `ff.sparse_witness=true` tries bounded univariate slices of underdetermined
  systems with at most twelve active variables. This phase gets at most roughly
  one sixteenth of the remaining algebra budget. Failed slices cannot establish
  UNSAT. Every accepted candidate is evaluated against all residual constraints,
  restored definitions and the original input.
- The valid lemma `x*x=x => x=0 or x=1` is available through
  `ff.boolean_split=true`, **off by default**. Its equality premise guards every
  clause. It can help SAT search substantially, but it can also hurt it.

The first two algebra options can be disabled independently. Their global
SMT-LIB spellings are `:smt.ff.batch` and `:smt.ff.sparse_witness`; the optional
split uses `:smt.ff.boolean_split`. Public-parameter regression tests check that
these controls actually reach the backend.

Mathematical justifications are included beside each transformation. Premise
sets are conflict explanations, not polynomial-combination certificates. Proof
reconstruction remains v2 work.

## Validation protocol and avoidance of benchmark-specific tuning

The baseline is the previous round's frozen executable
`9876bedaa258cc3173f5307f584e0e66762baab5104c0ad1ba9b56106ab70f76`.
The final executable is
`d16a97e31fe3ebe51b39bc5ef48ccc0dec77f2d6aac9e73b0f619cef83bc9765`.
Each primary run has a 10-second wall limit and 4-GiB memory limit. Eight workers
run fresh processes; builds, tests and model validation do not overlap timed
experiments. Unchanged baseline records are reused for final verification of the
328-input prior sample and the 212-input first validation sample. The final
108-input comparison measures both binaries afresh.

Seven known gaps were used for initial development. Before tuning, 212 additional
inputs were selected by hashing `generalization-round5:` plus their exact input
hash within each family, excluding the previous 328 inputs. Selection did not
use solver outcomes. This first holdout exposed regressions, so it subsequently
became validation data. Before the final policy change, a further **108 disjoint
inputs** were selected by hashing `confirmatory-round5:` plus the input hash:
20 Small, 40 CirC-S, 20 CirC-D, 12 TV, 12 TV-pureFF and four QED2. Their outcomes
were not used to tune the final implementation.

These are held-out inputs from public benchmark families, not evidence of
performance on every future ZK circuit or a completely new problem distribution.
The independent generated tests vary primes, widths, operators, scopes,
coefficients, equation shapes, and satisfiability.

## Final default results

| Sample | Inputs | Baseline | Final default | Gains / losses |
| --- | ---: | ---: | ---: | ---: |
| Prior selection | 328 | 242 | 245 | 3 / 0 |
| First validation sample | 212 | 127 | 131 | 4 / 0 |
| Fresh confirmation sample | 108 | 67 | 68 | 1 / 0 |
| **Total** | **648** | **436** | **444** | **8 / 0** |

All eight gains are from baseline timeouts: seven additional SAT answers and one
additional UNSAT answer. No definite answer disagrees between the two binaries.


| Family (all samples) | Inputs | Baseline | Final default |
| --- | ---: | ---: | ---: |
| ASHR | 32 | 31 | 31 |
| CirC-D | 124 | 97 | 97 |
| CirC-S | 140 | 42 | 42 |
| QED2 | 24 | 14 | 14 |
| Real | 8 | 3 | 3 |
| Seq | 100 | 100 | 100 |
| Small | 100 | 67 | 74 |
| TV | 48 | 42 | 43 |
| TV-pureFF | 72 | 40 | 40 |


## Rejected defaults and ablations

A global change to graded reverse lexicographic order was rejected: it turned a
roughly 40-ms QED2 instance into a timeout. Restoring the original order recovered
that input without losing the seven prototype gains in the prior sample.

Eager propagation of every normalized constant was also removed. It generated
many extra clauses and slowed the division/remainder development cases.

The Boolean-domain split prototype solved 249/328 prior inputs versus 242 for the
baseline, with seven gains and no losses. But the first holdout exposed three
mixed comparison regressions: baseline times of about 3.50, 0.69 and 0.70 seconds
became timeouts. Disabling this single heuristic restored all three. The default
therefore gives back some prototype gains rather than selecting behavior by
operator name, bit width, field prime, or benchmark identity.

With Boolean splitting enabled in both configurations, the first small-field
holdout ablation solved 43/60 with batching and 40/60 without it; the old baseline
solved 39/60. Batching is not uniformly faster: the development ablation includes
both speedups and slowdowns. The final-default tables above and the independent
confirmation are the acceptance results, not the more favorable prototype total.

Three fresh-process repetitions in isolation give these median seconds. These
are targeted examples of an improvement and a regression, not an aggregate
speedup estimate. The scalar variant disables batching on the final build.

| Input | Baseline | Final default | Batching disabled |
| --- | ---: | ---: | ---: |
| `i_13_8_4_system23.smt2` | 0.523 | 0.108 | 1.282 |
| `i_3_8_8_system19.smt2` | 0.613 | 1.590 | 0.400 |
| `i_13_8_4_system21.smt2` | 0.268 | 0.029 | 0.047 |


## Correctness checks and remaining limits

All 13 regression commands pass, including the C++ algebra tests and existing
preprocessing, combination, roots, incremental cache, API, model and artifact
harness tests. The new suite includes 225 random three-variable systems with
independently enumerated answers and unsat cores; 54 guarded-domain checks;
96 scalar/batched checks around the 32-bit arithmetic boundary and at a
cryptographic prime; 360 mixed BV/field checks across widths and operations; and
30 witness/failure-fallthrough checks. Both parameter settings are exercised.

Independent assertion evaluation validates **199 model-producing runs**
(96 baseline and 103 final-default SAT models), with zero failures. All twelve
symbolic Poseidon sentinels retain their answers; all sixteen associated SAT
models across the two binaries also validate. This is separate from solver
self-validation and is outside timed benchmark runs.

The three hard F211 UNSAT development systems remain unresolved at ten seconds.
Increasing only the diagnostic work budget still reached matrix-storage limits;
this round does not raise the default work or storage limits to fit those cases.
The small-field batch reducer is a bounded first implementation, not a claim of
full F4 performance parity. Scalable matrix storage and reducing redundant
symbolic preprocessing are remaining algebra work. Mixed-theory heuristics also
need broader portfolio research before eager domain splitting can be a safe
default. Arbitrary-precision batching and certificates are not implemented here.

Joining exact input hashes to the historical cvc5 1.3.4 GB/split results
(with the existing wrong-answer adjudication applied) gives no conflicting
definite answers on 640 comparable paper inputs. The union of the two cvc5
configurations still solves **21 inputs** missed by the final default, including
**8 in the original 328-input selection**. These are historical reference
measurements, not new cvc5 1.4.0 performance runs or a full-corpus parity claim.

Exact inputs, raw runs, model validation, source overlays, rejected experiments
and reproduction instructions are in
[performance-round5](../tests/finite_field/results/performance-round5/README.md).

# FMCAD 2026 proof artifact: reference results and first v2 coverage screen

## Reference pipeline and published results

The [paper](https://repositum.tuwien.at/handle/20.500.12708/230471)
provides an existing interoperability target: Alethe/Carcara delegates field
refutations through `ff_pac` to FFPacheck; Lean-SMT reconstructs CPC proofs.
This supports evaluating compatibility before expanding our experimental rules.

Table I reports the following at 1200 seconds and 16 GiB per problem:

| Published configuration | Completed / 403 |
| --- | ---: |
| cvc5 | 403 |
| cvc5, simplification disabled | 392 |
| cvc5 with proofs | 392 |
| cvc5 + proofs + Carcara/FFPacheck | 392 |
| Lean-SMT | 348 |

The published PDF is internally inconsistent: its introduction says 247 Lean
reconstructions, while Table I and the results discussion say 348. Its 403-input
count also differs from the artifact's 408-path selection. Neither discrepancy
has been adjudicated. These are reported figures, not reproduced results.

The [artifact README](https://zenodo.org/records/20133205) documents generated
results under `figures/408/table1_proof_checker_extensions.md`,
`table2_cumulative_times.md` and `cactus_all_benchmarks.{png,pdf}`. The ZIP's
README was retrieved by byte ranges and its member CRC verified. The full image
was not downloaded or executed in this screen; presence of precomputed raw
results inside it has not been established.

## Fresh Z3 measurement

On 2026-09-24, the current milestone-1 Z3 binary was run on every byte-distinct
input in `benchmark_set_FF_UNSAT_SMT`. The existing verified corpus contains
408 member paths and **390 distinct inputs**. Each input ran twice: once for ordinary
solving and once for the standalone certificate command.
The actual scheduling completed the certificate pass before the solver pass.
No formula was simplified or translated to fit the certificate profile.

Each run had a ten-second outer timeout, eight concurrent workers and a 4 GiB
sampled RSS cap. Certificate commands also had a 9.8-second internal timeout.
The Python 3.14 supervised benchmark runner isolated/reaped each process;
all 780 runs completed without an infrastructure failure.

| Current Z3 mode | UNSAT answers | Checked certificates | Other outcomes |
| --- | ---: | ---: | --- |
| Ordinary solver | **382 / 390** | Not requested | 8 timeouts |
| Standalone `ff-certify` | Not a solver-status query | **0 / 390** | 390 explicitly unsupported |

All ordinary answers agree with the artifact's UNSAT selection, but they are
not certified by this milestone. Counting duplicate member paths would give
400/408 ordinary solves; those are not 408 independent runs. This is not a
same-machine, same-budget comparison against the paper's proof pipeline.
No fresh cvc5, Carcara, FFPacheck or Lean runs are claimed.

The certificate command consistently rejects the input before algebraic
reconstruction: it supports only conjunctions of positive field equalities.
The 390 selected inputs all contain negation; 211 also declare Boolean variables
and use ITEs and disjunction. All declare QF_FF; this subset contains no BitVec
sorts. Lexical occurrence counts identify input features, not a proof that every
occurrence must survive normalization.

The separate Python checker audit gives 135 positive-equality-scope rejections,
185 declaration/sort-profile rejections and 70 nesting-limit rejections. Those
are first encountered errors, not mutually exclusive semantic classifications.
The subsequent actual Z3 command runs establish the producer's 390 unsupported
results independently of those checker parser limits.

## Implications for v2

The artifact is already in our historical solver corpus; the new measurement
is certificate coverage. The current result identifies an interface/proof-scope
gap, not 390 failed polynomial contradiction searches.

The next concrete milestone should cover original negated field equalities and
Boolean structure, with checked inverse-witness introductions and exact theory
lemma premises. Normalize and handle shared expression DAGs without requiring
unchecked input rewriting. Extend the independent checker's input profile with
those rules. Then repeat this entire fixed selection and classify failures into
unsupported proof features, algebra/resource limits and checker failures.

In parallel design work, map our existing addition/multiplication DAG evidence
to the artifact's PAC interface. Test the actual artifact checker before
claiming format compatibility. Complete SMT proofs must also justify their
Boolean and preprocessing steps. Root certificates remain required for cases
that cannot be refuted by ideal membership alone.

## Evidence and reproduction

Local evidence: `tests/finite_field/results/fmcad-proof-screen-v2/` (ignored by git).
It contains `run.py`, `selection.json`, `metadata.json`, `runs.jsonl`,
`checker-profile.json`, `summary.json`, the CRC-verified artifact README,
ZIP header extraction details and the final published PDF/text. The script
retains its original absolute input/output paths as an exact run record; edit
`ROOT` and `OUT` to relocate it. It uses the tracked `benchmark_artifacts.py`
runner and the current `scripts/ff_certificate.py` checker. Binary identity is
recorded by SHA256; the measured source is `bb05aa376` with unchanged solver code.

The eight timeouts all come from deterministic `zokref` instances. Their exact
member names and hashes are preserved in `runs.jsonl`; no timeout is silently
removed from the denominator.

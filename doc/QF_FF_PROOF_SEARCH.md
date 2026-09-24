# Bounded proof-search improvements: fourth v2 milestone

The standalone artifact-format pipeline certifies **355/390** distinct original
FMCAD inputs within ten seconds per input, up from **340/390**. All 340 prior
successes are retained: ten additional soundness cases and five additional
determinism cases now have complete, independently checked proofs. This is
proof-pipeline coverage, not an updated CVC5 solver comparison.

## Changes retained

- **Reuse proved Boolean conflicts.** Conflict analysis and branch resolution
  already produced globally valid clauses. These clauses now participate in
  later propagation, including subsequent field-lemma iterations. Each still
  has explicit resolution evidence; no branch assumption becomes an axiom.
- **Bounded alternative polynomial ordering.** Keep the original input order
  first. If reconstruction exhausts a bound, discard that attempt and try
  increasing polynomial degree, then sparsity, with stable input-index ties.
  Input proof nodes retain their original premise indices. Both attempts share
  the same arithmetic engine, consumed work and cancellation state. The
  2M-operation default, 256-row basis cap, term, DAG and time bounds remain.
  An exhausted operation budget cannot be reset by the retry.
- **Reduce subprocess waiting overhead.** Wait up to 20 ms for a child, returning
  early on completion, instead of unconditionally sleeping 20 ms after every
  poll. Output checks, deadlines and process-group cleanup remain in place.

The proof formats, independent verifiers, external checker pins and required
input-binding guard are unchanged. These changes affect standalone proof
production; they do not alter normal Z3 solving or add native `get-proof`,
root-completion, theory-combination or Lean certificates.

## Fixed-corpus results

The selection is unchanged: 408 artifact member paths, deduplicated to 390
original SMT2 inputs. Four workers, ten seconds of **whole-pipeline wall time**
per input, including front end, production, independent replay, FFPacheck and
Carcara. There is no process-wide memory cap.

| Outcome | Previous | Current |
|---|---:|---:|
| Complete original-input proofs checked | 340 | **355** |
| Bounded polynomial reconstruction unavailable | 22 | 17 |
| Boolean search work limit | 28 | 16 |
| Whole-pipeline timeout during production | 0 | 2 |
| Front-end / independent / external rejection | 0 | 0 |

The current successes comprise **193 soundness** and **162 determinism** inputs,
with **2,689** checked field lemmas. Median Alethe size is 177,993 bytes; maximum
is 13,969,177 bytes.

For the same 340 previously certified inputs, median pipeline time changed from
**0.354 s to 0.158 s**; the median paired current/previous time ratio is **0.584**.
Across all 355 current successes, median time is **0.167 s** and maximum is
**9.137 s**. These are concurrent screening measurements, not repeated isolated
solver timings. They include subprocess waiting overhead; they do not establish
an equivalent speedup in polynomial arithmetic. Regression suites ran briefly
alongside the beginning of the final screen.

## Alternatives measured and rejected

On the 28 prior Boolean failures, clause learning plus responsive waiting
certified ten inputs. A watched-literal prototype certified exactly the same
ten; the other outcomes shifted from 17 work-limit exits and one timeout to
three work-limit exits and 15 timeouts. This does not justify its additional
machinery, so it is excluded.

Always using the new polynomial order gained five of the 22 polynomial failures,
but a full-corpus screen lost two old successes. The retained original-first
fallback recovers both and preserves all five gains. There are no corpus-name,
field-size or circuit-family selectors. An early targeted run with fixed sleeps
encountered a process-cleanup permission error; it is excluded from comparisons.

## Validation and reproduction

Validation passes include the finite-field C++ suite, 96 independently checked
DAG/Alethe pairs, 144 exhaustively adjudicated polynomial systems, 575 Boolean
search checks against exhaustive assignments with independent resolution replay,
30 externally checked Boolean/ITE proofs and 29 externally checked literal
proofs. Existing corruption, unsupported-input and deadline tests pass.
New tests cover repeated search after added constraints, premise permutations,
a basis-cap fallback, unchanged output on failure, and retention of consumed
work across the fallback.

```sh
python3 tests/finite_field/benchmark_ff_proof_pipeline.py \
  --manifest tests/finite_field/results/paper-artifacts/manifest.json \
  --corpus tests/finite_field/results/paper-artifacts/corpus.zip \
  --out /tmp/ff-proof-search-reproduction \
  --z3 build-ff-cmake/z3 --carcara "$CARCARA" --ffpacheck "$FFPACHECK" \
  --timeout 10 --jobs 4
```

The local archive `tests/finite_field/results/fmcad-proof-search-v2/` contains
original inputs, proof bundles, checker logs, raw outcomes, binary/script hashes,
`analysis.json` with every gained input and the empty loss set, and `experiments/`
with exploratory outcomes and source snapshots. The baseline is
`fmcad-proof-boolean-v2/`. Checker setup and the required local FFPacheck patch
remain documented in `tests/finite_field/proof_checkers/README.md`.

The remaining 35 inputs split into 17 polynomial-budget cases and 18 Boolean
search/deadline cases. Diagnostics identify the 256-row basis cap in many fast
polynomial failures. The next polynomial direction is proof-preserving linear
elimination and basis storage reduction; the Boolean direction is stronger
branching/conflict analysis under the current bounds. CPC/Lean reconstruction
and finite-field root evidence remain separate work.

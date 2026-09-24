# Native comparison with the FMCAD 2026 proof candidate

## Scope

This campaign reruns the [public artifact](https://zenodo.org/records/20133205)
for [Proof Production for Satisfiability Modulo Finite Fields with Proof
Checking in Pacheck and Lean](https://hanielbarbosa.com/papers/2026fmcad-ffproofs.pdf),
excluding Lean-SMT. It compares ordinary solving, proof generation and external
proof checking separately. The tables and figures below are fresh local
measurements, not the paper's published timings.

The artifact's `benchmark_set_FF_UNSAT_SMT` lists **408 paths**. Its set exactly
matches the existing verified corpus manifest. Byte-identical inputs are run
once, giving **390 distinct inputs**; path-weighted counts are reported too.
The paper reports 403 inputs. The missing correspondence to that 403-input
selection remains unresolved; no cases are silently removed to match it.

## Candidate and baseline provenance

The artifact's proof-producing CVC5 contains four finite-field source changes
beyond public branch `psaccomani15/cvc5` at
`fd1eaa1782824b29b079efd70c2a1a3f48cc706a`. The native build applies those exact
artifact files. All other non-generated files under `src`, `include` and `cmake`
match; the source-file hash manifest and four-file overlay are archived. This
is the artifact candidate's code, not merely the current public branch.

The build uses production optimization, static linking, GMP and the artifact's
pinned CoCoALib 0.99800. It targets native macOS arm64. The unrelated libpoly
backend is disabled because its nested build selected an incompatible macOS
SDK; no finite-field algorithm was changed for this port. The Linux image
binary is not executed under emulation.

The artifact's ordinary and no-simplification wrappers actually invoke the
`clean-wip` release of the author's fork through the bundled `lean-cvc5`
package. Its pinned package revision is
`e18693d477b9af96221463cf05c417c1ef36caf3`; its release binary identifies itself
as `1.3.3.dev+clean_WIP@b1f8abb`. Both configurations are measured using that
release's native arm64 binary, without running Lean.

Official CVC5 **1.3.3** (`8ff882e`), **1.4.0** (`b432cd7`), and pinned main
**72f647eb75c0241d82bc24ecf1f4092ff0f683f7** provide additional version context.
GB and split are measured for all three; simplification-disabled modes are
also measured for both releases. The proof candidate is additionally measured
with and without simplification but without producing proofs, to help separate
its own solving behavior from its proof overhead. Official release binaries
use CLN; our candidate/main builds use GMP. Compiler/build differences mean
this is a comparison of pinned executables, not an isolated causal estimate
of a version change.

## Protocol and checking contract

Every configuration receives the exact original SMT2 bytes. The primary
13-configuration campaign is shuffled deterministically and uses four workers.
The two exact `clean-wip` baseline modes run afterward, also with four workers.
Each fresh worker receives **10 seconds total wall time**, including startup,
production, independent replay when applicable, and external checking. Worker
and descendant RSS is sampled every 50 ms against **16 GiB**; this is a sampled
limit, not a hard allocation cap. The host is an **Apple M2 Max**, 12 logical CPUs and 64 GiB RAM, running
macOS 26.6.2. Python **3.14.2** is used throughout. All
provisional setup runs, including a system-Python-3.9 run, are excluded.

CVC5 proof production follows the artifact settings:
`--simplification=none --produce-proofs --proof-format-mode=alethe
--proof-granularity=dsl-rewrite --ff-proof-pac --dump-proofs`.
Carcara expands lets, reads the artifact's identical `rewrites.eo`, allows
integer/real subtyping, and delegates PAC steps to FFPacheck. The runner rejects
holes and requires a successful exit and `valid`. It does not allow unknown
rules. Generated proof text and checker output are retained.

Carcara's 73 core source files and five CLI source files match the artifact.
FFPacheck is the artifact source with the existing
`tests/finite_field/proof_checkers/ffpacheck-completion.patch`, applied equally
to both proof pipelines. This intentionally tightens incomplete-proof handling.
The known Carcara PAC-premise binding limitation still applies: candidate rows
mean acceptance by that external checker pipeline. Z3 additionally performs its
mandatory original-input binding, polynomial and Boolean replay. These are
explicitly different checking contracts; no proof holes are counted as success.

The paper's published comparison used 1200 seconds on Linux/x86-64. This is a
matched native **10-second screen**, not a reproduction of those absolute
numbers or of its 20-minute resource budget. Generation-only results are the
recorded successful production stages of the same runs. A successful UNSAT
answer without a proof is never counted as a checked certificate.

## Results

The completed campaign contains **5,850 measurements** (15 configurations ×
390 inputs). The two generation-only rows are derived stages of the proof
runs, not additional measurements. For solver modes, success means UNSAT; for
proof modes it means a checked proof. No SAT disagreement, checker rejection,
process error or memory-limit result occurred.

| Configuration | Success / 390 | Weighted / 408 | Median successful time |
|---|---:|---:|---:|
| cvc5-1.3.3-gb | 357 | 375 | 0.150 s |
| cvc5-1.3.3-nosimp | 369 | 387 | 0.158 s |
| cvc5-1.3.3-split | 322 | 340 | 0.203 s |
| cvc5-1.4.0-gb | 356 | 374 | 0.183 s |
| cvc5-1.4.0-nosimp | 366 | 384 | 0.138 s |
| cvc5-1.4.0-split | 322 | 340 | 0.200 s |
| cvc5-main-72f647e-gb | 363 | 381 | 0.140 s |
| cvc5-main-72f647e-split | 331 | 349 | 0.150 s |
| z3-ff-solve | 380 | 398 | 0.133 s |
| z3-ff-proof | 351 | 369 | 0.397 s |
| paper-candidate-gb | 347 | 365 | 0.219 s |
| paper-candidate-nosimp | 366 | 384 | 0.151 s |
| paper-candidate-proof | 358 | 376 | 0.310 s |
| artifact-clean-wip-gb | 342 | 360 | 0.141 s |
| artifact-clean-wip-nosimp | 364 | 382 | 0.143 s |
| z3-ff-proof-generation | 354 | 372 | 0.235 s |
| paper-candidate-proof-generation | 360 | 378 | 0.200 s |


The paper candidate checks **358/390**, versus **351/390** for Z3+FF. They
share **338** successes; **20** are candidate-only, **13** Z3-only, and **19**
are checked by neither pipeline. On those same 338 inputs, cumulative pipeline
time is **185.726 s** for the candidate and **291.157 s** for Z3 (1.57× as much
wall time). Paired-set medians are 0.294 s and 0.401 s respectively. These figures
include our extra independent replay in Z3's checking contract.

Ordinary Z3 solves **380/390**, ahead of every measured CVC5 configuration in
this screen; the best measured CVC5 solver coverage is **369/390**, from 1.3.3
with simplification disabled. This does not imply superior certificate coverage:
the candidate currently leads there. Nor does it establish that one release is
intrinsically faster than another under their different build environments.

The candidate produces 360 proofs, of which two exceed the overall deadline
while checking. Z3 produces 354 certificates, of which three exceed the deadline
while checking; 28 other runs report a bounded production failure and 11 reach
the outer timeout. All 28 unavailable receipts are production-stage failures,
not suppressed checker rejections.

The most visible category gaps are CirC soundness (**47 candidate vs 39 Z3
checked**) and ZoKrates/CirC determinism (**58 vs 51**). Z3 leads on CirC
determinism (**47 vs 43**) and ZoKrates/ref determinism (**64 vs 57**). The
interactive [per-input explorer](../tests/finite_field/results/fmcad-cvc5-comparison-20260924/explorer.html)
filters any two configurations by compiler, property and exclusive successes.
The [complete CSV](../tests/finite_field/results/fmcad-cvc5-comparison-20260924/per-input.csv)
retains every status and failure reason.

### What the missed proofs suggest

Among the 20 candidate-only proofs, Z3 has nine polynomial-certificate budget
failures, five Boolean search work-limit failures, and six timeout-related
failures (including three reported within the production pipeline).

Eight candidate-only cases close with finite-field simplification and Boolean
rules **without any `ff_pac` lemma**. This points to proof-aware normalization
and Boolean preprocessing as a concrete next investigation. The other twelve
candidate proofs use PAC axioms and linear combinations; none uses a PAC root
rule. Root-certificate support therefore does not explain this particular
20-case coverage gap. This is a profile of the accepted candidate proofs, not a
claim that those proof shapes are the only possible solutions.

Several Boolean work-limit cases have 264–768 candidate `ff_pac` lemmas.
Our default certificate pipeline bounds field lemmas at 256; this motivates
studying Boolean proof search and lemma reuse, rather than assuming polynomial
arithmetic alone is responsible. The candidate's lemma count is not a lower
bound on what Z3 must produce. All per-case rule counts are in `summary.json`.

Four inputs checked in the earlier 355/390 screen timed out in this concurrent
campaign. With the same binary and source, isolated follow-ups under this
supervisor checked all four in **3.49, 4.05, 3.78 and 5.58 seconds**. They remain
failures in the primary table. These separate receipts are stored under
`diagnostics/serial-timeouts/` and `diagnostics/serial-timeouts.json`; they show
timing sensitivity under this execution protocol, not a demonstrated code
regression. Repeated isolated measurements would be needed for stable close
performance claims.

### Common-set overhead, excluding Lean-SMT

The paper-style cumulative calculation must use the same successful inputs in
every row. Recomputed on all four artifact modes, the shared set has 330 inputs.
Adding Z3's three modes yields 313 inputs. The second comparison is below; the
[first comparison and exact common sets](../tests/finite_field/results/fmcad-cvc5-comparison-20260924/common-times.md)
are archived alongside it.

| Configuration | Cumulative time | Relative to artifact no-simplification |
|---|---:|---:|
| artifact-clean-wip-gb | 155.029 s | 2.16x |
| artifact-clean-wip-nosimp | 71.707 s | 1.00x |
| paper-candidate-proof-generation | 111.824 s | 1.56x |
| paper-candidate-proof | 165.556 s | 2.31x |
| z3-ff-solve | 73.286 s | 1.02x |
| z3-ff-proof-generation | 160.720 s | 2.24x |
| z3-ff-proof | 258.514 s | 3.61x |


![Cactus plot](../tests/finite_field/results/fmcad-cvc5-comparison-20260924/cactus.png)

![Coverage by category](../tests/finite_field/results/fmcad-cvc5-comparison-20260924/categories.png)

![Checked-proof timing comparison](../tests/finite_field/results/fmcad-cvc5-comparison-20260924/proof-scatter.png)

The timing graphs include process startup and supervision. They are concurrent
screening measurements, not repeated isolated timings. Compare cumulative
times and paired times on the common-success set; medians from different solved
subsets alone are not speedup estimates.

## Evidence and reproduction

The primary archive is
`tests/finite_field/results/fmcad-cvc5-comparison-20260924/`;
the two artifact baseline modes are in the sibling directory
`fmcad-cvc5-comparison-20260924-artifact-baselines/`.
They contain `metadata.json`, exact selections, durable `runs.jsonl`, original
inputs, stage outputs, per-input receipts and proof files. The primary archive
also contains `summary.json`, `per-input.csv`, the figures, native binaries,
source hashes, source-overlay patch, wrapper scripts and release provenance.
The complete SHA-256-verified public artifact ZIP is archived in `provenance/`.
The bulky result directory is intentionally ignored by Git; the report and
reproduction tools are versioned, while raw evidence remains in this workspace.
`summary.json` lists every proof-coverage difference by input hash and name.

Use Python 3.14 with `psutil` for the benchmark and `matplotlib` for figures.
Configuration JSON is an array of objects with `id`, `kind` (`solve`,
`cvc5-proof`, or `z3-proof`), `command`, and optional `checker_args`. Paths in
archived configurations identify the measured executables; adjust them when
relocating. Binary hashes and the exact argument vectors are preserved.

```sh
python3.14 tests/finite_field/test_ff_paper_runner.py
python3.14 tests/finite_field/benchmark_ff_paper.py \
  --manifest tests/finite_field/results/paper-artifacts/manifest.json \
  --corpus tests/finite_field/results/paper-artifacts/corpus.zip \
  --config comparison.json --out /tmp/ff-paper-comparison \
  --carcara /path/to/carcara --ffpacheck /path/to/ffpacheck \
  --timeout 10 --jobs 4 --memory-mib 16384
```

Repeat with the archived `clean-wip.json` configuration in a second output
directory, then run:

```sh
python3.14 tests/finite_field/analyze_ff_paper.py /tmp/ff-paper-comparison \
  --extra /tmp/ff-paper-artifact-baselines
```

The supervisor regressions cover successful/wrong answers, nonzero exits,
timeouts including descendants that start separate sessions, memory exhaustion,
and rejection of stale success receipts. A full rerun with a longer budget is
selected by `--timeout`; no implementation or dataset change is required.

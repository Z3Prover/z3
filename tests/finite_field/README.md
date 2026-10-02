# Finite-field regression tests

The solver tree keeps regression tests and their small, licensed fixtures.
Corpus acquisition, benchmark campaigns, paper sources, figures and experiment
reports are preserved separately. Existing evidence remains available in the
[immutable published snapshot](https://github.com/RSoulatIOHK/z3/tree/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/tests/finite_field).

## Run the acceptance checks

Python 3.12+, Linux or macOS, and a CMake build are required. The runner uses
that build's Python package and verifies shared-library identity before running
any suite; an installed Z3 cannot accidentally satisfy these tests.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_PYTHON_BINDINGS=ON
cmake --build build --target z3 test-z3 test-ff-api libz3 build_z3_python_bindings --parallel 2
python3 tests/finite_field/run_tests.py --build build --suite core --out /tmp/ff-core
```

The core selection runs **19 Python suites**, six native groups (`finite_field`,
`ast`, `smt_context`, `smt2print_parse`, `api`, `arith_rewriter`), and the public
C++ API smoke test. The smoke target keeps assertions enabled in Release builds.
Coverage includes exhaustive small-field oracles, SAT models and UNSAT cores,
generic equality rewriting, global/local options, mixed theories, translated
contexts, scopes, cancellation, fallback recovery, F4 and scalar backends.

Certificate validation is a separate explicit selection:

```sh
python3 tests/finite_field/proof_checkers/build.py --out /tmp/ff-checkers
python3 tests/finite_field/run_tests.py --build build --suite proofs \
  --carcara /tmp/ff-checkers/carcara --ffpacheck /tmp/ff-checkers/ffpacheck \
  --out /tmp/ff-proofs
```

The builder verifies the pinned source archive and patch checksums before
building with Cargo/CMake. It requires Rust and GMP; on macOS pass
`--cmake-arg=-DCMAKE_PREFIX_PATH=/opt/homebrew` and, if necessary,
`--cmake-arg=-DCMAKE_CXX_FLAGS=-I/opt/homebrew/include`. Existing local archives
can be supplied with `--archives DIR` (`carcara.tar.gz`, `ffpacheck.tar.gz`).
See [the checker trust boundary](proof_checkers/README.md) for required input
binding and why raw external-checker acceptance alone is insufficient.

Proof suites exercise independent DAG/Alethe replay, original-input binding,
external literal and Boolean pipelines, tampered/truncated/wrong-input rejection,
and resource recovery. Missing checkers are an error, not a skipped pass.
Use `--suite all` to combine core and proof selections.

Every invocation requires a new output directory and writes per-suite logs plus
`summary.json`, including commands, statuses, timings and the selected build.
Failures, missing prerequisites and timeouts return a nonzero exit code.
`--jobs` defaults to two and `--timeout` to 300 seconds per suite; timeout stops
the suite's process group, including child solver processes. The CI workflow
runs both selections on Ubuntu Release builds for pull requests and saves the
logs even on failure. `test_ff_runner.py` checks failure handling separately.
These are correctness regressions; the timed public-corpus comparisons remain
separate from CI acceptance and are not silently refreshed by a test run.

The other `test_ff_*.py` files exercise individual algebra, preprocessing,
resource, incremental and certificate features. CLI-based suites accept `--z3`;
external proof tests additionally require the checkers documented in
[proof_checkers/README.md](proof_checkers/README.md). Independent Python proof
checkers intentionally do not share the C++ arithmetic/translation implementation.
`benchmark_qfff.py` remains a small generated benchmark harness; measured public
corpus comparisons and their provenance belong to the research archive.

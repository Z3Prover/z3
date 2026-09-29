# Finite-field regression tests

The solver tree keeps regression tests and their small, licensed fixtures.
Corpus acquisition, benchmark campaigns, paper sources, figures and experiment
reports are preserved separately. Existing evidence remains available in the
[immutable published snapshot](https://github.com/RSoulatIOHK/z3/tree/0a5210c9009ba5595521c39cefa7ef0a7b1d46aa/tests/finite_field).

Build the CLI, native tests and Python bindings (replace `build` as needed):

```sh
cmake --build build --target z3 test-z3 libz3 build_z3_python_bindings
build/test-z3 finite_field
export PYTHONPATH="$PWD/build/python"
export Z3_LIBRARY_PATH="$PWD/build"
python3 tests/finite_field/test_ff_integration.py --z3 build/z3
python3 tests/finite_field/test_qfff.py --z3 build/z3
python3 tests/finite_field/test_ff_combination.py
python3 tests/finite_field/test_ff_large_combination.py
python3 tests/finite_field/test_ff_simplify.py
```

The other `test_ff_*.py` files exercise individual algebra, preprocessing,
resource, incremental and certificate features. CLI-based suites accept `--z3`;
external proof tests additionally require the checkers documented in
[proof_checkers/README.md](proof_checkers/README.md). Independent Python proof
checkers intentionally do not share the C++ arithmetic/translation implementation.
`benchmark_qfff.py` remains a small generated benchmark harness; measured public
corpus comparisons and their provenance belong to the research archive.

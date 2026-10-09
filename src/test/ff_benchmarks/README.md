# QF_FF benchmark corpus (CAV'23 "Satisfiability Modulo Finite Fields")

This directory contains the finite-field-theory-tagged SMT-LIB2 benchmarks from
the public artifact accompanying:

> Alex Ozdemir, Gereon Kremer, Cesare Tinelli, Clark Barrett,
> "Satisfiability Modulo Finite Fields", CAV 2023.
> https://eprint.iacr.org/2023/091

Source archive: `cav23-artifact-ff-init.zip`, Zenodo record
https://doi.org/10.5281/zenodo.7864537 (open access, CC-BY-4.0).

The archive's `docker/benchmarks/benchmarks/` directory contains 4,770 `.smt2`
files in four theory encodings used for the paper's solver comparison:
`ff` (1602 files), `pureff` (864 files), `bv` (1440 files), `nia` (864 files).
This directory keeps only the `ff`- and `pureff`-tagged files (2,466 total,
~66 MB) — these are the native finite-field encodings directly usable with
Z3's `QF_FF`/`FiniteField` theory. The `bv`/`nia` files encode the *same*
problems into bit-vector/non-linear-integer-arithmetic theories for comparison
with other solvers and are not applicable here.

Retrieved: 2026-10-09, via range/central-directory extraction (no local
docker/zenodo tooling required — see the PR discussion for context). Files
are unmodified copies of the archive's SMT-LIB2 benchmark inputs; filenames
encode the original generation parameters (compiler sweep, variable/term
counts, field bit-width, determinism mode).

This is a manually curated download, not yet wired into any CMake/CTest
target or CI workflow — see follow-up work for turning this into an
automated regression/performance suite (e.g. running `z3 -in` over each file
with a timeout and comparing against expected results, as approximated by
`z3test`'s `benchmark_qfff.py`).

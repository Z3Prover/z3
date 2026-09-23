# Real-project ZK circuit benchmarks

Source: [Veridise/Picus](https://github.com/Veridise/Picus), commit
`138b151d3a388e5b6c040c163e0a1db04f2ceda6` (2024 corpus snapshot).
The source manifest records every included Circom file's SHA-256.
These are the versions distributed by Picus, including its `-fixed` variants,
not claims about current deployed versions of the original projects.

## Contents

* `picus/pure`, `picus/int`, `picus/fixed-int`, `picus/src`: verbatim gnark
  Plonky2 verifier SR1CS exports and their Go wrappers from Picus. The measured
  primary suite uses **only the three `pure` exports**. The six integer/range
  variants are preserved for future experiments, not counted as measured cases.
* `circom-sources.zip`: the five application entry points and all 33 transitively
  included source files, preserving their paths, plus Picus's license and test
  expectations. Original notices in included libraries are preserved.
* `compiled-r1cs.zip`: R1CS binaries, symbol maps, and compiler logs for the five
  Circom entry points. Whitelist compiled with 888 constraints / 891 wires;
  the remaining counts are in `picus/circom/*.json`.
* `picus/circom`: exact textual transcriptions of those R1CS equations. Coefficient
  values and wire identities are retained. These are generated inputs, unlike
  the verbatim gnark SR1CS files.
* `nonvacuity-witnesses.zip`: two original witness files and their inputs, plus
  the compiler-generated witness helper scripts. They establish that the two
  circuits whose determinism Z3 proves have at least one valid execution.

## Reproduction

Unpack `circom-sources.zip` into a fresh directory. Install `circom2@0.2.23`
in a temporary prefix (`npm install --ignore-scripts --no-audit --no-fund`).
Its bundled compiler reports **Circom 2.2.3**; the WASM hash is in
`source-manifest.json`. With the unpacked source root as working directory,
compile each entry point in that manifest using:

```sh
/path/to/node_modules/.bin/circom2 benchmarks/PATH.circom --r1cs --sym --O0 -o /path/to/output
```

No source changes are required. Picus itself defaults to `--O0`; we use the
same optimization level. Missing pragma warnings are retained in compiler logs.
The compiler version is newer than Picus's documented minimum, so these are
new compilations of its published circuits, not byte-identical historical jobs.

Convert each `.r1cs` with `tests/finite_field/import_real_circuits.py INPUT OUTPUT`.
The five output names used here are `darkforest-whitelist`, `darkforest-move`,
`hermez-compute-fee`, `maci-merkle-inclusion`, and `maci-signature`.
The importer checks the section structure, coefficients, wire bounds, and
constraint counts. It rejects custom-gate files.

From the Z3 repository, using Python **3.14 or later**:

```sh
python3.14 tests/finite_field/benchmark_real_circuits.py \
  --z3 /path/to/z3 --cvc5 /path/to/cvc5 \
  --group pure --timeout 10 --out /path/to/new-pure-results
python3.14 tests/finite_field/benchmark_real_circuits.py \
  --z3 /path/to/z3 --cvc5 /path/to/cvc5 \
  --group circom --timeout 10 --out /path/to/new-circom-results
python3.14 -m unittest discover -s tests/finite_field -p test_real_circuit_import.py -v
```

Use the CoCoA-enabled cvc5 build. Solver executable hashes, versions, commands,
platform, limits, and generated input hashes are retained beside each run log.
`--case SUBSTRING` and `--solvers z3 cvc5 cvc5_split` allow selected follow-ups;
`--repetitions 3` records separate fresh-process runs. Each new configuration
must use a new results directory. No solver source changes were made in this task.

The translator copies all constraints twice, fixes wire 0 to one, equates all
top-level inputs (public and private), and asks for differing top-level outputs.
SAT exhibits non-determinism; UNSAT establishes output determinism. This does
not test full security, equivalence to a functional specification, or proving
speed. It does not reproduce Picus's inference, decomposition, or selective SMT
strategy, and historical Picus statuses are not used as solver ground truth.

For optional `--group ranged`, the strict canonical integer bound `x < B` is
encoded with Boolean field digits, non-wrapping binary reconstruction, and an
exact lexicographic bound. This changes the encoding from Picus's integer
backend; those optional cases are excluded from the reported comparison.

For the nonvacuity check, unpack the witness archive and run:

```sh
python3.14 tests/finite_field/validate_real_circuit_witness.py \
  tests/finite_field/fixtures/real-circuits/picus/circom/darkforest-whitelist.sr1cs \
  /path/to/whitelist.wtns --out /path/to/check.json
```

The same command with `maci-merkle-inclusion.sr1cs` and
`merkleTreeInclusionProof_test.wtns` checks the Merkle case. To regenerate the
witnesses, compile those same entry points with `--wasm --O0` and invoke the
compiler's `generate_witness.js` with the preserved input JSON. The checker
evaluates every R1CS equation modulo BN254 independently of either SMT solver.
This is not an UNSAT certificate; proof reconstruction remains v2.

## Source-tree packaging

The branch tracks this guide and the source manifest. Large downloaded Picus
exports, compiled circuits, and witness archives remain local benchmark data
and are excluded from the source commits. The named files above describe the
local evidence bundle, not files present in a fresh source checkout. Obtain
the pinned public Picus sources and compile using the steps above when
reconstructing those application benchmarks. Correctness tests use small
self-contained importer examples and do not require the application downloads.

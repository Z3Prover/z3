# Real-project ZK circuit comparison

We benchmarked eight output-determinism queries from four real ZK projects.
At **10 seconds and 4 GiB per process**, the Z3 FF branch solves **2/8**;
cvc5 1.3.4 GB and split each solve **0/8**. This is a small, deliberately
selected diagnostic set, not a representative estimate of production coverage.

## What these circuits are

The inputs come from [Veridise's public Picus suite](https://github.com/Veridise/Picus/tree/138b151d3a388e5b6c040c163e0a1db04f2ceda6/benchmarks):

* **Dark Forest:** the whitelist circuit and the full published movement circuit
  in the `darkforest-eth-9033eaf-fixed` snapshot.
* **Hermez:** its transaction-fee computation circuit from `hermez-network-9a696e3-fixed`.
* **MACI:** depth-4 Merkle inclusion and seven-message-element signature
  verification from `maci-9b1b1a6-fixed`.
* **Succinct's gnark Plonky2 verifier:** Goldilocks inverse, multiply-add,
  and reduction subcircuits, distributed as native-field SR1CS by Picus.
  The [upstream project](https://github.com/succinctlabs/gnark-plonky2-verifier)
  implements a Plonky2 verifier in gnark. These three cases are its arithmetic
  building blocks, not a complete recursive verifier.

Picus uses cvc5 as a backend and combines it with circuit-specific reasoning.
Its [application tests](https://github.com/Veridise/Picus/tree/138b151d3a388e5b6c040c163e0a1db04f2ceda6/tests)
include these cases. We run the same newly generated monolithic SMT query on
each solver, rather than timing the full Picus pipeline or claiming to reproduce
its historical times. The corpus contains patched (`-fixed`) versions; these
are published verification examples, not assertions about current deployments.

There is another relevant public project: [Quantstamp's Halo2 analyzer](https://github.com/quantstamp/halo2-analyzer)
uses cvc5 finite fields. Its [technical report](https://forum.zcashcommunity.com/uploads/short-url/3rGuQSM2LKVIwSzbv8Mh4C6Pzzp.pdf)
includes zkEVM gadget experiments. Those Halo2 experiments have **not** been
run in this comparison; recreating their extraction pipeline is separate work.

## Primary results

Times include solver startup, parsing, solving, and shutdown. Each row is one
fresh-process measurement; repeat measurements for successful Z3 cases follow
below. Constraint counts are for one original circuit; the determinism query
contains two copies plus input equalities and an output disequality.

| Circuit | R1CS constraints | Z3 FF | cvc5 GB | cvc5 split |
| --- | ---: | --- | --- | --- |
| Dark Forest whitelist | 888 | UNSAT, 0.318 s | timeout | timeout |
| Dark Forest movement | 33,269 | timeout | memory limit, 6.521 s | timeout |
| Hermez fee computation | 1,588 | timeout | timeout | timeout |
| MACI Merkle inclusion, depth 4 | 3,114 | UNSAT, 2.488 s | memory limit, 3.664 s | memory limit, 2.742 s |
| MACI signature verification | 25,516 | timeout | memory limit, 5.036 s | memory limit, 7.889 s |
| Plonky2 Goldilocks inverse | 93 | timeout | timeout | timeout |
| Plonky2 Goldilocks multiply-add | 68 | timeout | timeout | timeout |
| Plonky2 Goldilocks reduction | 78 | timeout | timeout | timeout |

All circuits use the **254-bit BN254 scalar field**. In the Plonky2 cases,
Goldilocks arithmetic is represented by constraints over BN254; this is not
a solver run directly over the 64-bit Goldilocks field.

The repeat-only Z3 run contains three fresh processes per solved case:

| Circuit | Median | Minimum–maximum |
| --- | ---: | ---: |
| Dark Forest whitelist | 0.312 s | 0.310–0.313 s |
| MACI Merkle inclusion | 2.424 s | 2.420–2.433 s |

No speedup is assigned to a memory failure. The primary timeout comparisons
are censored measurements, not exact cvc5 solve times.

## Longer runs

Selected 60-second runs retain the same 4-GiB sampled RSS cap. They extend the
three unresolved Z3 application cases, both cvc5 whitelist runs, and all three
solver configurations on Plonky2 inversion. None of these eight follow-up
runs produces a definite answer.

| Circuit / solver | 60-second outcome | Wall time |
| --- | --- | ---: |
| Dark Forest movement / Z3 | memory limit | 34.991 s |
| Hermez fee computation / Z3 | memory limit | 14.755 s |
| MACI signature / Z3 | memory limit | 27.839 s |
| Dark Forest whitelist / cvc5 GB | timeout | 60.007 s |
| Dark Forest whitelist / cvc5 split | timeout | 60.010 s |
| Plonky2 inverse / Z3 | memory limit | 14.380 s |
| Plonky2 inverse / cvc5 GB | timeout | 60.009 s |
| Plonky2 inverse / cvc5 split | timeout | 60.009 s |

The largest sampled RSS is 4,682 MiB. Both cvc5 whitelist timeouts are
CPU-active (about 60 CPU seconds), not stalled input transfers.

## Interpretation and next bottlenecks

The whitelist and Merkle results extend the earlier Poseidon/MiMC wins to
real-project circuits. They are consistent with the branch's strength on
symbolic circuit determinism. They do **not** establish broad superiority on
ZK verification: six of the eight cases remain unresolved at the primary limit.

More time alone does not rescue Z3 on the three larger unresolved application
cases: all reach the memory cap in the 60-second extension. Hermez's fee code
contains a 256-way selection and a 253-bit decomposition; the Plonky2 exports
include emulated-field range/lookup constraints. These provide concrete inputs
for investigating propagation of bit/range facts and controlling polynomial
growth. That is a source-based hypothesis about where to investigate, not a
profile proving which operation dominates runtime. No solver optimization was
added or tuned on these inputs in this experiment.

## Protocol, correctness checks, and limits

* Source snapshot: Picus `138b151d3a388e5b6c040c163e0a1db04f2ceda6`.
  The three native SR1CS files are unchanged. The five application circuits
  were compiled without source edits using Circom **2.2.3**, npm package
  `circom2@0.2.23`, with `--O0 --r1cs --sym`. This is a fresh compilation,
  not a byte-identical reproduction of older paper jobs.
* Each query asserts both full constraint systems, equates every top-level
  input (including private inputs), and requires at least one output to differ.
  **UNSAT means output determinism.** It does not establish full functional
  correctness, absence of every underconstraint, or proof-system security.
  Proof generation and proof verification throughput are not being measured.
* Both solvers receive byte-identical generated SMT-LIB. There is no benchmark
  preprocessor beyond faithful R1CS transcription and the two-copy property.
  Picus's inference and selective SMT/decomposition are not included.
* We reuse the exact frozen Z3 and official ARM64 CoCoA-enabled cvc5 **1.3.4**
  binaries from the paper comparison. The Z3 SHA-256 is
  `ded108b8c0b65169bf8b64c2444e80e7b5f76f6ea527fb8c1ebbe3ca6d86439a`;
  cvc5 is `802ca3d002b4b61ed0827d944d2ce653cbe8337580361c777d976c132d2f90f0`.
  Commands and platform details are in each run's metadata.
* The Python 3.14 harness runs one solver process at a time. Limits apply to
  wall time and RSS sampled every 50 ms; a sampled memory limit permits
  overshoot. Processes are killed and reaped on timeout or memory excess.
  No timeout, memory failure, or historical Picus label is counted as a proof.
* The importer/translator passed four tests, including exhaustive small-field
  checks of the two-copy property, exact range bounds, binary R1CS wire ordering
  and constants, and rejection of unrecognized constraints.
* For each of Z3's two UNSAT results, we generated a valid single-copy witness
  with Circom and independently checked every original R1CS equation using
  Python modular arithmetic: **888/888** whitelist and **3,114/3,114** Merkle
  constraints pass. This rules out vacuity from an impossible circuit for
  those results. It is not an independent UNSAT certificate; proof
  reconstruction remains v2.

## Reproducibility

The [fixture README](../tests/finite_field/fixtures/real-circuits/README.md)
documents compilation, import, benchmarking, and independent witness checks.
The [source manifest](../tests/finite_field/fixtures/real-circuits/source-manifest.json)
pins all included Circom files and the compiler WASM hash.

Original source dependencies, compiled R1CS/symbol files, and valid witnesses
are preserved in the fixture archives. All generated SMT queries, hashes,
per-run results, limits, and binary identities are in
[`tests/finite_field/results/real-circuits`](../tests/finite_field/results/real-circuits).
The six optional integer/range SR1CS variants also preserved in the fixture
directory were not run and are not included in the eight-case result.

There are **38 measured solver runs** in total: 24 primary, six repeat timings,
and eight longer follow-ups. Witness generation and validation are outside
these timings.

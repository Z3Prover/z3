# Exact Pulse MIP prototype

General mixed-integer linear optimization with free/unbounded variables, exact
rational coefficients, minimization/maximization, and explicit unboundedness.
There are no floating-point operations, feasibility tolerances, epsilon tests,
or fixed-width coefficient arithmetic.

The imperative branch-and-bound search is in `PulseMip.Solver.fst` (Pulse).
It mutates a shared node budget and incumbent. LP relaxations use exact
Fourier-Motzkin elimination with nonnegative integer Farkas multipliers,
objective projection, and rational witness reconstruction.

## Result guarantees

Every conclusive result passes the executable F*-verified certificate checker:

| Result | Evidence checked |
|---|---|
| `OPTIMAL` | Feasible mixed-integer point and a branching tree of exact objective bounds/refutations covering the integer search space |
| `INFEASIBLE` | Branching tree ending in exact Farkas contradictions |
| `UNBOUNDED` | Feasible mixed-integer point and a recession direction with negative minimized objective slope and integer-compatible components |
| `UNKNOWN` | Node/LP-row limit reached; optional incumbent is checked feasible |
| `ERROR` | Invalid input or rejected internal certificate, never a success-shaped fallback |

`PulseMip.Certificate.lemma_infeasible` and `lemma_optimal` prove the certificate
claims over **real-valued** models, not just a rational grid.
`lemma_unbounded` proves that every nonnegative integer step along an accepted
ray remains mixed-integer feasible, with objective decreasing linearly.
`PulseMip.Model.lemma_feasible` connects exact rational point checking to those
real-valued semantics. Pulse's public `solve` postcondition ensures the result
passes this boundary or is an explicit error. No new axioms or admits are used.

The LP algorithm is verified total and type-safe, but its completeness and its
correspondence to LP optimization are **not** proved. Search correctness does
not depend on trusting an LP answer: its witnesses/certificates are checked
before publication. Integer branch-and-bound over unbounded domains is not a
complete decision procedure; for example, `2*x - 2*y = 1` can exhaust its
budget and return `UNKNOWN`.

## Build and run

Requires Linux/WSL, a Custard/Pulse-capable F* (tested with v2026.10.25),
Z3 for verification, Python 3, OCaml/ocamlfind, and Zarith.
The defaults reuse the local toolchain under
`build\fstar-epsilon-master-20261031`; override with `--fstar`/`--z3`
or `FSTAR_EXE`/`Z3_EXE`.

From `C:\z3q` on Windows:

```powershell
wsl -d Ubuntu -- python3 /mnt/c/z3q/pulsemip/build.py --test
python .\pulsemip\solve.py .\pulsemip\example.json
```

The example returns `OPTIMAL`, point `[1, 1/3]`, objective `-4/3`, and its
certificate. `solve.py` also accepts JSON on stdin; use `--nodes` and `--rows`
to set search limits. `build.py --verify-only` checks the sources without
extraction. Generated code, executable, and build provenance are in `_build`.

## Input

- `objective`: coefficient vector; its length defines the number of variables.
- `objective_offset`: optional exact constant, default zero.
- `sense`: `min` (default) or `max`.
- `integers`: zero-based integer variable indices; all others are continuous.
- `constraints`: rows with `coefficients`, `rhs`, and optional `relation`
  (`<=`, `>=`, or `=`; default `<=`). No implicit variable bounds are added.

Use integers or exact strings such as `"1/3"` and `"0.1"`. JSON decimal numbers
are parsed exactly as decimals; Python API binary floats are rejected.
The Python interface clears denominators using positive integer scales.
It reports all coordinates/objectives as exact rational strings.

## Validation and limitations

The build verifies all six prototype F*/Pulse modules and the reused
`Z3LinearArithmeticTheory` kernel, then extracts and compiles with the
repository's exact Zarith-backed `Prims` and standard list runtime bindings.
These bindings, F*/OCaml extraction, Zarith, and the unverified JSON/protocol
adapter are part of the trusted execution boundary. There is no runtime call
to Z3 or another optimizer.

Tests independently recheck emitted certificates with Python `Fraction`,
compare 160 generated integer/continuous/mixed instances against exhaustive
integer search or exact vertex enumeration, and exercise tiny infeasible gaps,
180-bit integers, negative floors, unbounded LPs with infeasible integer
domains, resource exhaustion, and corrupted certificates.

This is a small-problem correctness prototype, **not a production simplex or
cutting-plane implementation**. Fourier-Motzkin projection can explode in rows
and coefficient size; the row limit is per projection stage, not a byte limit.
Rationals are not GCD-normalized internally. OS memory exhaustion is an error,
not mathematical evidence of infeasibility. C extraction is not provided:
the initial executable uses OCaml/Zarith to preserve arbitrary precision.

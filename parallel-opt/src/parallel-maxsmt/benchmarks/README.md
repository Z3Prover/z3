# Parallel MaxSMT benchmark layer

A small, reproducible benchmark layer for the parallel MaxSMT prototype.  It
holds a deterministic offline portfolio under `local/`, a calibrated set of
non-trivial instances for empirical evaluation, an explicit public-fetch
script, a common Z3 representation, and a machine-readable manifest.

## Layout

* `gen_benchmarks.py` writes the 24-instance **smoke** portfolio to `local/`
  (six families x two seeds x unweighted/weighted).  These solve in
  milliseconds and exist for correctness tests and CI.
* `calibrate.py` builds the **eval** and **hard** tiers by measurement (below).
* `parse.py` exposes `parse_file`, `parse_wcnf`, `parse_smt2`, returning
  `ParsedProblem(hard, soft, context)`.  Pass a fresh `z3.Context()` to build
  an isolated worker-local problem.  The layer is standalone; it does not
  import from the `pmaxsmt` package.
* `fetch_benchmarks.py` downloads an explicitly-listed public subset with a
  5 MiB cap, resumable skip-if-present, a socket timeout, and `--dry-run`.
* `make_manifest.py` writes `manifest.json`, adding a `tier` to every entry and
  reusing cached calibration timings for the eval/hard tiers.
* `calibration.json` caches the calibration measurements so tiers can be
  regenerated and the manifest never re-solves them.
* `manifest.json` records, per instance: relative path, `tier`, family, format,
  weighted flag, variable/hard/soft counts, total soft weight, source, and
  `known_optimum`; eval/hard rows additionally carry `measured_seconds`, and
  hard rows carry `best_known_cost`.
* `test_parse.py` is a plain-assertion regression test (also pytest-friendly).

## Tiers

| tier    | count | purpose | optimum |
| ------- | ----- | ------- | ------- |
| `smoke` | 24    | fast correctness tests / CI (ms each)                 | proven |
| `eval`  | 15    | empirical evaluation of an anytime solver (1–30 s)    | proven |
| `hard`  | 5     | anytime bound-trajectory evaluation (open at 60 s)    | `null`, with `best_known_cost` |
| `public`| 9     | third-party instances (see provenance)                | proven where closable |

The `eval` tier spans all six families; `hard` covers instances where
`z3.Optimize` cannot prove optimality within 60 s (so an anytime solver's
bound trajectory is actually meaningful).

### Why calibration, not hand-picked sizes

The smoke tier solves in single-digit milliseconds — useless for evaluating a
parallel *anytime* solver, where every configuration finishes before
parallelism or bound trajectories can matter.  `calibrate.py` therefore
*measures* instead of guessing.  Each family exposes one scalar difficulty knob
(instance size, or a random-3-SAT overlay for the structured covering
families).  For each `(family, weighted)` slot it bisects that knob, timing how
long `z3.Optimize` needs to prove optimality:

* measured time in `[1 s, 30 s]` → retained in `eval`;
* still open at the search timeout → bisect down; the first such candidate per
  slot is re-confirmed at the full 60 s timeout and, if still open, retained in
  `hard` with `known_optimum: null` and `best_known_cost`;
* solved far too quickly → bisect up.

Because instances are selected on the *observed* outcome, the retained eval
tier lands in the window by construction; sweep-time variance only changes
which candidates survive.

### Regenerating the tiers

```text
python calibrate.py                       # full sweep, ~20 min budget
python calibrate.py --merge --weighted true --budget 700   # top up weighted slots
python make_manifest.py --timeout 60      # fold calibration.json into the manifest
```

`calibrate.py` is seeded (`--seed`, default 20260813) and records
`(family, knob, seed, measured_seconds)` per accepted instance in
`calibration.json`, so the tiers can be regenerated on another machine.
`--merge` preserves instances already in `calibration.json` and only fills
missing slots.  The sweep is bounded by `--budget` (default 1200 s).

**Timings are machine-specific.**  The committed tiers were calibrated on:
AMD Zen 3 (CPU family 25), 32 logical cores, Windows 11 (10.0.26200),
CPython 3.14, `z3-solver` 5.0.0, single-threaded `z3.Optimize`.  The full
sweep took **1205 s** and the weighted top-up **700 s** of wall time.  The
`eval` window is defined by measured time on this machine; recalibrate
(`python calibrate.py`) elsewhere, since a different CPU will move instances
in and out of the `[1 s, 30 s]` window.

Measured eval times ranged 1.33 s–24.58 s; the five `hard` instances all
remained open at the 60 s timeout.

## Exact commands

From this directory, with Python 3.14 and `z3-solver` installed:

```text
python gen_benchmarks.py                  # (re)write the 24 smoke instances
python calibrate.py                       # (re)build eval + hard tiers (~20 min)
python fetch_benchmarks.py                # download the public subset
python fetch_benchmarks.py --dry-run      # probe public URLs without writing
python make_manifest.py --timeout 60      # rebuild manifest.json + tier summary
python test_parse.py                      # regression checks
```

`make_manifest.py` prints a tier summary (count, weighted/unweighted split,
measured-time range, families) at the end.  It measures only the smoke and
public instances (trivial or timeout-bounded); eval/hard optima come from
`calibration.json`, so a rebuild never spends a 60 s solve on a hard instance.

To use a parsed problem in a worker:

```python
from pathlib import Path
import z3
from parse import parse_file

problem = parse_file(Path("local/eval_lia_u_3.smt2"), ctx=z3.Context())
# problem.hard and problem.soft are ready for a worker-local Optimize/Solver.
```

## Input conventions

New-format WCNF uses one clause per line: `h ... 0` marks a hard clause and
`<positive-integer-weight> ... 0` marks a soft clause.  Old `p wcnf` files use
the conventional `top` threshold for hard clauses.  A plain `p cnf` file has no
hard/soft distinction, so its clauses are interpreted as unit-weight soft
clauses — the useful MaxSAT interpretation.  Empty clauses become `False`;
malformed headers, terminators, literal ranges, and weights raise `ParseError`.

SMT-LIB2 files load through `z3.Optimize().from_file()`.  Z3 exposes an
`assert-soft` as `If(formula, 0, weight)` in `objectives()`; `parse_smt2`
recovers those terms recursively and preserves integral weights.  Files with
only ordinary `minimize`/`maximize` objectives are rejected.

## Git tracking

From the target checkout root, `git check-ignore -v --no-index optimization/src/parallel-maxsmt/benchmarks/local/gen_lia_0_u.smt2 optimization/src/parallel-maxsmt/benchmarks/public/dpmaxsat_test.cnf optimization/src/parallel-maxsmt/benchmarks/calibration.json optimization/src/parallel-maxsmt/benchmarks/manifest.json` exits 1 with no output, while `git ls-files --error-unmatch optimization/src/parallel-maxsmt/benchmarks/local/gen_lia_0_u.smt2 optimization/src/parallel-maxsmt/benchmarks/public/dpmaxsat_test.cnf optimization/src/parallel-maxsmt/benchmarks/calibration.json optimization/src/parallel-maxsmt/benchmarks/manifest.json` lists all four paths; these tracked paths are **not** ignored by this repository's `.gitignore`, so no `benchmarks/.gitignore` override is required.

## Public provenance and what was fetched

The script probes both official MaxSAT Evaluation 2023 anytime archives for
provenance and skips them by the 5 MiB cap:

* weighted: `https://www.cs.helsinki.fi/group/coreo/MSE2023-anytime-instances/MSE2023-anytime-W-benchmarks.zip`
  — HTTP 200, advertised 5,726,648,750 bytes;
* unweighted: `https://www.cs.helsinki.fi/group/coreo/MSE2023-anytime-instances/MSE2023-anytime-UW-benchmarks.zip`
  — HTTP 200, advertised 2,301,903,923 bytes.

No MSE archive content is stored here.  The individually-fetchable public
instances that do download (each verified at HTTP 200 with a valid format
marker; sizes recorded in `public/SOURCES.json`) are:

| file | source | license | weighted |
| ---- | ------ | ------- | -------- |
| `public/dpmaxsat_cat.wcnf` | zzwonder/DPMaxSAT `examples/cat.wcnf` | MIT | weighted |
| `public/dpmaxsat_test.cnf` | zzwonder/DPMaxSAT `dmc/test.cnf` | MIT | unweighted CNF |
| `public/z3_maxsat_ex.smt` | Z3Prover/z3 `examples/maxsat/ex.smt` | MIT | SMT-LIB2 |
| `public/pacose_smallo0.wcnf` | tobipaxe/PacoseMaxSATSolver regression suite | MIT | small WCNF |
| `public/pacose_smallo1.wcnf` | tobipaxe/PacoseMaxSATSolver regression suite | MIT | small WCNF |
| `public/pacose_two_minimal_contradicting.wcnf` | tobipaxe/PacoseMaxSATSolver regression suite | MIT | unweighted |
| `public/i2hs_planning_depot01c.wcnf` | maxbannach/i2hs `examples/planning_wt-depot01c` | MIT | weighted |
| `public/i2hs_planning_driverlog01bc.wcnf` | maxbannach/i2hs `examples/planning_wt-driverlog01bc` | MIT | weighted |
| `public/i2hs_qcp_N10_H60_2.wcnf` | maxbannach/i2hs `examples/qcp_wt-file_qc_wcnf_N10_H60_2` | MIT | weighted |

The `weighted` flag in `manifest.json` reflects the actual clause weights in
each file (a file with any weight other than 1 is weighted), which can differ
from a provenance hint in `SOURCES.json`.  Re-running the fetch validates
existing files and reports `existing` rather than redownloading.  If a
host/network is unavailable, the script prints a clear error and exits
non-zero; it never waits indefinitely.

## License note

The generated instances and scripts here are original project work.  Public
files remain attributable to their upstream repositories (see the table above
and `public/SOURCES.json`).  The layer does not redistribute the skipped MSE
archives.

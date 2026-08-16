# Parallel anytime MaxSMT prototype
> **In-repository copy:** This prototype lives at `optimization/src/parallel-maxsmt/` in the `z3-internals` checkout. Run the commands below from that directory; the original source checkout is `C:\z3opt\parallel_maxsmt`. The non-imported artifacts are `eval\results\raw\`, `eval\e2e_artifacts\`, `eval\campaign_*.log`, `eval\campaign_*.done`, `eval\campaigns.done`, `eval\e2e_probe*.jsonl`, `eval\e2e_pty.py`, and `eval\e2e_tmux.log`; they remain only in `C:\z3opt\parallel_maxsmt`.

This directory is a runnable research prototype of an **exact anytime
MaxSMT solver** built with the Z3 Python API.  It supports both unweighted and
positive-integer weighted soft objectives, runs independent Z3 contexts in
Python worker threads, and emits feasible incumbents and sound bounds while it
runs.  When the original-core lower bound equals the feasible upper bound, it
emits a certificate that a fresh verifier checks independently.

This is deliberately a prototype, not a replacement for Z3's tuned native
optimizer.  The fifth regenerated evaluation in
[`eval/RESULTS.md`](eval/RESULTS.md) finds tied feasibility between Z3 and the
portfolio, while Z3 dominates optimality proof and incumbent cost quality more
often.  The prototype's demonstrated contributions are an independently
verified certification pipeline, measurable MSS local improvement, and
configurable role diversity. Research sources and design notes are in
[`research/RESEARCH.md`](research/RESEARCH.md).

## Supported input and objective forms

* Revised and legacy DIMACS WCNF, including hard-clause conventions.
* Plain `p cnf` DIMACS is accepted as a unit-weight soft MaxSAT instance: every
  complete clause remains intact and receives weight 1.
* SMT-LIB2 files with `assert-soft`, including weighted assertions.
* Unit penalties (unweighted) and positive integer weights (weighted).
* An extensible `Objective` abstraction in `pmaxsmt/objective.py`; adding a
  compatible objective does not require changing worker/coordinator protocols.

The parser preserves the problem's original soft-constraint order and IDs.
Worker messages contain only ordinary Python data (IDs, integer costs,
serialized assignments, and sets/lists of IDs), never Z3 ASTs or models.

## Install and basic CLI use

Commands below were run from the imported in-repository directory
`optimization/src/parallel-maxsmt/` with CPython 3.14 and `z3-solver 5.0.0`:

```text
cd optimization/src/parallel-maxsmt
python -m pip install z3-solver
```

> **Embedding warning — process-global Z3 hook.** Importing `pmaxsmt`
> immediately replaces z3py's process-global `Z3_inc_ref` and `Z3_dec_ref`
> wrappers with lock-serialized versions. This prevents the cross-thread AST
> reference-count race seen under the portfolio, but it also serializes those
> operations for unrelated Z3 work in the same host process. The hook remains
> installed for the process lifetime; use a separate process if that global
> side effect is unacceptable.

Solve a small unweighted WCNF instance with a static four-thread portfolio,
writing a JSONL anytime trace and a certificate if it closes:

```text
python -m pmaxsmt.cli solve benchmarks/local/gen_random_2sat_0_u.wcnf --threads 4 --roles hs=1,mss=1,backbone=1,maxres=0,zopt=1 --timeout 10 --seed 20260813 --trace eval/example.trace.jsonl --certificate eval/example.certificate.json
```

Solve weighted and SMT-LIB2 examples in the same way:

```text
python -m pmaxsmt.cli solve benchmarks/local/gen_lia_0_w.smt2 --threads 4 --roles hs=1,mss=1,backbone=1,maxres=0,zopt=1 --timeout 15 --seed 20260814 --trace eval/weighted.trace.jsonl --certificate eval/weighted.certificate.json
python -m pmaxsmt.cli solve benchmarks/local/gen_lia_1_u.smt2 --threads 4 --roles hs=1,mss=1,backbone=1,maxres=0,zopt=1 --timeout 15 --seed 20260815 --trace eval/lia.trace.jsonl --certificate eval/lia.certificate.json
```

The final CLI JSON object has status `OPTIMAL`, `SAT`, `UNKNOWN`, or `UNSAT`.
An `OPTIMAL` result is independently verified by default before it is printed;
`--no-verify` is an explicit opt-out for experiments that accept an unchecked
claim. Exit code `0` means `OPTIMAL`/`UNSAT`, `10` means a feasible but
uncertified `SAT`, and `20` means unknown/timeout. Verify a certificate in a
fresh context:

```text
python -m pmaxsmt.cli verify benchmarks/local/gen_lia_0_w.smt2 --certificate eval/weighted.certificate.json
```

The CLI also exposes the internal IHS-only baseline:

```text
python -m pmaxsmt.cli solve benchmarks/local/gen_random_2sat_0_u.wcnf --sequential --timeout 10 --seed 20260813 --trace eval/sequential.trace.jsonl
```

Role counts are static and must sum to `--threads`.  The recorded
`parallel-8` allocation is `hs=1,mss=2,backbone=1,maxres=2,zopt=2`.

## Architecture and soundness

`pmaxsmt/solver.py` creates the requested static allocation and starts Python
threads.  Every worker reconstructs the serializable `Problem` in its own
fresh `z3.Context`; no Z3 object crosses a thread boundary.  The coordinator
is fully asynchronous: workers publish events through a queue, while a lock
protects versioned snapshots, monotone bounds, incumbents, original cores,
and correction sets.  Workers never wait for a particular peer.
`Problem.translate` batches the declaration prelude and all hard/soft
assertions once per worker context. This avoids the prior quadratic
per-formula SMT-LIB2 reparse; on `eval_random_2sat_u_0.wcnf` the current
batched translation measured 0.608 s, while `parse_file` itself takes about
4.8 s. The four 40k–54k-clause random-2SAT instances therefore remain a
substantive search-time limitation under the short budgets, not a startup
translation artifact.


The five configurable roles are:

* **`hs`** — extracts original-soft unsat cores and searches minimum-cost
  hitting sets (the core-guided/IHS path inspired by the local `hs.py`).
* **`mss`** — seeds neighborhoods from the incumbent, grows MSS/MCS sets,
  reduces cores, and performs rotation/local improvement.
* **`backbone`** — samples feasible models, triages literals with stable values,
  and reports sampled-consensus candidates. `backbone_candidate` telemetry now
  carries those consensus literals (`countermodel: false`); a separate
  `backbone_refuted` event carries a hard-feasible countermodel. A candidate is
  asserted/recorded only after `hard AND NOT literal` is proven UNSAT; a SAT
  countermodel prevents it from being asserted.
* **`maxres`** — explores private weighted MaxRes and dual-MaxRes
  transformations, including correction-set restrictions.  Fresh relaxation
  variables, offsets, and transformed cores remain private heuristic data.
* **`zopt`** — a native Z3 `Optimize` portfolio member minimizing one weighted-sum objective (the same objective as the external baseline), useful as a source of incumbents but not required for certification.


The proof invariant is intentionally narrow.  Every global core is an
independently obtained core over **original** soft IDs.  Any feasible model
must falsify at least one member of every such core, so the minimum-cost
hitting set of stored cores is a lower bound on every feasible solution. A
hard-feasible model gives an upper bound equal to its measured penalty. Every
worker checks all hard constraints before publishing a model; after workers
stop, the coordinator applies a fresh-context final feasibility gate before
returning the incumbent. When those bounds meet, the certificate contains the
assignment, falsified soft IDs, cost, original cores, and a minimum hitting set.
`pmaxsmt/certify.py` then rebuilds a fresh context and checks hard feasibility,
model cost, every core's UNSAT status, the minimum hitting-set cost, and
`LB == UB`. Correction sets are transformation hints and are excluded from
the lower bound. MaxRes-transformed cores are never shared as proof data.

The worker-side Z3 AST reference-count operations are serialized to avoid
cross-thread `Z3_inc_ref`/`Z3_dec_ref` races. This is a deliberate soundness
guard; it may reduce parallel scaling compared with the earlier unsound
measurements.

The design choices follow the cited literature and notes: complementary
parallel lower/upper searches, implicit hitting-set MaxSMT, core/correction
set duality, MSS/MCS rotation, large-neighborhood improvement, backbone
probing, and portfolio role separation. The local reference
`C:\z3\examples\python\hs.py` is used for named relaxations, hitting-set
state, correction sets, core reduction, and rotation; its unweighted
assumptions are not silently applied to weighted objectives.

## Benchmarks

`benchmarks/manifest.json` contains 53 provenance-tracked entries:

* 24 fast `smoke` instances for correctness and CI;
* 15 calibrated `eval` instances measured at 1–30 s with native
  `z3.Optimize` on this machine;
* five `hard` instances left open at a 60 s calibration timeout, with
  `known_optimum: null` and recorded `best_known_cost`;
* nine individually fetched public WCNF instances.

The timing window is machine-dependent and must be recalibrated elsewhere.  The
large MaxSAT Evaluation archives are documented but not copied into this
checkout because they exceed the fetch cap; provenance/licenses are in
`benchmarks/public/SOURCES.json`.

Regenerate and validate the benchmark layer:

```text
cd optimization/src/parallel-maxsmt/benchmarks
python gen_benchmarks.py
python fetch_benchmarks.py --dry-run
python make_manifest.py --timeout 60
python test_parse.py
```

The seeded calibration cache is `benchmarks/calibration.json`:

```text
python calibrate.py
python calibrate.py --merge --weighted true --budget 700
```

## Tests and empirical evaluation

From the imported directory `optimization/src/parallel-maxsmt/`:

```text
python -m pytest -q tests
python -m compileall -q pmaxsmt tests
```

The regression suite covers WCNF/SMT-LIB2 parsing, weighted and unweighted
differential correctness, all worker roles, isolated contexts,
correction-set guards, validated/refuted backbone candidates, certificate
corruption rejection, UNSAT/zero-cost cases, repeated bound determinism, and
shutdown without live worker threads.

`eval/run_eval.py` launches each run in a fresh subprocess, appends one JSON
object to `eval/results/runs.jsonl`, and stores traces/certificates plus
stdout/stderr under the ignored `eval/results/raw/` directory (not imported here; see the note above). Existing run
keys are `(instance, configuration, repeat, seed)`; **budget is not part of
that key**, so a different budget must use a different seed or a cleaned
record when reproducing the same instance/configuration. The harness records
status, bounds, first-feasible and best times, trajectory events, certificates,
verification, crashes, and timeout state.

The fifth post-fix pass-separated report is generated, with assertions, directly
from the current dataset:

```text
cd optimization/src/parallel-maxsmt
python eval/report_regenerated.py
python eval/report_regenerated.py --check-invariants
```

The invariant command reports:

```text
records=415
upper_bound_lt_known_optimum=0
lost_incumbents=0
crashed_records=0
live_thread_records=0
harness_killed_records=0
wall_over_1.25x_budget=87
```

The previous report's claim that the prototype led anytime feasibility is
withdrawn. With Z3's best-so-far model retained even when `Optimize.check()`
returns `unknown`, feasibility is tied: Z3 and the prototype are 15/15 at
30 s, 45/45 at 8 s, and 5/5 on hard@60 s. The old claim favoured the prototype;
the earlier 0/88 claim disfavoured it. Both errors, and their retained
archives, are documented with equal prominence in [`eval/RESULTS.md`](eval/RESULTS.md).

Feasibility is therefore saturated. Incumbent cost quality is the useful
comparison, but the ratio needs an explicit zero-baseline rule. For each
shared record, `better`/`tie`/`worse` compares the prototype cost with the
minimum feasible Z3 cost for the same instance/tier/budget cell. The finite
ratio median covers only records where Z3's cost is positive: 45/65 records
for each parallel portfolio and 15/20 for `sequential-mss`, yielding 1.00,
1.00, and 1.05 respectively. The remaining Z3-zero records are not silently
dropped: 16/65, 16/65, and 4/20 are unbounded positive-cost gaps, including
prototype cost 67,855 against a proven Z3 optimum of 0. The full table and
all grouped zero-baseline records are generated below.

Z3 dominates proof closure (12/15 vs 1/15 at 30 s, 24/45 vs 3/45 at 8 s,
and 1/5 vs 0/5 on hard) and produces better incumbents more often. The
corrected ablation is not flat. Removing MSS costs 12 feasible records
(33/45 instead of 45/45), while removing backbone or zopt is indistinguishable
from the full portfolio at this budget. This supports the local-improvement
role; it does not show that every role helps. The IHS-only `sequential`
baseline remains 0 feasible everywhere, while `sequential-mss` demonstrates
the role-diversity control.

All 18 prototype OPTIMAL claims are independently certified, but all 18 are
from one instance, `local/eval_random_3sat_w_0.wcnf`, whose optimum is 0. The
certifier is also independently exercised on nonzero optima (6, 7, and 12)
and rejects tampered cores, bounds, assignments, and certificate core sets.

The startup defect that reparsed declarations once per formula is fixed in
`9ce3734e2`: `parse_file` costs about 4.8 s on the four 40k–54k-clause
random-2SAT cases, while batched `Problem.translate` measured 0.608 s. The
timeout, salvage, and cleanup fixes are `c908862b4`, `08b90af68`,
`f3a730b50`, `f0a55c5f0`, and `ac33a0e68`.
The corrected timeout figure is measured on the largest shipped instance,
`local/eval_random_2sat_u_1.wcnf` (54,003 lines): `solve(timeout=8)` with
eight workers took about 11.79 s (1.47x), with a worst observed ratio of
1.48x. The second-largest `u_0` measured about 10.6 s (1.33x) at 8 s.
My short-budget probe at `timeout=0.5` measured `u_0` at 1.023–1.064 s
(2.05–2.13x) and the largest `u_1` at 1.399–1.444 s (2.80–2.89x) across
three trials each. The `u_1` floor is about 1.4 s even as the requested
budget shrinks; small budgets pay proportionally more for clean
`threads_alive=[]` shutdown.


`eval/run_eval.py` salvages trace bounds from a killed child. The current
dataset has zero lost incumbents and zero harness kills. The full fifth-dataset
lineage, cost-quality table, second retraction, and generated tables are in
[`eval/RESULTS.md`](eval/RESULTS.md).

The recorded short ablation pass was:

```text
cd optimization/src/parallel-maxsmt
python eval/run_eval.py --tier eval --repeat 3 --timeout 8 --max-total 5400 --configs z3-optimize,sequential,parallel-4,parallel-8,no-backbone-4,no-mss-4,no-zopt-4 --no-resume
```

The less-censored headline and hard passes were:

```text
python eval/run_eval.py --tier eval --repeat 1 --timeout 30 --seeds 20260901 --configs z3-optimize,sequential,parallel-4,parallel-8 --max-total 0
python eval/run_eval.py --tier hard --repeat 1 --timeout 60 --configs z3-optimize,sequential,parallel-4,parallel-8 --max-total 0
```

The role-diversity control was:

```text
python eval/run_eval.py --tier eval --repeat 1 --timeout 30 --seeds 20260901 --configs sequential-mss --max-total 0
python eval/run_eval.py --tier hard --repeat 1 --timeout 60 --configs sequential-mss --max-total 0
```

`sequential` is IHS-only (`hs=1`), so it is not a role-balanced one-thread
portfolio. Supplying `--sequential` together with `--threads` or `--roles` is
rejected instead of silently discarding those options (fix `f3a730b50`).
`sequential-mss` is the one-thread MSS-only control. See
[`eval/RESULTS.md`](eval/RESULTS.md) for the five-dataset defect lineage,
equal-prominence retractions, cost-quality comparison, trajectory counts,
certification concentration, and validity threats.

## End-to-end terminal transcript

The requested tmux check was attempted first:

```text
$ tmux --version
/usr/bin/bash: line 1: tmux: command not found
```

The Windows fallback was then executed and saved to
`eval\e2e_tmux.log` in the original source checkout (not imported here; see the note above):

```text
$ python eval/e2e_pty.py
```
The fallback command above was run from the original source checkout; its driver is not imported here (see the note above).

The transcript contains live trace lines and final evidence for an unweighted
WCNF certified optimum, a weighted SMT-LIB2 instance, a QF_LIA SMT-LIB2
instance, a hard-tier 20-second `SAT` anytime run, acceptance/rejection of a
real/tampered certificate, the explicit `--sequential --threads 8` rejection,
and a console interrupt. It also demonstrates that `backbone_candidate` carries
a sampled-consensus literal while `backbone_refuted` carries the countermodel
case. The latter first tries `CTRL_C_EVENT`; this runner does not deliver it to
the child, so it falls back to `CTRL_BREAK_EVENT`, which the CLI maps to
cooperative cleanup. Its final payload has `threads_alive: []`.

## Limits

* The exact pure-Python hitting-set search is exponential in retained core
  count and is intended for prototype/reference use.
* Python scheduling, Z3 build choices, and static role allocation are
  machine-dependent; no linear parallel speedup is claimed.
* Feasibility is tied in this matrix, so incumbent cost quality and proof
  closure are the discriminating metrics. The finite-ratio medians are 1.00
  (`parallel-4`), 1.00 (`parallel-8`), and 1.05 (`sequential-mss`), but these
  cover only positive-baseline records. Z3-zero records are explicitly
  reported as unbounded when the prototype cost is positive; the largest is
  67,855 versus proven 0. The derived finite-gap table contains 47.2x, 39.0x,
  30.7x, 11.0x, 8.5x, and 3.2x rows.
* The calibrated/public benchmark collection is small compared with the full
  public suites, and all headline/hard measurements are from one machine.
* The internal `sequential` baseline is deliberately IHS-only and therefore
  weak on instances needing a model-producing role. The MSS-only control
  addresses this confound but does not replace a fully role-balanced study.
* The timeout is not a strict wall-clock guarantee: the largest instance,
  `eval_random_2sat_u_1.wcnf`, measured about 11.79 s for `timeout=8` (1.47x),
  with a worst observed ratio of 1.48x. My `timeout=0.5` probe measured
  `u_0` at 1.023–1.064 s (2.05–2.13x) and `u_1` at 1.399–1.444 s
  (2.80–2.89x); the latter is the relevant largest-instance floor. Restoring
  the bounded second join pass trades short-budget proportionality for clean
  `threads_alive=[]` shutdown.
* Sampled backbones are validated for entailment under the hard constraints,
  not for agreement across all optimal models; proving the latter would need an
  objective-bound refutation.
* MaxRes transformations are private heuristic search artifacts. Only
  independently validated original-soft cores enter the proof store.
* Serializing z3py AST reference-count operations is required for soundness in
  the threaded prototype and may reduce parallel scaling relative to earlier
  measurements.

## File map

All paths are under `optimization/src/parallel-maxsmt/`:

* `pmaxsmt/` — serializable problem/objective API, parsers, coordinator,
  solver, verifier, CLI, and worker roles.
* `tests/` — differential and regression suite.
* `benchmarks/` — generators, seeded calibration, public provenance, manifest,
  and 53 local/public instances.
* `research/RESEARCH.md` — cited parallel MaxSAT/SMT literature and Z3/
  `hs.py` notes.
* `eval/run_eval.py` — resumable subprocess evaluation harness with trace-bound
  salvage for killed children.
* `eval/report_regenerated.py` — fifth-dataset report generator and extended
  invariant checker.
* `eval/results/runs.jsonl` — current fifth-dataset pass-separated records.
* `eval/results/runs_pre_fix_f26597a79.jsonl` — retained unsound-dataset
  provenance; never aggregate it with current records.
* `eval/results/runs_startup_bug_3e3112ca6.jsonl` — retained quadratic-startup
  provenance; never aggregate it with current records.
* `eval/results/runs_timeout_bug_fd8474617.jsonl` — retained timeout/kill-margin
  provenance; never aggregate it with current records.
* `eval/results/runs_baseline_bias_55c7514b1.jsonl` — retained Z3-baseline-model
  provenance; never aggregate it with current records.
* `eval/RESULTS.md` — corrected empirical analysis, retraction, generated
  tables, and threats.
* `eval/e2e_pty.py` — PTY fallback driver (not imported here; see the note above).
* `eval/e2e_tmux.log` — required tmux attempt plus captured fallback output (not imported here; see the note above).

# Parallel anytime MaxSMT prototype

This note records a runnable Python-API research prototype in
`src/parallel-maxsmt/` in this repository's `optimization/` directory. It is an exact **anytime** MaxSMT solver for
unweighted and positive-integer weighted soft objectives: it reports feasible
incumbents and sound bounds while it runs, and can emit an independently
checked certificate when the bounds meet. It is a prototype, not a
replacement for Z3's tuned native optimizer.

It is relevant to the [parallel solving work item](README.md#parallel-solving)
("parallelizing the maxsat backend") and to the proposed
[IHS engine](redesign.md#34-maxsmt-additions). It is an architecture experiment,
not evidence of a native Z3 backend win.

## Architecture

`pmaxsmt/solver.py` creates a static role allocation and starts Python worker
threads. Each worker reconstructs the serializable `Problem` in a fresh
`z3.Context`; no Z3 AST, model, solver, or other Z3 object crosses a thread
boundary. Worker messages contain ordinary Python data such as soft IDs,
costs, serialized assignments, and sets/lists of IDs.

The coordinator is fully asynchronous. Workers publish events through a
queue, while a lock protects versioned snapshots, monotone lower and upper
bounds, incumbents, original cores, and correction sets. Workers never wait
for a particular peer. `Problem.translate` batches the declaration prelude and
all hard/soft assertions once per worker context. On
`eval_random_2sat_u_0.wcnf`, batched translation measured 0.608 s versus
`parse_file` at about 4.8 s.

The prototype installs a process-global lock-serialized wrapper for Z3Py's
`Z3_inc_ref` and `Z3_dec_ref`. This guards the cross-thread reference-count
race but serializes unrelated Z3 work, may reduce scaling, and is an embedding
hazard; use a separate process if that side effect is unacceptable.

## The five roles

The static allocation can contain these complementary roles:

* **`hs`** extracts cores over original soft IDs and searches minimum-cost
  hitting sets: the core-guided/implicit-hitting-set path inspired by the
  local `hs.py` reference.
* **`mss`** seeds neighborhoods from the incumbent, grows MSS/MCS sets,
  reduces cores, and performs rotation and local improvement.
* **`backbone`** samples feasible models, triages literals with stable sampled
  values, and reports consensus candidates. A candidate is asserted or
  recorded only after `hard AND NOT literal` is proved UNSAT; a SAT
  countermodel prevents it from being asserted.
* **`maxres`** explores private weighted MaxRes and dual-MaxRes
  transformations, including correction-set restrictions. Fresh relaxation
  variables, offsets, and transformed cores remain private heuristic data.
* **`zopt`** is a native Z3 `Optimize` portfolio member minimizing the same
  weighted-sum objective as the external baseline. It is useful as a source
  of incumbents but is not required for certification.

## Exact certificate path

The proof invariant is intentionally narrow. Every global core is independently
obtained over **original** soft IDs. Every feasible model must falsify at
least one member of each such core, so the minimum-cost hitting set of the
stored cores is a lower bound. A hard-feasible model supplies an upper bound
equal to its measured penalty. Correction sets are transformation hints and
are excluded from the lower bound; MaxRes-transformed cores never enter the
proof store.

Workers check hard constraints before publishing a model. After workers stop,
the coordinator applies a fresh-context final feasibility gate before
returning the incumbent. When `LB == UB`, the certificate records the
assignment, falsified soft IDs, cost, original cores, and a minimum hitting
set. `pmaxsmt/certify.py` rebuilds a fresh context and checks hard
feasibility, model cost, every core's UNSAT status, the minimum hitting-set
cost, and `LB == UB`.

The CLI independently verifies an `OPTIMAL` result by default. `--no-verify`
is an explicit opt-out for experiments that accept an unchecked claim.

## Evaluation method

`benchmarks/manifest.json` contains 53 provenance-tracked entries: 24 fast
`smoke` instances, 15 calibrated `eval` instances, five `hard` instances left
open at a 60-second calibration timeout, and nine individually fetched public
WCNF instances. Timing is machine-dependent and must be recalibrated
elsewhere.

`eval/run_eval.py` launches each configuration in a fresh subprocess and
appends one object to `eval/results/runs.jsonl`. Run keys are
`(instance, configuration, repeat, seed)`; budget is deliberately not part of
the key, so a different budget needs a different seed or a cleaned record.
`eval/report_regenerated.py` generates the corrected report and
`--check-invariants` checks its current dataset. The reported passes are
eval@30 s, eval@8 s with three repeats for the ablation, and hard@60 s. The
configurations include `z3-optimize`, IHS-only `sequential`,
`sequential-mss`, `parallel-4`, `parallel-8`, `no-backbone-4`, `no-mss-4`,
and `no-zopt-4`.

## Corrected findings

The corrected fifth dataset does **not** show a prototype feasibility win.
Z3 and the prototype are tied: both reach 15/15 at eval@30 s, 45/45 at
eval@8 s, and 5/5 at hard@60 s.

The two retractions have equal status. The old 0/88 claim disfavoured the
prototype because a timeout/kill-margin artifact discarded already-emitted
incumbents. A later claim that the prototype led anytime feasibility favoured
it and was withdrawn after the Z3 baseline retained its best-so-far
hard-feasible model when `Optimize.check()` returned `unknown`. The retained
archives and the corrected rerun are documented at
`src/parallel-maxsmt/eval/RESULTS.md`.

Z3 `Optimize` dominates proof closure: 12/15 versus 1/15 at 30 s, 24/45
versus 3/45 at 8 s, and 1/5 versus 0/5 on hard. It also produces better
incumbents more often. For `parallel-4`, the shared-record comparison is 19
better, 9 ties, and 37 worse for the prototype out of 65 records.

Cost-quality ratios use an explicit zero-baseline rule. The finite-ratio
medians are 1.00 for `parallel-4`, 1.00 for `parallel-8`, and 1.05 for
`sequential-mss`, counting only records where Z3's cost is positive. Z3-zero
records are not dropped: 16/65, 16/65, and 4/20 are unbounded positive-cost
gaps respectively. The largest is prototype cost 67,855 against a proven Z3
optimum of 0.

The ablation is not flat but is not uniformly supportive. Removing MSS drops
feasibility to 33/45, while `no-backbone-4` and `no-zopt-4` remain at 45/45.
This supports a local-improvement role at this budget; it does not show that
every role helps.

All 18 prototype `OPTIMAL` claims are independently certified, but all 18
come from the single cost-0 instance
`local/eval_random_3sat_w_0.wcnf`. The certifier is separately exercised on
nonzero optima (6, 7, and 12) and rejects tampered cores, bounds, assignments,
and certificate core sets. This is certification evidence, not broad
optimality coverage.

The timeout is not a hard wall-clock guarantee. On
`local/eval_random_2sat_u_1.wcnf`, `solve(timeout=8)` with eight workers took
about 11.79 s (1.47x), with a worst observed ratio of 1.48x. At
`timeout=0.5`, the largest instance had a floor of about 1.4 s (2.80–2.89x).

The demonstrated contributions are limited to three: an independently
verified certification pipeline, measurable MSS local improvement, and
configurable role diversity beyond the IHS-only baseline. The data do not
support claiming linear parallel speedup, a feasibility advantage, or a
universal benefit from every role.

## What Z3 should take from it

The following is this note's design reading, not an additional empirical
result. The prototype makes the proposed [§3.4 IHS engine](redesign.md#34-maxsmt-additions)
concrete as a separation between original-core lower-bound information and
model-producing workers. It suggests retaining that separation in a native
implementation while making the certificate boundary explicit.

For [§3.7 parallelism](redesign.md#37-or-derived-rule-policies), isolated
contexts and serializable messages are a safer starting point than sharing
mutable solver state; shared primal incumbents and verified dual information
should remain monotone. This complements §2.5's MaxSMT/discrete proposal;
`redesign.md` records the corresponding design. The prototype's negative
comparison results are a reminder to measure proof closure and incumbent quality
against the native optimizer rather than infer a win from role count.

## Pointers and reproduction

The runnable source is included in this repository at
`src/parallel-maxsmt/`. The pointers below are relative to the
`optimization/` directory:

* `src/parallel-maxsmt/pmaxsmt/` — serializable problem/objective API,
  parser, coordinator, solver, verifier, CLI, and worker roles.
* `src/parallel-maxsmt/tests/` — differential and regression tests.
* `src/parallel-maxsmt/benchmarks/manifest.json` — provenance-tracked
  benchmark manifest and shipped solver inputs.
* `src/parallel-maxsmt/research/RESEARCH.md` — research sources and design
  notes.
* `src/parallel-maxsmt/eval/run_eval.py` — fresh-subprocess evaluation
  harness.
* `src/parallel-maxsmt/eval/report_regenerated.py` — report generator
  and invariant checker.
* `src/parallel-maxsmt/eval/RESULTS.md` — full corrected analysis,
  retractions, tables, and threats.
* `src/parallel-maxsmt/eval/results/runs.jsonl` — current records.
* `src/parallel-maxsmt/eval/results/runs_pre_fix_f26597a79.jsonl`,
  `runs_startup_bug_3e3112ca6.jsonl`,
  `runs_timeout_bug_fd8474617.jsonl`, and
  `runs_baseline_bias_55c7514b1.jsonl` — retained defect archives; never
  aggregate them with current records.

The bulky or transient artifacts `C:\z3opt\parallel_maxsmt\eval\results\raw\`,
`C:\z3opt\parallel_maxsmt\eval\e2e_artifacts\`,
`C:\z3opt\parallel_maxsmt\eval\campaign_*.log`,
`C:\z3opt\parallel_maxsmt\eval\campaign_*.done`,
`C:\z3opt\parallel_maxsmt\eval\campaigns.done`,
`C:\z3opt\parallel_maxsmt\eval\e2e_probe*.jsonl`,
`C:\z3opt\parallel_maxsmt\eval\e2e_pty.py`, and
`C:\z3opt\parallel_maxsmt\eval\e2e_tmux.log` were deliberately not imported.
They remain in the original `C:\z3opt\parallel_maxsmt` directory.

Useful reproductions, with the remaining CLI options documented in the
prototype README:

```text
cd optimization/src/parallel-maxsmt
python -m pmaxsmt.cli solve benchmarks/local/gen_lia_0_w.smt2 --threads 4 --roles hs=1,mss=1,backbone=1,maxres=0,zopt=1 --timeout 15 --seed 20260814 --trace eval/weighted.trace.jsonl --certificate eval/weighted.certificate.json
python eval/report_regenerated.py --check-invariants
python -m pmaxsmt.cli verify benchmarks/local/gen_lia_0_w.smt2 --certificate eval/weighted.certificate.json
```

See `src/parallel-maxsmt/README.md` for supported input forms,
installation, additional commands, and the complete file map.

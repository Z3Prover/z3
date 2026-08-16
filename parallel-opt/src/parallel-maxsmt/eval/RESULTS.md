# Empirical evaluation results (fifth regenerated dataset)

This report is generated from the committed `eval/results/runs.jsonl`; it is not hand-entered. The three pass filters are explicit, and all four retained defect archives are excluded from aggregation.
All supplied status cells and feasible counts match the current JSONL; no cell disagrees.

## Executive findings

* **Second explicit retraction:** the previous report's claim that the prototype *leads anytime feasibility in all three passes* is withdrawn. With the corrected Z3 baseline measured on the same footing, feasibility is tied: both Z3 and the prototype reach 15/15 at eval@30s, 45/45 at eval@8s, and 5/5 at hard@60s. The previous error favoured the prototype; the prior 0/88 error disfavoured it. Both were corrected by retaining and re-running from the defective archive rather than rewriting numbers.
* Feasibility is saturated. **Incumbent cost quality is the useful comparison:** finite-ratio medians are 1.00 for `parallel-4`, 1.00 for `parallel-8`, and 1.05 for `sequential-mss`; these cover only the finite-ratio records shown below. Zero-cost Z3 optima create 16/65, 16/65, and 4/20 unbounded prototype gaps, including a cost of 67855 against a proven optimum of 0.
* Z3 `Optimize` dominates overall: it ties feasibility, proves optimality decisively (12/15 vs 1/15 at 30s; 24/45 vs 3/45 at 8s; 1/5 vs 0/5 on hard), and produces better incumbents more often. The prototype demonstrates a working exact certification pipeline, a measurable MSS local-improvement contribution, and role diversity beyond the IHS-only baseline.
* The corrected ablation is not flat: removing MSS drops `no-mss-4` to 33/45 feasible, while the full portfolio, `no-backbone-4`, and `no-zopt-4` are each 45/45. Backbone and zopt show no measurable feasibility benefit at this budget.
* All 18 prototype OPTIMAL claims are independently certified, but all 18 come from the single cost-0 instance `local/eval_random_3sat_w_0.wcnf`; this is certification evidence, not evidence of broad optimality coverage.

## Explicit retractions

### Retraction 1 — the old 0/88 claim disfavoured the prototype

The fourth-dataset report said the prototype produced 0/88 feasible incumbents on the four large random-2SAT instances. That was a timeout/kill-margin artifact: exact hitting-set work blocked deadline polling, teardown and the final gate ran after the deadline, and the harness discarded already-emitted bounds. The retained `eval/results/runs_timeout_bug_fd8474617.jsonl` has 18 records with `upper_bound=None` but a real first-feasible time. This error biased the comparison against the prototype.

### Retraction 2 — the old feasibility lead favoured the prototype

The fifth-dataset predecessor counted every Z3 `unknown` as infeasible because `z3_optimize_baseline` did not call `Optimize.model()` after `check()` returned `unknown`. Z3's best-so-far hard-feasible model was therefore discarded. The retained `eval/results/runs_baseline_bias_55c7514b1.jsonl` is the contaminated baseline dataset; `ac33a0e68` fixes the baseline model accounting. Re-running on the current dataset gives tied feasibility (15/15, 45/45, 5/5), so the old prototype-leads claim is withdrawn. These two retractions are intentionally given equal prominence: one measurement error disfavoured us, the other favoured us, and both required the same remedy — preserve the defective evidence and regenerate.

## Incumbent cost quality

Cost comparisons use each feasible prototype record against the minimum feasible Z3 incumbent cost for the same instance, tier, and budget cell. `better`, `tie`, and `worse` count every shared record. The three configurations below are the model-producing controls used for the quality comparison; the ablations are used for the separate feasibility experiment.
A ratio is finite only when the Z3 incumbent cost is positive. When Z3 proves a zero-cost optimum, a positive prototype cost is an **unbounded ratio**, not a value to discard; zero-versus-zero is reported as a zero-cost tie. The finite median and the all-record unbounded counts are both reported.

| configuration | better | tie | worse | shared records | finite-ratio records | finite median | Z3-zero records | unbounded records | max unbounded prototype cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `parallel-4` | 19 | 9 | 37 | 65 | 45 | 1.00 | 20 | 16 | 67855 |
| `parallel-8` | 21 | 7 | 37 | 65 | 45 | 1.00 | 20 | 16 | 67855 |
| `sequential-mss` | 5 | 3 | 12 | 20 | 15 | 1.05 | 5 | 4 | 67855 |

### Z3-zero optimum records (unbounded-ratio cases)

These grouped records are explicitly retained rather than filtered. `records` counts repeats in the current JSONL; the Z3 baseline cost is 0 for every row. A positive prototype cost has an infinite ratio, while prototype cost 0 is a zero-cost tie.

| configuration | instance | tier | budget (s) | records | prototype cost | classification |
|---|---|---|---:|---:|---:|---|
| `parallel-4` | `local/eval_random_2sat_u_0.wcnf` | `eval` | 8 | 3 | 10118 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_u_0.wcnf` | `eval` | 30 | 1 | 10118 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_u_1.wcnf` | `eval` | 8 | 3 | 13404 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_u_1.wcnf` | `eval` | 30 | 1 | 13404 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_w_0.wcnf` | `eval` | 8 | 3 | 50740 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_w_0.wcnf` | `eval` | 30 | 1 | 50740 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_w_1.wcnf` | `eval` | 8 | 3 | 67855 | unbounded ratio |
| `parallel-4` | `local/eval_random_2sat_w_1.wcnf` | `eval` | 30 | 1 | 67855 | unbounded ratio |
| `parallel-4` | `local/eval_random_3sat_w_0.wcnf` | `eval` | 8 | 3 | 0 | zero-cost tie |
| `parallel-4` | `local/eval_random_3sat_w_0.wcnf` | `eval` | 30 | 1 | 0 | zero-cost tie |
| `parallel-8` | `local/eval_random_2sat_u_0.wcnf` | `eval` | 8 | 3 | 10118 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_u_0.wcnf` | `eval` | 30 | 1 | 10118 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_u_1.wcnf` | `eval` | 8 | 3 | 13404 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_u_1.wcnf` | `eval` | 30 | 1 | 13404 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_w_0.wcnf` | `eval` | 8 | 3 | 50740 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_w_0.wcnf` | `eval` | 30 | 1 | 50740 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_w_1.wcnf` | `eval` | 8 | 3 | 67855 | unbounded ratio |
| `parallel-8` | `local/eval_random_2sat_w_1.wcnf` | `eval` | 30 | 1 | 67855 | unbounded ratio |
| `parallel-8` | `local/eval_random_3sat_w_0.wcnf` | `eval` | 8 | 3 | 0 | zero-cost tie |
| `parallel-8` | `local/eval_random_3sat_w_0.wcnf` | `eval` | 30 | 1 | 0 | zero-cost tie |
| `sequential-mss` | `local/eval_random_2sat_u_0.wcnf` | `eval` | 30 | 1 | 10118 | unbounded ratio |
| `sequential-mss` | `local/eval_random_2sat_u_1.wcnf` | `eval` | 30 | 1 | 13404 | unbounded ratio |
| `sequential-mss` | `local/eval_random_2sat_w_0.wcnf` | `eval` | 30 | 1 | 50740 | unbounded ratio |
| `sequential-mss` | `local/eval_random_2sat_w_1.wcnf` | `eval` | 30 | 1 | 67855 | unbounded ratio |
| `sequential-mss` | `local/eval_random_3sat_w_0.wcnf` | `eval` | 30 | 1 | 0 | zero-cost tie |

The table above accounts for all zero-baseline records (45 total across the three quality configurations), including 36 unbounded gaps and 9 ties.

The finite-ratio median covers only the explicitly counted positive-baseline records. The following **top 6 finite-ratio records**, with no deduplication, are derived by sorting every positive-baseline shared record by descending prototype/Z3 ratio:

| tier | budget (s) | instance | configuration | prototype cost | Z3 cost | ratio |
|---|---:|---|---|---:|---:|---:|
| `hard` | 60 | `local/hard_random_3sat_w_2.wcnf` | `parallel-8` | 1463 | 31 | 47.2x |
| `hard` | 60 | `local/hard_random_3sat_u_0.wcnf` | `parallel-8` | 39 | 1 | 39.0x |
| `hard` | 60 | `local/hard_random_3sat_w_2.wcnf` | `parallel-4` | 951 | 31 | 30.7x |
| `hard` | 60 | `local/hard_random_3sat_u_0.wcnf` | `parallel-4` | 11 | 1 | 11.0x |
| `hard` | 60 | `local/hard_random_3sat_w_2.wcnf` | `sequential-mss` | 262 | 31 | 8.5x |
| `eval` | 8 | `local/eval_set_cover_w_6.wcnf` | `parallel-4` | 279 | 86 | 3.2x |

Generator audit: the cost-quality and worst-gap tables above are derived by grouping and sorting the current JSONL; no hand-maintained worst-row membership list remains. The remaining exact current-dataset oracles assert pass status/record counts, feasible counts, hard-trajectory counts, and certification concentration, and fail loudly if those values change. No other silent metric filter was found; rows without a feasible Z3 baseline are not comparable and would be excluded explicitly (none occur in these three quality configurations).

## Defect lineage: five retained datasets

Five datasets exist because each defect invalidated its predecessor's numbers; only the fifth is current. Three of the four defects were measurement artifacts that inverted a headline conclusion (quadratic startup, timeout/kill-margin, and discarded Z3 best-so-far models). The unsound-incumbent defect was an implementation soundness failure.

1. `eval/results/runs_pre_fix_f26597a79.jsonl` — unsound worker incumbents, including UB 10 versus proven optimum 83; repaired by worker hard-feasibility checks and the fresh-context gate (`94715f141`, `b98d270de`).
2. `eval/results/runs_startup_bug_3e3112ca6.jsonl` — quadratic per-formula declaration reparsing; repaired by batched translation (`9ce3734e2`).
3. `eval/results/runs_timeout_bug_fd8474617.jsonl` — deadline polling/kill-margin loss of 18 emitted incumbents; repaired by cooperative timeout work and trace-bound salvage (`c908862b4`, `08b90af68`, `f3a730b50`, `f0a55c5f0`).
4. `eval/results/runs_baseline_bias_55c7514b1.jsonl` — Z3 `unknown` models discarded, biasing feasibility toward the prototype; repaired in `ac33a0e68`.
5. `eval/results/runs.jsonl` — current corrected fifth dataset after all fixes; never aggregate the archives with it.

## Standing invariant check

```text
cd optimization/src/parallel-maxsmt
python eval/report_regenerated.py --check-invariants
records=415
upper_bound_lt_known_optimum=0
lost_incumbents=0
crashed_records=0
live_thread_records=0
harness_killed_records=0
wall_over_1.25x_budget=87
```

## Generated pass tables

Status cells are asserted to sum to the records in each row; feasible means a recorded hard-feasible incumbent, whether or not optimality was proved.

| pass | configuration | records | OPTIMAL | SAT | TIMEOUT | UNKNOWN | feasible | prototype certificates |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `eval-30s` | `z3-optimize` | 15 | 12 | 3 | 0 | 0 | 15 | — |
| `eval-30s` | `parallel-4` | 15 | 1 | 14 | 0 | 0 | 15 | 1 |
| `eval-30s` | `parallel-8` | 15 | 1 | 14 | 0 | 0 | 15 | 1 |
| `eval-30s` | `sequential-mss` | 15 | 1 | 14 | 0 | 0 | 15 | 1 |
| `eval-30s` | `sequential` | 15 | 0 | 0 | 0 | 15 | 0 | 0 |
| **eval-30s total** | **all configurations** | **75** |  |  |  |  |  |  |
| `hard-60s` | `z3-optimize` | 5 | 1 | 4 | 0 | 0 | 5 | — |
| `hard-60s` | `parallel-4` | 5 | 0 | 5 | 0 | 0 | 5 | 0 |
| `hard-60s` | `parallel-8` | 5 | 0 | 5 | 0 | 0 | 5 | 0 |
| `hard-60s` | `sequential-mss` | 5 | 0 | 5 | 0 | 0 | 5 | 0 |
| `hard-60s` | `sequential` | 5 | 0 | 0 | 0 | 5 | 0 | 0 |
| **hard-60s total** | **all configurations** | **25** |  |  |  |  |  |  |
| `eval-8s` | `z3-optimize` | 45 | 24 | 21 | 0 | 0 | 45 | — |
| `eval-8s` | `parallel-4` | 45 | 3 | 42 | 0 | 0 | 45 | 3 |
| `eval-8s` | `parallel-8` | 45 | 3 | 42 | 0 | 0 | 45 | 3 |
| `eval-8s` | `no-backbone-4` | 45 | 3 | 42 | 0 | 0 | 45 | 3 |
| `eval-8s` | `no-zopt-4` | 45 | 3 | 42 | 0 | 0 | 45 | 3 |
| `eval-8s` | `no-mss-4` | 45 | 3 | 30 | 0 | 12 | 33 | 3 |
| `eval-8s` | `sequential` | 45 | 0 | 0 | 0 | 45 | 0 | 0 |
| **eval-8s total** | **all configurations** | **315** |  |  |  |  |  |  |

Pass totals are 75 (eval@30s), 25 (hard@60s), and 315 (eval@8s), for 415 current records.

## Certification, timeout, and E2E evidence

There are 18 prototype OPTIMAL claims, all independently certified, and all on `local/eval_random_3sat_w_0.wcnf` whose optimum is 0. The verifier itself has also been independently exercised on nonzero optima (set cover 6, vertex cover 7, scheduling 12) and rejects bogus cores, raised bounds, flipped assignments, and removed cores. The external Z3 baseline has 37 OPTIMAL claims; its prototype certificate field is not applicable.
Hard-tier trajectories are committed inline in `eval/results/runs.jsonl`: 20/25 records contain trajectories with 547 core, 656 correction_set, 329 incumbent, 2189 backbone_candidate, 2188 backbone_refuted, and 20 finished events. `eval/e2e_tmux.log` in the original standalone checkout `C:\z3opt\parallel_maxsmt` (not imported here) records the tmux attempt/failure, PTY fallback, unweighted/weighted/QF_LIA solves, hard anytime bounds, certificate accept/reject, sampled-consensus backbone telemetry, and sequential-option rejection.
The corrected timeout figure is measured on the largest shipped instance `local/eval_random_2sat_u_1.wcnf` (54,003 lines): `solve(timeout=8)` with eight workers took about 11.79s (1.47x), with the committed worst observed ratio 1.48x. The second-largest `u_0` measured about 10.6s (1.33x) at 8s. My short-budget probe at `timeout=0.5` measured `u_0` at 1.023–1.064s (2.05–2.13x) and the largest `u_1` at 1.399–1.444s (2.80–2.89x) across three trials each; the `u_1` floor is about 1.4s even as the requested budget shrinks. Small budgets pay proportionally more for clean `threads_alive=[]` shutdown.

## Threats to validity and reproduction

* Feasibility is tied in this matrix; incumbent cost quality and proof closure are the discriminating metrics. Zero-cost Z3 optima produce explicitly reported unbounded prototype gaps, including 67855 versus proven 0.
* The calibrated/public benchmark collection is small compared with full public suites; timings are machine-dependent; headline/hard passes use one repeat and eval@8s uses three.
* Exact Python hitting-set search is exponential; static role allocation and process-global z3py refcount serialization may reduce scaling.
* Timeout is a measured budget rather than a strict wall-clock guarantee; current invariant output reports 87/415 records over 1.25x, despite zero lost bounds and zero harness kills.

```text
cd optimization/src/parallel-maxsmt
python eval/report_regenerated.py
python eval/report_regenerated.py --check-invariants
python -m pytest -q tests
```

Current records: `eval/results/runs.jsonl`. Retained archives: `runs_pre_fix_f26597a79.jsonl`, `runs_startup_bug_3e3112ca6.jsonl`, `runs_timeout_bug_fd8474617.jsonl`, and `runs_baseline_bias_55c7514b1.jsonl`. Never aggregate archives with current records.

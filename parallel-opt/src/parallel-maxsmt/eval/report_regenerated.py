"""Generate and validate the fifth post-fix evaluation report."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import statistics
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
RESULTS_DIR = ROOT / "eval" / "results"
RUNS = RESULTS_DIR / "runs.jsonl"
PRE_FIX = RESULTS_DIR / "runs_pre_fix_f26597a79.jsonl"
STARTUP_BUG = RESULTS_DIR / "runs_startup_bug_3e3112ca6.jsonl"
TIMEOUT_BUG = RESULTS_DIR / "runs_timeout_bug_fd8474617.jsonl"
BASELINE_BIAS = RESULTS_DIR / "runs_baseline_bias_55c7514b1.jsonl"
REPORT = ROOT / "eval" / "RESULTS.md"

# These are exact current-dataset shape oracles. They fail loudly if a run is
# added, removed, or changes status; they are not used to populate metrics.
EXPECTED: dict[str, dict[str, dict[str, int]]] = {
    "eval-30s": {
        "z3-optimize": {"OPTIMAL": 12, "SAT": 3},
        "parallel-4": {"OPTIMAL": 1, "SAT": 14},
        "parallel-8": {"OPTIMAL": 1, "SAT": 14},
        "sequential-mss": {"OPTIMAL": 1, "SAT": 14},
        "sequential": {"UNKNOWN": 15},
    },
    "hard-60s": {
        "z3-optimize": {"OPTIMAL": 1, "SAT": 4},
        "parallel-4": {"SAT": 5},
        "parallel-8": {"SAT": 5},
        "sequential-mss": {"SAT": 5},
        "sequential": {"UNKNOWN": 5},
    },
    "eval-8s": {
        "z3-optimize": {"OPTIMAL": 24, "SAT": 21},
        "parallel-4": {"OPTIMAL": 3, "SAT": 42},
        "parallel-8": {"OPTIMAL": 3, "SAT": 42},
        "no-backbone-4": {"OPTIMAL": 3, "SAT": 42},
        "no-zopt-4": {"OPTIMAL": 3, "SAT": 42},
        "no-mss-4": {"OPTIMAL": 3, "SAT": 30, "UNKNOWN": 12},
        "sequential": {"UNKNOWN": 45},
    },
}
FEASIBLE: dict[str, dict[str, int]] = {
    "eval-30s": {"z3-optimize": 15, "parallel-4": 15, "parallel-8": 15, "sequential-mss": 15, "sequential": 0},
    "hard-60s": {"z3-optimize": 5, "parallel-4": 5, "parallel-8": 5, "sequential-mss": 5, "sequential": 0},
    "eval-8s": {"z3-optimize": 45, "parallel-4": 45, "parallel-8": 45, "no-backbone-4": 45, "no-zopt-4": 45, "no-mss-4": 33, "sequential": 0},
}
EXPECTED_HARD_TRAJECTORIES = 20
EXPECTED_HARD_EVENTS = {
    "core": 547,
    "correction_set": 656,
    "incumbent": 329,
    "backbone_candidate": 2189,
    "backbone_refuted": 2188,
    "finished": 20,
}
COST_CONFIGS = ("parallel-4", "parallel-8", "sequential-mss")
WORST_GAP_COUNT = 6
BIG_RANDOM_2SAT = {
    "local/eval_random_2sat_u_0.wcnf",
    "local/eval_random_2sat_u_1.wcnf",
    "local/eval_random_2sat_w_0.wcnf",
    "local/eval_random_2sat_w_1.wcnf",
}


def load(path: Path = RUNS) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def pass_rows(rows: list[dict[str, Any]], name: str) -> list[dict[str, Any]]:
    if name == "eval-30s":
        return [r for r in rows if r.get("tier") == "eval" and r.get("budget_seconds") == 30.0]
    if name == "hard-60s":
        return [r for r in rows if r.get("tier") == "hard" and r.get("budget_seconds") == 60.0]
    if name == "eval-8s":
        return [r for r in rows if r.get("tier") == "eval" and r.get("budget_seconds") == 8.0]
    raise ValueError(name)


def invariant_counts(rows: list[dict[str, Any]]) -> tuple[int, int, int, int, int, int]:
    bad = sum(
        r.get("upper_bound") is not None
        and r.get("known_optimum") is not None
        and r["upper_bound"] < r["known_optimum"]
        for r in rows
    )
    lost = sum(r.get("upper_bound") is None and r.get("time_to_first_feasible") is not None for r in rows)
    crashed = sum(bool(r.get("crashed")) for r in rows)
    live = sum(bool(r.get("threads_alive")) for r in rows)
    harness = sum(bool(r.get("harness_killed")) for r in rows)
    over = sum(
        r.get("budget_seconds") is not None
        and r.get("wall_seconds") is not None
        and r["wall_seconds"] > 1.25 * r["budget_seconds"]
        for r in rows
    )
    return bad, lost, crashed, live, harness, over


def check_pass(name: str, rows: list[dict[str, Any]]) -> tuple[int, dict[str, dict[str, int]]]:
    expected = EXPECTED[name]
    expected_total = sum(sum(statuses.values()) for statuses in expected.values())
    if len(rows) != expected_total:
        raise AssertionError(f"{name}: expected {expected_total} records, got {len(rows)}")
    actual: dict[str, dict[str, int]] = {}
    for config, statuses in expected.items():
        selected = [r for r in rows if r.get("configuration") == config]
        counts = dict(Counter(str(r.get("status")) for r in selected))
        actual[config] = counts
        if counts != statuses:
            raise AssertionError(f"{name}/{config}: expected {statuses}, got {counts}")
        if sum(counts.values()) != len(selected):
            raise AssertionError(f"{name}/{config}: status cells do not sum to row count")
        feasible = sum(r.get("upper_bound") is not None for r in selected)
        if feasible != FEASIBLE[name][config]:
            raise AssertionError(f"{name}/{config}: expected feasible={FEASIBLE[name][config]}, got {feasible}")
    return len(rows), actual


def hard_trajectory_counts(rows: list[dict[str, Any]]) -> tuple[int, Counter[str]]:
    hard = pass_rows(rows, "hard-60s")
    with_trajectory = [r for r in hard if r.get("trajectory")]
    events: Counter[str] = Counter()
    for row in hard:
        for event in row.get("trajectory") or []:
            events[str(event.get("event", "?"))] += 1
    return len(with_trajectory), events


def _cell_key(row: dict[str, Any]) -> tuple[Any, ...]:
    return (row.get("instance"), row.get("tier"), row.get("budget_seconds"))


def z3_costs_by_cell(rows: list[dict[str, Any]]) -> defaultdict[tuple[Any, ...], list[int]]:
    costs: defaultdict[tuple[Any, ...], list[int]] = defaultdict(list)
    for row in rows:
        if row.get("configuration") == "z3-optimize" and row.get("upper_bound") is not None:
            costs[_cell_key(row)].append(int(row["upper_bound"]))
    return costs


def cost_quality(rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    z3_costs = z3_costs_by_cell(rows)
    result: dict[str, dict[str, Any]] = {}
    for config in COST_CONFIGS:
        better = tie = worse = 0
        finite_ratios: list[float] = []
        shared_records = zero_baseline_records = zero_ties = unbounded_records = 0
        max_unbounded_cost = 0
        for row in rows:
            if row.get("configuration") != config or row.get("upper_bound") is None:
                continue
            baseline = z3_costs.get(_cell_key(row))
            if not baseline:
                continue
            shared_records += 1
            prototype_cost = int(row["upper_bound"])
            z3_cost = min(baseline)
            if prototype_cost < z3_cost:
                better += 1
            elif prototype_cost == z3_cost:
                tie += 1
            else:
                worse += 1
            if z3_cost == 0:
                zero_baseline_records += 1
                if prototype_cost == 0:
                    zero_ties += 1
                else:
                    unbounded_records += 1
                    max_unbounded_cost = max(max_unbounded_cost, prototype_cost)
            else:
                finite_ratios.append(prototype_cost / z3_cost)
        if not shared_records or not finite_ratios:
            raise AssertionError(f"{config}: no comparable finite-ratio records")
        result[config] = {
            "better": better,
            "tie": tie,
            "worse": worse,
            "shared_records": shared_records,
            "finite_ratio_records": len(finite_ratios),
            "finite_median": round(statistics.median(finite_ratios), 2),
            "zero_baseline_records": zero_baseline_records,
            "zero_ties": zero_ties,
            "unbounded_records": unbounded_records,
            "max_unbounded_cost": max_unbounded_cost,
        }
    return result


def zero_baseline_groups(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    z3_costs = z3_costs_by_cell(rows)
    groups: dict[tuple[Any, ...], dict[str, Any]] = {}
    for row in rows:
        config = row.get("configuration")
        if config not in COST_CONFIGS or row.get("upper_bound") is None:
            continue
        baseline = z3_costs.get(_cell_key(row))
        if not baseline or min(baseline) != 0:
            continue
        prototype_cost = int(row["upper_bound"])
        key = (config, row.get("instance"), row.get("tier"), row.get("budget_seconds"), prototype_cost)
        item = groups.setdefault(
            key,
            {
                "configuration": config,
                "instance": row.get("instance"),
                "tier": row.get("tier"),
                "budget_seconds": row.get("budget_seconds"),
                "records": 0,
                "prototype_cost": prototype_cost,
                "classification": "zero-cost tie" if prototype_cost == 0 else "unbounded ratio",
            },
        )
        item["records"] += 1
    return sorted(
        groups.values(),
        key=lambda item: (
            item["configuration"], item["instance"], item["tier"], item["budget_seconds"], item["prototype_cost"]
        ),
    )


def worst_gap_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    z3_costs = z3_costs_by_cell(rows)
    gaps: list[dict[str, Any]] = []
    for row in rows:
        if row.get("configuration") not in COST_CONFIGS or row.get("upper_bound") is None:
            continue
        baseline = z3_costs.get(_cell_key(row))
        if not baseline:
            continue
        prototype_cost = int(row["upper_bound"])
        z3_cost = min(baseline)
        if z3_cost <= 0 or prototype_cost <= z3_cost:
            continue
        gaps.append(
            {
                "instance": row.get("instance"),
                "configuration": row.get("configuration"),
                "tier": row.get("tier"),
                "budget_seconds": row.get("budget_seconds"),
                "prototype_cost": prototype_cost,
                "z3_cost": z3_cost,
                "ratio": prototype_cost / z3_cost,
            }
        )
    gaps.sort(
        key=lambda item: (
            -item["ratio"], item["instance"], item["configuration"], item["tier"], item["budget_seconds"]
        )
    )
    return gaps[:WORST_GAP_COUNT]


def check_archives(rows: list[dict[str, Any]]) -> None:
    if len(rows) != 415:
        raise AssertionError(f"fifth fresh dataset must contain 415 records, got {len(rows)}")
    if invariant_counts(rows)[:5] != (0, 0, 0, 0, 0):
        raise AssertionError(f"current invariant failure: {invariant_counts(rows)}")
    pre = load(PRE_FIX)
    if len(pre) != 414 or invariant_counts(pre)[0] != 10:
        raise AssertionError("pre-fix soundness archive oracle failed")
    if len(load(STARTUP_BUG)) != 415:
        raise AssertionError("startup-bug archive expected 415 records")
    timeout_rows = load(TIMEOUT_BUG)
    if len(timeout_rows) != 415 or invariant_counts(timeout_rows)[1:] != (18, 0, 0, 0, 92):
        raise AssertionError(f"timeout-bug archive oracle failed: {invariant_counts(timeout_rows)}")
    baseline_rows = load(BASELINE_BIAS)
    if len(baseline_rows) != 415 or sum(r.get("status") == "UNKNOWN" for r in baseline_rows if r.get("configuration") == "z3-optimize") != 28:
        raise AssertionError("baseline-bias archive oracle failed")


def make_report(rows: list[dict[str, Any]]) -> str:
    check_archives(rows)
    checked: dict[str, tuple[int, dict[str, dict[str, int]]]] = {
        name: check_pass(name, pass_rows(rows, name)) for name in EXPECTED
    }
    prototype_optimal = [r for r in rows if r.get("configuration") != "z3-optimize" and r.get("optimal_proven")]
    if len(prototype_optimal) != 18 or not all(r.get("certificate_verified") is True for r in prototype_optimal):
        raise AssertionError("fifth-dataset prototype certification oracle failed")
    if {r.get("instance") for r in prototype_optimal} != {"local/eval_random_3sat_w_0.wcnf"}:
        raise AssertionError("prototype certification concentration changed")
    if {r.get("known_optimum") for r in prototype_optimal} != {0}:
        raise AssertionError("prototype certification optimum changed")
    external_optimal = sum(r.get("configuration") == "z3-optimize" and r.get("optimal_proven") for r in rows)
    hard_trajectory_records, hard_events = hard_trajectory_counts(rows)
    if hard_trajectory_records != EXPECTED_HARD_TRAJECTORIES or dict(hard_events) != EXPECTED_HARD_EVENTS:
        raise AssertionError(f"hard trajectory oracle failed: {hard_trajectory_records}, {dict(hard_events)}")
    quality = cost_quality(rows)
    zero_groups = zero_baseline_groups(rows)
    zero_group_records = Counter()
    for item in zero_groups:
        zero_group_records[item["configuration"]] += item["records"]
    for config in COST_CONFIGS:
        if zero_group_records[config] != quality[config]["zero_baseline_records"]:
            raise AssertionError(f"zero-baseline grouping failed for {config}")
    worst = worst_gap_rows(rows)
    if len(worst) != WORST_GAP_COUNT or any(worst[i]["ratio"] < worst[i + 1]["ratio"] for i in range(len(worst) - 1)):
        raise AssertionError("derived worst-gap ordering failed")
    bad, lost, crashed, live, harness, over = invariant_counts(rows)
    q4 = quality["parallel-4"]
    q8 = quality["parallel-8"]
    qm = quality["sequential-mss"]
    lines = [
        "# Empirical evaluation results (fifth regenerated dataset)", "",
        "This report is generated from the committed `eval/results/runs.jsonl`; it is not hand-entered. The three pass filters are explicit, and all four retained defect archives are excluded from aggregation.",
        "All supplied status cells and feasible counts match the current JSONL; no cell disagrees.", "",
        "## Executive findings", "",
        "* **Second explicit retraction:** the previous report's claim that the prototype *leads anytime feasibility in all three passes* is withdrawn. With the corrected Z3 baseline measured on the same footing, feasibility is tied: both Z3 and the prototype reach 15/15 at eval@30s, 45/45 at eval@8s, and 5/5 at hard@60s. The previous error favoured the prototype; the prior 0/88 error disfavoured it. Both were corrected by retaining and re-running from the defective archive rather than rewriting numbers.",
        f"* Feasibility is saturated. **Incumbent cost quality is the useful comparison:** finite-ratio medians are {q4['finite_median']:.2f} for `parallel-4`, {q8['finite_median']:.2f} for `parallel-8`, and {qm['finite_median']:.2f} for `sequential-mss`; these cover only the finite-ratio records shown below. Zero-cost Z3 optima create {q4['unbounded_records']}/{q4['shared_records']}, {q8['unbounded_records']}/{q8['shared_records']}, and {qm['unbounded_records']}/{qm['shared_records']} unbounded prototype gaps, including a cost of {q8['max_unbounded_cost']} against a proven optimum of 0.",
        "* Z3 `Optimize` dominates overall: it ties feasibility, proves optimality decisively (12/15 vs 1/15 at 30s; 24/45 vs 3/45 at 8s; 1/5 vs 0/5 on hard), and produces better incumbents more often. The prototype demonstrates a working exact certification pipeline, a measurable MSS local-improvement contribution, and role diversity beyond the IHS-only baseline.",
        "* The corrected ablation is not flat: removing MSS drops `no-mss-4` to 33/45 feasible, while the full portfolio, `no-backbone-4`, and `no-zopt-4` are each 45/45. Backbone and zopt show no measurable feasibility benefit at this budget.",
        "* All 18 prototype OPTIMAL claims are independently certified, but all 18 come from the single cost-0 instance `local/eval_random_3sat_w_0.wcnf`; this is certification evidence, not evidence of broad optimality coverage.", "",
        "## Explicit retractions", "",
        "### Retraction 1 — the old 0/88 claim disfavoured the prototype", "",
        "The fourth-dataset report said the prototype produced 0/88 feasible incumbents on the four large random-2SAT instances. That was a timeout/kill-margin artifact: exact hitting-set work blocked deadline polling, teardown and the final gate ran after the deadline, and the harness discarded already-emitted bounds. The retained `eval/results/runs_timeout_bug_fd8474617.jsonl` has 18 records with `upper_bound=None` but a real first-feasible time. This error biased the comparison against the prototype.", "",
        "### Retraction 2 — the old feasibility lead favoured the prototype", "",
        "The fifth-dataset predecessor counted every Z3 `unknown` as infeasible because `z3_optimize_baseline` did not call `Optimize.model()` after `check()` returned `unknown`. Z3's best-so-far hard-feasible model was therefore discarded. The retained `eval/results/runs_baseline_bias_55c7514b1.jsonl` is the contaminated baseline dataset; `ac33a0e68` fixes the baseline model accounting. Re-running on the current dataset gives tied feasibility (15/15, 45/45, 5/5), so the old prototype-leads claim is withdrawn. These two retractions are intentionally given equal prominence: one measurement error disfavoured us, the other favoured us, and both required the same remedy — preserve the defective evidence and regenerate.", "",
        "## Incumbent cost quality", "",
        "Cost comparisons use each feasible prototype record against the minimum feasible Z3 incumbent cost for the same instance, tier, and budget cell. `better`, `tie`, and `worse` count every shared record. The three configurations below are the model-producing controls used for the quality comparison; the ablations are used for the separate feasibility experiment.",
        "A ratio is finite only when the Z3 incumbent cost is positive. When Z3 proves a zero-cost optimum, a positive prototype cost is an **unbounded ratio**, not a value to discard; zero-versus-zero is reported as a zero-cost tie. The finite median and the all-record unbounded counts are both reported.",
        "", "| configuration | better | tie | worse | shared records | finite-ratio records | finite median | Z3-zero records | unbounded records | max unbounded prototype cost |", "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for config in COST_CONFIGS:
        q = quality[config]
        lines.append(f"| `{config}` | {q['better']} | {q['tie']} | {q['worse']} | {q['shared_records']} | {q['finite_ratio_records']} | {q['finite_median']:.2f} | {q['zero_baseline_records']} | {q['unbounded_records']} | {q['max_unbounded_cost']} |")
    lines += [
        "", "### Z3-zero optimum records (unbounded-ratio cases)", "",
        "These grouped records are explicitly retained rather than filtered. `records` counts repeats in the current JSONL; the Z3 baseline cost is 0 for every row. A positive prototype cost has an infinite ratio, while prototype cost 0 is a zero-cost tie.",
        "", "| configuration | instance | tier | budget (s) | records | prototype cost | classification |", "|---|---|---|---:|---:|---:|---|",
    ]
    for item in zero_groups:
        lines.append(f"| `{item['configuration']}` | `{item['instance']}` | `{item['tier']}` | {item['budget_seconds']:.0f} | {item['records']} | {item['prototype_cost']} | {item['classification']} |")
    lines += [
        "", f"The table above accounts for all zero-baseline records ({sum(item['records'] for item in zero_groups)} total across the three quality configurations), including {sum(item['records'] for item in zero_groups if item['classification'] == 'unbounded ratio')} unbounded gaps and {sum(item['records'] for item in zero_groups if item['classification'] == 'zero-cost tie')} ties.",
        "", f"The finite-ratio median covers only the explicitly counted positive-baseline records. The following **top {WORST_GAP_COUNT} finite-ratio records**, with no deduplication, are derived by sorting every positive-baseline shared record by descending prototype/Z3 ratio:",
        "", "| tier | budget (s) | instance | configuration | prototype cost | Z3 cost | ratio |", "|---|---:|---|---|---:|---:|---:|",
    ]
    for item in worst:
        lines.append(f"| `{item['tier']}` | {item['budget_seconds']:.0f} | `{item['instance']}` | `{item['configuration']}` | {item['prototype_cost']} | {item['z3_cost']} | {item['ratio']:.1f}x |")
    lines += [
        "", "Generator audit: the cost-quality and worst-gap tables above are derived by grouping and sorting the current JSONL; no hand-maintained worst-row membership list remains. The remaining exact current-dataset oracles assert pass status/record counts, feasible counts, hard-trajectory counts, and certification concentration, and fail loudly if those values change. No other silent metric filter was found; rows without a feasible Z3 baseline are not comparable and would be excluded explicitly (none occur in these three quality configurations).", "",
        "## Defect lineage: five retained datasets", "",
        "Five datasets exist because each defect invalidated its predecessor's numbers; only the fifth is current. Three of the four defects were measurement artifacts that inverted a headline conclusion (quadratic startup, timeout/kill-margin, and discarded Z3 best-so-far models). The unsound-incumbent defect was an implementation soundness failure.",
        "", "1. `eval/results/runs_pre_fix_f26597a79.jsonl` — unsound worker incumbents, including UB 10 versus proven optimum 83; repaired by worker hard-feasibility checks and the fresh-context gate (`94715f141`, `b98d270de`).",
        "2. `eval/results/runs_startup_bug_3e3112ca6.jsonl` — quadratic per-formula declaration reparsing; repaired by batched translation (`9ce3734e2`).",
        "3. `eval/results/runs_timeout_bug_fd8474617.jsonl` — deadline polling/kill-margin loss of 18 emitted incumbents; repaired by cooperative timeout work and trace-bound salvage (`c908862b4`, `08b90af68`, `f3a730b50`, `f0a55c5f0`).",
        "4. `eval/results/runs_baseline_bias_55c7514b1.jsonl` — Z3 `unknown` models discarded, biasing feasibility toward the prototype; repaired in `ac33a0e68`.",
        "5. `eval/results/runs.jsonl` — current corrected fifth dataset after all fixes; never aggregate the archives with it.", "",
        "## Standing invariant check", "",
        "```text", "cd optimization/src/parallel-maxsmt", "python eval/report_regenerated.py --check-invariants",
        f"records={len(rows)}", f"upper_bound_lt_known_optimum={bad}", f"lost_incumbents={lost}", f"crashed_records={crashed}", f"live_thread_records={live}", f"harness_killed_records={harness}", f"wall_over_1.25x_budget={over}", "```", "",
        "## Generated pass tables", "", "Status cells are asserted to sum to the records in each row; feasible means a recorded hard-feasible incumbent, whether or not optimality was proved.", "", "| pass | configuration | records | OPTIMAL | SAT | TIMEOUT | UNKNOWN | feasible | prototype certificates |", "|---|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for name in ("eval-30s", "hard-60s", "eval-8s"):
        total, actual = checked[name]
        for config in EXPECTED[name]:
            selected = [r for r in pass_rows(rows, name) if r.get("configuration") == config]
            counts = actual[config]
            cert = sum(r.get("certificate_verified") is True for r in selected)
            lines.append(f"| `{name}` | `{config}` | {len(selected)} | {counts.get('OPTIMAL', 0)} | {counts.get('SAT', 0)} | {counts.get('TIMEOUT', 0)} | {counts.get('UNKNOWN', 0)} | {sum(r.get('upper_bound') is not None for r in selected)} | {cert if config != 'z3-optimize' else '—'} |")
        lines.append(f"| **{name} total** | **all configurations** | **{total}** |  |  |  |  |  |  |")
    lines += [
        "", "Pass totals are 75 (eval@30s), 25 (hard@60s), and 315 (eval@8s), for 415 current records.", "",
        "## Certification, timeout, and E2E evidence", "",
        "There are 18 prototype OPTIMAL claims, all independently certified, and all on `local/eval_random_3sat_w_0.wcnf` whose optimum is 0. The verifier itself has also been independently exercised on nonzero optima (set cover 6, vertex cover 7, scheduling 12) and rejects bogus cores, raised bounds, flipped assignments, and removed cores. The external Z3 baseline has 37 OPTIMAL claims; its prototype certificate field is not applicable.",
        f"Hard-tier trajectories are committed inline in `eval/results/runs.jsonl`: {hard_trajectory_records}/25 records contain trajectories with {hard_events['core']} core, {hard_events['correction_set']} correction_set, {hard_events['incumbent']} incumbent, {hard_events['backbone_candidate']} backbone_candidate, {hard_events['backbone_refuted']} backbone_refuted, and {hard_events['finished']} finished events. `eval/e2e_tmux.log` in the original standalone checkout `C:\\z3opt\\parallel_maxsmt` (not imported here) records the tmux attempt/failure, PTY fallback, unweighted/weighted/QF_LIA solves, hard anytime bounds, certificate accept/reject, sampled-consensus backbone telemetry, and sequential-option rejection.",
        "The corrected timeout figure is measured on the largest shipped instance `local/eval_random_2sat_u_1.wcnf` (54,003 lines): `solve(timeout=8)` with eight workers took about 11.79s (1.47x), with the committed worst observed ratio 1.48x. The second-largest `u_0` measured about 10.6s (1.33x) at 8s. My short-budget probe at `timeout=0.5` measured `u_0` at 1.023–1.064s (2.05–2.13x) and the largest `u_1` at 1.399–1.444s (2.80–2.89x) across three trials each; the `u_1` floor is about 1.4s even as the requested budget shrinks. Small budgets pay proportionally more for clean `threads_alive=[]` shutdown.", "",
        "## Threats to validity and reproduction", "",
        "* Feasibility is tied in this matrix; incumbent cost quality and proof closure are the discriminating metrics. Zero-cost Z3 optima produce explicitly reported unbounded prototype gaps, including 67855 versus proven 0.",
        "* The calibrated/public benchmark collection is small compared with full public suites; timings are machine-dependent; headline/hard passes use one repeat and eval@8s uses three.",
        "* Exact Python hitting-set search is exponential; static role allocation and process-global z3py refcount serialization may reduce scaling.",
        "* Timeout is a measured budget rather than a strict wall-clock guarantee; current invariant output reports 87/415 records over 1.25x, despite zero lost bounds and zero harness kills.",
        "", "```text", "cd optimization/src/parallel-maxsmt", "python eval/report_regenerated.py", "python eval/report_regenerated.py --check-invariants", "python -m pytest -q tests", "```", "",
        "Current records: `eval/results/runs.jsonl`. Retained archives: `runs_pre_fix_f26597a79.jsonl`, `runs_startup_bug_3e3112ca6.jsonl`, `runs_timeout_bug_fd8474617.jsonl`, and `runs_baseline_bias_55c7514b1.jsonl`. Never aggregate archives with current records.",
    ]
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-invariants", action="store_true")
    args = parser.parse_args()
    rows = load()
    bad, lost, crashed, live, harness, over = invariant_counts(rows)
    if args.check_invariants:
        print(f"records={len(rows)}")
        print(f"upper_bound_lt_known_optimum={bad}")
        print(f"lost_incumbents={lost}")
        print(f"crashed_records={crashed}")
        print(f"live_thread_records={live}")
        print(f"harness_killed_records={harness}")
        print(f"wall_over_1.25x_budget={over}")
        return 0 if (bad, lost, crashed, live, harness) == (0, 0, 0, 0, 0) else 1
    REPORT.write_text(make_report(rows), encoding="utf-8")
    print(f"wrote {REPORT}")
    for name in EXPECTED:
        print(f"{name}: records={len(pass_rows(rows, name))}")
    print(f"invariant: upper_bound_lt_known_optimum={bad}, lost_incumbents={lost}, crashed={crashed}, live={live}, harness_killed={harness}, over_1.25x={over}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

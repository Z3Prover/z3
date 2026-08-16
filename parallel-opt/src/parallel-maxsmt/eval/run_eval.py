"""Empirical evaluation harness for the parallel MaxSMT prototype.

The parent process runs every configuration in a fresh subprocess.  This keeps a
crash, a native Z3 timeout, or a broken worker from losing earlier JSONL records.
The command is resumable: a run key is the tuple (instance, configuration,
repeat, seed), and completed keys are skipped unless ``--no-resume`` is used.

Examples (from the imported directory ``optimization/src/parallel-maxsmt``)::

    python eval/run_eval.py --tier smoke --repeat 1 --timeout 10
    python eval/run_eval.py --tier eval --repeat 3 --timeout 60 --max-total 5400
    python eval/run_eval.py --tier hard --repeat 1 --timeout 60

The ``--z3-child`` mode is an implementation detail used to isolate the
external Optimize baseline in its own Python process.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time
from typing import Any, Iterable
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
BENCHMARKS = ROOT / "benchmarks"
RESULTS = ROOT / "eval" / "results"
RUNS_PATH = RESULTS / "runs.jsonl"
SEEDS = (20260813, 20260814, 20260815, 20260816, 20260817)

# The role strings are deliberately explicit: they make each ablation's static
# allocation inspectable and keep the total equal to --threads.
CONFIGS: dict[str, dict[str, Any]] = {
    "z3-optimize": {"kind": "z3", "threads": 1, "roles": None},
    "sequential": {"kind": "sequential", "threads": 1, "roles": None},
    "sequential-mss": {
        "kind": "parallel", "threads": 1, "roles": "hs=0,mss=1,backbone=0,maxres=0,zopt=0"
    },
    "parallel-4": {
        "kind": "parallel", "threads": 4, "roles": "hs=1,mss=1,backbone=1,maxres=0,zopt=1"
    },
    "parallel-8": {
        "kind": "parallel", "threads": 8, "roles": "hs=1,mss=2,backbone=1,maxres=2,zopt=2"
    },
    "no-backbone-4": {
        "kind": "parallel", "threads": 4, "roles": "hs=1,mss=2,backbone=0,maxres=0,zopt=1"
    },
    "no-mss-4": {
        "kind": "parallel", "threads": 4, "roles": "hs=1,mss=0,backbone=2,maxres=0,zopt=1"
    },
    "no-zopt-4": {
        "kind": "parallel", "threads": 4, "roles": "hs=1,mss=1,backbone=1,maxres=1,zopt=0"
    },
}


def _json_line(text: str) -> dict[str, Any] | None:
    for line in reversed(text.splitlines()):
        line = line.strip()
        if not line:
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            return value
    return None


def _subprocess_limit(entry: dict[str, Any], timeout: float) -> float:
    """Include parsing/serialization headroom scaled to the instance."""
    constraint_count = int(entry.get("nhard") or 0) + int(entry.get("nsoft") or 0)
    try:
        measured = max(0.0, float(entry.get("measured_seconds") or 0.0))
    except (TypeError, ValueError):
        measured = 0.0
    variable_overhead = max(2.0, measured * 3.0, constraint_count * 0.0002)
    return max(1.0, float(timeout) + 3.0 + variable_overhead)

def _safe_name(text: str) -> str:
    return "".join(c if c.isalnum() or c in "._-" else "_" for c in text)


def _read_manifest(tier: str) -> list[dict[str, Any]]:
    entries = json.loads((BENCHMARKS / "manifest.json").read_text(encoding="utf-8"))
    if not isinstance(entries, list):
        raise ValueError("manifest.json must contain a list")
    selected = [e for e in entries if tier == "all" or e.get("tier") == tier]
    selected.sort(key=lambda e: str(e.get("path", "")))
    return selected


def _run_key(instance: str, config: str, repeat: int, seed: int) -> str:
    return f"{instance}|{config}|{repeat}|{seed}"


def _load_done(path: Path) -> dict[str, dict[str, Any]]:
    done: dict[str, dict[str, Any]] = {}
    if not path.exists():
        return done
    for line in path.read_text(encoding="utf-8").splitlines():
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        key = record.get("run_key")
        if key:
            done[str(key)] = record
    return done


def _trace_metrics(
    path: Path, tier: str, *, salvage: bool = False
) -> dict[str, Any]:
    """Extract elapsed anytime metrics from TraceWriter's epoch timestamps."""
    if not path.exists():
        return {
            "time_to_first_feasible": None,
            "time_to_best": None,
            "trajectory": [],
            "last_lower_bound": None,
            "last_upper_bound": None,
        }
    events: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict) and isinstance(item.get("timestamp"), (int, float)):
            events.append(item)
    if not events:
        return {
            "time_to_first_feasible": None,
            "time_to_best": None,
            "trajectory": [],
            "last_lower_bound": None,
            "last_upper_bound": None,
        }
    origin = min(float(e["timestamp"]) for e in events)
    first: float | None = None
    best: float | None = None
    trajectory: list[dict[str, Any]] = []
    last_lower: int | None = None
    last_upper: int | None = None
    for event in sorted(events, key=lambda e: float(e["timestamp"])):
        elapsed = max(0.0, float(event["timestamp"]) - origin)
        name = event.get("event")
        if event.get("lb") is not None:
            last_lower = int(event["lb"])
        if event.get("ub") is not None:
            last_upper = int(event["ub"])
        if name == "incumbent":
            if first is None:
                first = elapsed
            best = elapsed
        if (tier == "hard" or salvage) and (
            event.get("lb") is not None or event.get("ub") is not None
        ):
            trajectory.append(
                {
                    "time": round(elapsed, 6),
                    "lb": event.get("lb"),
                    "ub": event.get("ub"),
                    "event": name,
                    "worker": event.get("worker_id"),
                    "role": event.get("role"),
                    "status": event.get("status"),
                }
            )
    return {
        "time_to_first_feasible": first,
        "time_to_best": best,
        "trajectory": trajectory,
        "last_lower_bound": last_lower,
        "last_upper_bound": last_upper,
    }


def _verify(instance: Path, certificate: Path) -> tuple[bool | None, str]:
    if not certificate.exists():
        return None, "no certificate file"
    cmd = [
        sys.executable,
        "-m",
        "pmaxsmt.cli",
        "verify",
        str(instance),
        "--certificate",
        str(certificate),
    ]
    try:
        proc = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True, timeout=120)
    except subprocess.TimeoutExpired:
        return False, "verify subprocess timed out"
    payload = _json_line(proc.stdout)
    verified = bool(payload and payload.get("verified") is True and proc.returncode == 0)
    detail = (proc.stdout.strip() or proc.stderr.strip())[-2000:]
    return verified, detail


def _z3_child(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="run_eval.py --z3-child")
    parser.add_argument("--file", required=True)
    parser.add_argument("--timeout", type=float, required=True)
    parser.add_argument("--engine", default=None)
    args = parser.parse_args(argv)
    from pmaxsmt.solver import z3_optimize_baseline

    result = z3_optimize_baseline(args.file, timeout=args.timeout, engine=args.engine)
    result["event"] = "baseline-final"
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0


def _execute(
    entry: dict[str, Any],
    config_name: str,
    repeat: int,
    seed: int,
    timeout: float,
    raw_dir: Path,
    tier: str,
) -> dict[str, Any]:
    rel = str(entry["path"])
    instance = (BENCHMARKS / rel).resolve()
    cfg = CONFIGS[config_name]
    stem = _safe_name(f"{tier}-{rel}-{config_name}-r{repeat}-s{seed}")
    trace = raw_dir / f"{stem}.trace.jsonl"
    certificate = raw_dir / f"{stem}.certificate.json"
    stdout_path = raw_dir / f"{stem}.stdout.txt"
    stderr_path = raw_dir / f"{stem}.stderr.txt"
    if cfg["kind"] == "z3":
        command = [
            sys.executable,
            str(Path(__file__).resolve()),
            "--z3-child",
            "--file",
            str(instance),
            "--timeout",
            str(timeout),
        ]
    else:
        command = [sys.executable, "-m", "pmaxsmt.cli", "solve", str(instance)]
        if cfg["kind"] == "sequential":
            command.append("--sequential")
        else:
            command.extend(["--threads", str(cfg["threads"]), "--roles", cfg["roles"]])
        command.extend(
            [
                "--timeout",
                str(timeout),
                "--seed",
                str(seed),
                "--trace",
                str(trace),
                "--certificate",
                str(certificate),
            ]
        )
    started = time.perf_counter()
    timed_out = False
    crashed = False
    stdout = ""
    stderr = ""
    exit_code: int | None = None
    try:
        proc = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            capture_output=True,
            timeout=_subprocess_limit(entry, timeout),
            env={**os.environ, "PYTHONUNBUFFERED": "1"},
        )
        stdout, stderr, exit_code = proc.stdout, proc.stderr, proc.returncode
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        stdout = (exc.stdout or "") if isinstance(exc.stdout, str) else (exc.stdout or b"").decode(errors="replace")
        stderr = (exc.stderr or "") if isinstance(exc.stderr, str) else (exc.stderr or b"").decode(errors="replace")
    except OSError as exc:
        crashed = True
        stderr = f"{type(exc).__name__}: {exc}"
    wall = time.perf_counter() - started
    stdout_path.write_text(stdout, encoding="utf-8")
    stderr_path.write_text(stderr, encoding="utf-8")
    payload = _json_line(stdout)
    if cfg["kind"] == "z3":
        status = str(payload.get("status", "CRASH")) if payload else ("UNKNOWN" if timed_out else "CRASH")
        lower = None
        upper = payload.get("cost") if payload else None
        elapsed = payload.get("elapsed") if payload else None
        certificate_verified: bool | None = None
        trace_metrics = {
            "time_to_first_feasible": elapsed if upper is not None else None,
            "time_to_best": elapsed if upper is not None else None,
            "trajectory": [],
            "last_lower_bound": None,
            "last_upper_bound": upper,
        }
        optimal_proven = status == "OPTIMAL"
    else:
        trace_metrics = _trace_metrics(trace, tier, salvage=timed_out)
        if payload:
            status = str(payload.get("status", "CRASH"))
            lower = payload.get("lower_bound")
            upper = payload.get("upper_bound")
            elapsed = payload.get("elapsed")
        elif timed_out:
            lower = trace_metrics["last_lower_bound"]
            upper = trace_metrics["last_upper_bound"]
            status = "SAT" if upper is not None else "UNKNOWN"
            elapsed = None
        else:
            status = "CRASH"
            lower = upper = elapsed = None
        if trace_metrics["time_to_first_feasible"] is None and upper is not None:
            trace_metrics["time_to_first_feasible"] = elapsed if elapsed is not None else wall
        if trace_metrics["time_to_best"] is None and upper is not None:
            trace_metrics["time_to_best"] = elapsed if elapsed is not None else wall
        optimal_proven = status == "OPTIMAL"
        certificate_verified = None
        if optimal_proven:
            certificate_verified, detail = _verify(instance, certificate)
        else:
            detail = ""
    if payload is None and not timed_out and not crashed:
        status = "CRASH"
        crashed = True
    record: dict[str, Any] = {
        "run_key": _run_key(rel, config_name, repeat, seed),
        "instance": rel,
        "tier": tier,
        "family": entry.get("family"),
        "weighted": bool(entry.get("weighted", False)),
        "known_optimum": entry.get("known_optimum"),
        "best_known_cost": entry.get("best_known_cost"),
        "configuration": config_name,
        "kind": cfg["kind"],
        "threads": cfg.get("threads"),
        "roles": cfg.get("roles"),
        "repeat": repeat,
        "seed": seed,
        "budget_seconds": timeout,
        "status": status,
        "lower_bound": lower,
        "upper_bound": upper,
        "wall_seconds": round(wall, 6),
        "solver_elapsed_seconds": elapsed,
        "time_to_first_feasible": trace_metrics["time_to_first_feasible"],
        "time_to_best": trace_metrics["time_to_best"],
        "optimal_proven": optimal_proven,
        "certificate_verified": certificate_verified,
        "timed_out": timed_out,
        "harness_killed": timed_out,
        "crashed": crashed,
        "exit_code": exit_code,
        "trace": str(trace.relative_to(ROOT)) if trace.exists() else None,
        "certificate": str(certificate.relative_to(ROOT)) if certificate.exists() else None,
        "trajectory": trace_metrics["trajectory"],
        "verify_detail": detail if cfg["kind"] != "z3" else "not applicable to external baseline",
        "stdout": str(stdout_path.relative_to(ROOT)),
        "stderr": str(stderr_path.relative_to(ROOT)),
    }
    return record


def _fmt(value: Any) -> str:
    if value is None:
        return "—"
    if isinstance(value, float):
        return f"{value:.3f}"
    return str(value)


def _summaries(records: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for row in records:
        grouped[(str(row["instance"]), str(row["configuration"]))].append(row)
    output: list[dict[str, Any]] = []
    for (instance, config), rows in sorted(grouped.items()):
        times = [float(r["wall_seconds"]) for r in rows if r.get("wall_seconds") is not None]
        bests = [float(r["time_to_best"]) for r in rows if r.get("time_to_best") is not None]
        optimal_times = [float(r["wall_seconds"]) for r in rows if r.get("optimal_proven") and r.get("wall_seconds") is not None]
        optimal = sum(bool(r.get("optimal_proven")) for r in rows)
        certified = sum(r.get("certificate_verified") is True for r in rows)
        bounds = sorted({f"{r.get('lower_bound', '—')}..{r.get('upper_bound', '—')}" for r in rows})
        output.append(
            {
                "instance": instance,
                "configuration": config,
                "runs": len(rows),
                "status": ",".join(sorted({str(r.get("status")) for r in rows})),
                "median_wall": statistics.median(times) if times else None,
                "range_wall": (min(times), max(times)) if times else None,
                "median_best": statistics.median(bests) if bests else None,
                "median_optimal": statistics.median(optimal_times) if optimal_times else None,
                "bounds": ", ".join(bounds),
                "optimal": f"{optimal}/{len(rows)}",
                "certified": f"{certified}/{optimal}" if optimal else "—",
            }
        )
    return output


def write_results_md(records: list[dict[str, Any]], *, tier: str, requested: dict[str, Any]) -> Path:
    out = ROOT / "eval" / "RESULTS.md"
    by_tier: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in records:
        by_tier[str(row.get("tier", "unknown"))].append(row)
    lines = [
        "# Empirical evaluation results",
        "",
        "This file is generated by `eval/run_eval.py` from `eval/results/runs.jsonl`.",
        "It preserves completed, timed-out, and crashed runs; no result is inferred from a missing record.",
        "",
        f"Requested tier: `{tier}`; requested repeats: `{requested.get('repeat')}`; budget: `{requested.get('timeout')} s`; records: `{len(records)}`.",
        f"Configurations requested: `{', '.join(requested.get('configs', []))}`.",
        "",
    ]
    for current_tier, rows in sorted(by_tier.items()):
        lines += [f"## {current_tier} tier", ""]
        lines += [
            "| instance | configuration | runs | status | median wall (s) | wall range (s) | median time-to-best (s) | median time-to-optimal (s) | final LB..UB | optimal | independently certified |",
            "|---|---:|---:|---|---:|---:|---:|---:|---|---:|---:|",
        ]
        for item in _summaries(rows):
            rng = "—" if item["range_wall"] is None else f"{item['range_wall'][0]:.3f}–{item['range_wall'][1]:.3f}"
            lines.append(
                f"| `{item['instance']}` | `{item['configuration']}` | {item['runs']} | {item['status']} | {_fmt(item['median_wall'])} | {rng} | {_fmt(item['median_best'])} | {_fmt(item['median_optimal'])} | {item['bounds']} | {item['optimal']} | {item['certified']} |"
            )
        lines.append("")
        lines.append("")
        if current_tier == "hard":
            lines += ["### Hard-tier anytime trajectories", ""]
            for row in sorted(rows, key=lambda r: (str(r.get("instance")), str(r.get("configuration")), int(r.get("repeat", 0)))):
                trajectory = row.get("trajectory") or []
                lines.append(
                    f"**{row['instance']} / {row['configuration']} / repeat {row['repeat']} / seed {row['seed']}** — final `{row['status']}`, LB `{row.get('lower_bound')}`, UB `{row.get('upper_bound')}`"
                )
                lines += ["", "| t (s) | LB | UB | event | worker |", "|---:|---:|---:|---|---|"]
                if trajectory:
                    # Keep reports readable while retaining the full JSONL trace.
                    for point in trajectory[:40]:
                        lines.append(f"| {point.get('time', '—')} | {point.get('lb', '—')} | {point.get('ub', '—')} | {point.get('event', '—')} | {point.get('worker', '—')} |")
                    if len(trajectory) > 40:
                        lines.append(f"| … | … | … | {len(trajectory) - 40} additional trace events in raw JSONL | … |")
                else:
                    lines.append("| — | — | — | no trace events recorded | — |")
    # Aggregate baseline/parallel comparison and ablations, separately for each
    # tier so a smoke run cannot dilute the calibrated evaluation.
    for compare_tier in ("eval", "hard"):
        tier_rows = by_tier.get(compare_tier, [])
        if not tier_rows:
            continue
        lines += [f"## Aggregate comparison ({compare_tier})", "", "Values use completed records in this tier. `wall/config ÷ wall/sequential` is a descriptive paired ratio; it is not a claim of causal speedup.", ""]
        agg: dict[str, list[dict[str, Any]]] = defaultdict(list)
        by_pair: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
        for row in tier_rows:
            config = str(row.get("configuration"))
            agg[config].append(row)
            by_pair[(str(row.get("instance")), config)].append(row)
        lines += ["| configuration | runs | median wall (s) | median time-to-best (s) | optimal claims | certified claims |", "|---|---:|---:|---:|---:|---:|"]
        for config in requested.get("configs", []):
            rows = agg.get(config, [])
            walls = [float(r["wall_seconds"]) for r in rows if r.get("wall_seconds") is not None]
            bests = [float(r["time_to_best"]) for r in rows if r.get("time_to_best") is not None]
            opt = sum(bool(r.get("optimal_proven")) for r in rows)
            cert = sum(r.get("certificate_verified") is True for r in rows)
            lines.append(f"| `{config}` | {len(rows)} | {_fmt(statistics.median(walls) if walls else None)} | {_fmt(statistics.median(bests) if bests else None)} | {opt} | {cert} |")
        seq_by_instance = {
            instance: statistics.median(float(r["wall_seconds"]) for r in rows if r.get("wall_seconds") is not None)
            for (instance, config), rows in by_pair.items()
            if config == "sequential" and any(r.get("wall_seconds") is not None for r in rows)
        }
        lines += ["", "### Paired wall-time ratios versus sequential", "", "| configuration | paired instances | median config/sequential | range |", "|---|---:|---:|---:|"]
        for config in ("parallel-4", "parallel-8", "no-backbone-4", "no-mss-4", "no-zopt-4", "z3-optimize"):
            ratios: list[float] = []
            for (instance, current), rows in by_pair.items():
                if current != config or instance not in seq_by_instance:
                    continue
                walls = [float(r["wall_seconds"]) for r in rows if r.get("wall_seconds") is not None]
                if walls and seq_by_instance[instance] > 0:
                    ratios.append(statistics.median(walls) / seq_by_instance[instance])
            lines.append(f"| `{config}` | {len(ratios)} | {_fmt(statistics.median(ratios) if ratios else None)} | {(_fmt(min(ratios)) + '–' + _fmt(max(ratios))) if ratios else '—'} |")
        lines += ["", "### Ablation deltas versus parallel-4", "", "The paired deltas below use median wall time per instance where both records exist; positive means the ablation is slower than the full four-role portfolio.", "", "| ablation | paired instances | median (ablation - parallel-4) seconds |", "|---|---:|---:|"]
        full_by_instance = {
            instance: statistics.median(float(r["wall_seconds"]) for r in rows if r.get("wall_seconds") is not None)
            for (instance, config), rows in by_pair.items()
            if config == "parallel-4" and any(r.get("wall_seconds") is not None for r in rows)
        }
        for config in ("no-backbone-4", "no-mss-4", "no-zopt-4"):
            deltas: list[float] = []
            for (instance, current), rows in by_pair.items():
                if current != config or instance not in full_by_instance:
                    continue
                walls = [float(r["wall_seconds"]) for r in rows if r.get("wall_seconds") is not None]
                if walls:
                    deltas.append(statistics.median(walls) - full_by_instance[instance])
            lines.append(f"| `{config}` | {len(deltas)} | {_fmt(statistics.median(deltas) if deltas else None)} |")
        lines.append("")
    lines += ["### Interpretation", "", "The tables are descriptive, not a claim of a speedup. Compare medians and ranges on the same instance; timeout and missing records remain visible. The prototype is expected to lose to tuned native `z3-optimize` on many cases. Ablation deltas should be read as evidence about bound sharing and role usefulness, not as statistically powered conclusions. An OPTIMAL prototype claim without an independent certificate is an anomaly and is listed in the raw record.", ""]
    out.write_text("\n".join(lines), encoding="utf-8")
    return out


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="run isolated empirical MaxSMT evaluations")
    parser.add_argument("--tier", choices=("smoke", "eval", "hard", "public", "all"), default="eval")
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--max-total", type=float, default=5400.0, help="hard wall cap in seconds (0 disables cap)")
    parser.add_argument("--configs", default=",".join(CONFIGS), help="comma-separated configuration names")
    parser.add_argument("--seeds", default=None, help="comma-separated fixed seeds; defaults to 20260813,20260814,20260815")
    parser.add_argument("--max-instances", type=int, default=None)
    parser.add_argument("--limit-runs", type=int, default=None, help="debug/partial run limit; report it explicitly")
    parser.add_argument("--no-resume", action="store_true")
    parser.add_argument("--report-only", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] == "--z3-child":
        return _z3_child(argv[1:])
    args = build_parser().parse_args(argv)
    RESULTS.mkdir(parents=True, exist_ok=True)
    entries = _read_manifest(args.tier)
    if args.max_instances is not None:
        entries = entries[: max(0, args.max_instances)]
    config_names = [x.strip() for x in args.configs.split(",") if x.strip()]
    unknown = [x for x in config_names if x not in CONFIGS]
    if unknown:
        raise SystemExit(f"unknown configuration(s): {', '.join(unknown)}")
    if args.repeat < 1:
        raise SystemExit("--repeat must be >= 1")
    seeds = tuple(int(x.strip()) for x in args.seeds.split(",") if x.strip()) if args.seeds else SEEDS[: args.repeat]
    if len(seeds) < args.repeat:
        raise SystemExit("--seeds must contain at least --repeat values")
    done = {} if args.no_resume else _load_done(RUNS_PATH)
    all_records = list(done.values())
    if args.report_only:
        write_results_md(all_records, tier=args.tier, requested={"repeat": args.repeat, "timeout": args.timeout, "configs": config_names})
        print(f"report written from {len(all_records)} records")
        return 0
    planned: list[tuple[dict[str, Any], str, int, int]] = []
    for entry in entries:
        for config in config_names:
            for repeat in range(args.repeat):
                seed = seeds[repeat]
                key = _run_key(str(entry["path"]), config, repeat, seed)
                if key not in done:
                    planned.append((entry, config, repeat, seed))
    if args.limit_runs is not None:
        planned = planned[: max(0, args.limit_runs)]
    estimate = sum(_subprocess_limit(entry, args.timeout) for entry, _config, _repeat, _seed in planned)
    print(
        f"tier={args.tier} instances={len(entries)} configs={len(config_names)} repeats={args.repeat} "
        f"pending={len(planned)} per_run_budget={args.timeout:.1f}s estimated_serial_wall={estimate/60:.1f}min "
        f"hard_cap={(args.max_total/60 if args.max_total else 'disabled')}min",
        flush=True,
    )
    if args.max_total and estimate > args.max_total:
        print("WARNING: planned serial estimate exceeds hard cap; runs stop when the cap is reached. Use --limit-runs or --configs to make a bounded design.", flush=True)
    raw_dir = RESULTS / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)
    started_all = time.perf_counter()
    completed_this_call = 0
    with RUNS_PATH.open("a", encoding="utf-8") as stream:
        for entry, config, repeat, seed in planned:
            if args.max_total and time.perf_counter() - started_all >= args.max_total:
                print("hard total-runtime cap reached; leaving remaining runs resumable", flush=True)
                break
            print(f"[{completed_this_call + 1}/{len(planned)}] {entry['path']} :: {config} repeat={repeat} seed={seed}", flush=True)
            record = _execute(entry, config, repeat, seed, args.timeout, raw_dir, str(entry.get("tier", args.tier)))
            stream.write(json.dumps(record, sort_keys=True) + "\n")
            stream.flush()
            done[record["run_key"]] = record
            all_records.append(record)
            completed_this_call += 1
            print(
                f"  status={record['status']} wall={record['wall_seconds']:.3f}s LB={record.get('lower_bound')} UB={record.get('upper_bound')} certified={record.get('certificate_verified')}",
                flush=True,
            )
    report = write_results_md(all_records, tier=args.tier, requested={"repeat": args.repeat, "timeout": args.timeout, "configs": config_names})
    print(f"completed_this_call={completed_this_call} total_records={len(all_records)} report={report}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

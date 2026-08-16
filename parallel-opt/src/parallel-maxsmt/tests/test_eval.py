from __future__ import annotations

import json
from pathlib import Path
import subprocess

from eval import run_eval


def test_killed_child_salvages_trace_bounds_and_uses_size_scaled_margin(
    monkeypatch, tmp_path: Path
):
    entry = {
        "path": "local/eval_random_2sat_u_0.wcnf",
        "tier": "eval",
        "family": "random_2sat",
        "nsoft": 40_000,
        "nhard": 0,
        "measured_seconds": 1.705,
    }
    observed_timeout: list[float] = []

    def killed_run(command, **kwargs):
        observed_timeout.append(float(kwargs["timeout"]))
        trace = Path(command[command.index("--trace") + 1])
        events = [
            {
                "timestamp": 100.0,
                "worker_id": "mss-0",
                "role": "mss",
                "event": "incumbent",
                "lb": 2,
                "ub": 17,
                "status": "RUNNING",
            },
            {
                "timestamp": 101.0,
                "worker_id": "mss-0",
                "role": "mss",
                "event": "incumbent",
                "lb": 3,
                "ub": 12,
                "status": "RUNNING",
            },
        ]
        trace.write_text(
            "".join(json.dumps(event) + "\n" for event in events),
            encoding="utf-8",
        )
        raise subprocess.TimeoutExpired(command, kwargs["timeout"], output="partial\n")

    monkeypatch.setattr(run_eval, "ROOT", tmp_path)
    monkeypatch.setattr(run_eval.subprocess, "run", killed_run)

    record = run_eval._execute(
        entry,
        "parallel-8",
        repeat=0,
        seed=20260813,
        timeout=8.0,
        raw_dir=tmp_path,
        tier="eval",
    )

    assert observed_timeout[0] > 16.0  # the old fixed timeout + 8 seconds
    assert record["harness_killed"] is True
    assert record["status"] == "SAT"
    assert record["lower_bound"] == 3
    assert record["upper_bound"] == 12
    assert record["time_to_first_feasible"] == 0.0
    assert record["time_to_best"] == 1.0
    assert [point["ub"] for point in record["trajectory"]] == [17, 12]


def test_z3_unknown_incumbent_is_recorded_as_feasible_but_not_optimal(
    monkeypatch, tmp_path: Path
):
    entry = {
        "path": "local/hard_set_cover_u_2.wcnf",
        "tier": "hard",
        "family": "set_cover",
        "nsoft": 90,
        "nhard": 540,
    }

    def completed_run(_command, **_kwargs):
        return subprocess.CompletedProcess(
            _command,
            0,
            stdout=json.dumps({"status": "SAT", "cost": 39, "elapsed": 0.1}),
            stderr="",
        )

    monkeypatch.setattr(run_eval, "ROOT", tmp_path)
    monkeypatch.setattr(run_eval.subprocess, "run", completed_run)

    record = run_eval._execute(
        entry,
        "z3-optimize",
        repeat=0,
        seed=20260813,
        timeout=0.1,
        raw_dir=tmp_path,
        tier="hard",
    )

    assert record["status"] == "SAT"
    assert record["upper_bound"] == 39
    assert record["time_to_first_feasible"] == 0.1
    assert record["time_to_best"] == 0.1
    assert record["optimal_proven"] is False

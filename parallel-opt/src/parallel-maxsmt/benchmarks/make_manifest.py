"""Regenerate ``manifest.json`` for local and downloaded public instances."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

import z3
from z3.z3util import get_vars

from parse import ParseError, ParsedProblem, parse_file

ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "manifest.json"
SUPPORTED_SUFFIXES = {".wcnf", ".cnf", ".smt", ".smt2", ".smtlib"}
FAMILY_RE = re.compile(r"(?:^|\s)(?:c|;)\s*family=([^\s]+)")
WEIGHTED_RE = re.compile(r"(?:^|\s)(?:c|;)\s*family=[^\s]+\s+weighted=(true|false)", re.I)


def _metadata(path: Path) -> tuple[str, bool | None]:
    try:
        prefix = "\n".join(path.read_text(encoding="utf-8").splitlines()[:12])
    except (OSError, UnicodeDecodeError):
        return path.parent.name, None
    family_match = FAMILY_RE.search(prefix)
    weighted_match = WEIGHTED_RE.search(prefix)
    family = family_match.group(1) if family_match else path.parent.name
    weighted = None if weighted_match is None else weighted_match.group(1).lower() == "true"
    return family, weighted


def _source_records() -> dict[str, dict[str, Any]]:
    source_file = ROOT / "public" / "SOURCES.json"
    if not source_file.exists():
        return {}
    try:
        records = json.loads(source_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return {str(record.get("path")): record for record in records if isinstance(record, dict)}


def _calibration_records() -> dict[str, dict[str, Any]]:
    """Map ``local/...`` path -> calibration record for the eval/hard tiers.

    These timings and optima are cached here so a manifest rebuild never
    re-runs the (1--60s per instance) Optimize measurements.
    """
    cal_file = ROOT / "calibration.json"
    if not cal_file.exists():
        return {}
    try:
        record = json.loads(cal_file.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return {str(i.get("path")): i for i in record.get("instances", []) if isinstance(i, dict)}


def _integer_value(value: z3.ExprRef) -> int | None:
    if z3.is_int_value(value):
        return value.as_long()
    if z3.is_rational_value(value) and value.denominator_as_long() == 1:
        return value.numerator_as_long()
    return None


def _known_optimum(problem: ParsedProblem, timeout_seconds: float) -> int | None:
    """Compute the minimum violated-soft weight, or None on timeout/error."""
    opt = z3.Optimize(ctx=problem.context)
    opt.set(timeout=max(1, int(timeout_seconds * 1000)))
    if problem.hard:
        opt.add(*problem.hard)
    if problem.soft:
        terms = [z3.If(formula, z3.IntVal(0, ctx=problem.context), z3.IntVal(weight, ctx=problem.context)) for formula, weight in problem.soft]
        objective = z3.Sum(terms)
    else:
        objective = z3.IntVal(0, ctx=problem.context)
    handle = opt.minimize(objective)
    try:
        result = opt.check()
    except z3.Z3Exception:
        return None
    if result != z3.sat:
        return None
    # lower() is the certificate value for an Optimize objective.  A model
    # fallback handles versions that return an algebraic wrapper for lower().
    try:
        value = _integer_value(opt.lower(handle))
    except z3.Z3Exception:
        value = None
    if value is not None:
        return value
    try:
        return _integer_value(opt.model().eval(objective, model_completion=True))
    except z3.Z3Exception:
        return None


def _entry(path: Path, timeout_seconds: float, source_records: dict[str, dict[str, Any]],
           calibration: dict[str, dict[str, Any]]) -> dict[str, Any]:
    relative = path.relative_to(ROOT).as_posix()
    problem = parse_file(path)
    suffix = path.suffix.lower()
    fmt = "smt2" if suffix in {".smt", ".smt2", ".smtlib"} else suffix.lstrip(".")
    family, declared_weighted = _metadata(path)
    source_record = source_records.get(relative)
    if source_record and source_record.get("family"):
        family = str(source_record["family"])
    weighted = declared_weighted if declared_weighted is not None else any(weight != 1 for _, weight in problem.soft)
    variables = set()
    for formula in problem.hard:
        variables.update(str(var) for var in get_vars(formula))
    for formula, _weight in problem.soft:
        variables.update(str(var) for var in get_vars(formula))
    source = source_record.get("url") if source_record else "generated"

    entry: dict[str, Any] = {
        "path": relative,
        "family": family,
        "format": fmt,
        "weighted": bool(weighted),
        "nvars": len(variables),
        "nhard": len(problem.hard),
        "nsoft": len(problem.soft),
        "total_soft_weight": sum(weight for _formula, weight in problem.soft),
        "source": source,
    }

    cal = calibration.get(relative)
    if cal is not None:
        # eval/hard tiers: trust the cached calibration measurement, never
        # re-solve (a hard instance would cost a full timeout here).
        entry["tier"] = cal["tier"]
        entry["known_optimum"] = cal.get("known_optimum")
        entry["measured_seconds"] = cal.get("measured_seconds")
        entry["calibration_seed"] = cal.get("seed")
        if cal["tier"] == "hard":
            entry["best_known_cost"] = cal.get("best_known_cost")
        return entry

    # smoke (generated) and downloaded public instances: measure now; both are
    # either trivial or bounded by the timeout.  Public instances that cannot be
    # closed in time get ``known_optimum: null`` rather than an invented value.
    entry["tier"] = "smoke" if source == "generated" else "public"
    entry["known_optimum"] = _known_optimum(problem, timeout_seconds)
    return entry


def build_manifest(timeout_seconds: float = 60.0) -> list[dict[str, Any]]:
    source_records = _source_records()
    calibration = _calibration_records()
    paths = sorted(
        path
        for directory in (ROOT / "local", ROOT / "public")
        if directory.exists()
        for path in directory.rglob("*")
        if path.is_file() and path.suffix.lower() in SUPPORTED_SUFFIXES and not path.name.endswith(".part")
    )
    entries: list[dict[str, Any]] = []
    for path in paths:
        try:
            entry = _entry(path, timeout_seconds, source_records, calibration)
        except (ParseError, OSError, z3.Z3Exception) as exc:
            # A malformed downloaded instance must be visible to callers rather
            # than silently becoming a manifest row with invented dimensions.
            print(f"SKIP malformed {path.relative_to(ROOT)}: {exc}")
            continue
        entries.append(entry)
        print(
            f"[{entry['tier']:>5}] {entry['path']}: family={entry['family']} format={entry['format']} "
            f"weighted={entry['weighted']} vars={entry['nvars']} hard={entry['nhard']} "
            f"soft={entry['nsoft']} optimum={entry['known_optimum']}"
        )
    MANIFEST.write_text(json.dumps(entries, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {len(entries)} entries to {MANIFEST}")
    # Tier summary: count and measured-time range per tier.
    print("tier summary:")
    for tier in ("smoke", "eval", "hard", "public"):
        rows = [e for e in entries if e.get("tier") == tier]
        if not rows:
            continue
        measured = [e["measured_seconds"] for e in rows if e.get("measured_seconds") is not None]
        families = sorted({e["family"] for e in rows})
        weighted = sum(1 for e in rows if e["weighted"])
        span = f", measured {min(measured):.2f}s..{max(measured):.2f}s" if measured else ""
        print(f"  {tier:>5}: {len(rows)} instances ({weighted} weighted, "
              f"{len(rows) - weighted} unweighted){span}; families={', '.join(families)}")
    return entries


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=60.0, help="per-instance Optimize timeout in seconds (default: 60)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    build_manifest(args.timeout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

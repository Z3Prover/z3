"""Benchmark the native SMT-LIB checker; report coverage, not solver-only passes."""

import argparse
from collections import Counter
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys
import time


VERDICTS = {
    0: ("ACCEPT", r"ACCEPT"),
    1: ("REJECT", r"REJECT"),
    3: ("PARTIAL", r"PARTIAL [1-9][0-9]*"),
    4: ("SAT", r"SAT"),
    5: ("UNKNOWN", r"UNKNOWN .+"),
}
OUTCOMES = (
    "ACCEPT", "PARTIAL", "REJECT", "SAT", "UNKNOWN", "TIMEOUT",
    "ERROR", "CRASH", "PROTOCOL_ERROR", "NOT_RUN",
)
ERRORS = {"ERROR", "CRASH", "PROTOCOL_ERROR"}
STATISTICS = re.compile(
    r"^solve_ms=([\d.]+) marshal_ms=([\d.]+) check_ms=([\d.]+) "
    r"expressions=(\d+) declarations=(\d+) proof_nodes=(\d+)"
    r"(?: semantics=(legacy|sorted-datatype|sorted-core))?$", re.MULTILINE)


def classify(returncode, stdout):
    if returncode == 2:
        return "ERROR"
    if returncode not in VERDICTS:
        return "CRASH"
    outcome, pattern = VERDICTS[returncode]
    return outcome if re.fullmatch(pattern, stdout.strip()) else "PROTOCOL_ERROR"


def discover(corpus, relative_path, max_cases):
    root = (corpus / relative_path).resolve()
    if not root.is_relative_to(corpus) or not root.is_dir():
        raise ValueError("Corpus path must be an existing directory inside the corpus checkout")
    paths = sorted(root.rglob("*.smt2"))
    if not paths:
        raise ValueError(f"No .smt2 files found in {root}")
    if any(not path.resolve().is_relative_to(corpus) for path in paths):
        raise ValueError("Corpus contains an SMT-LIB symlink outside the checkout")
    return paths[:max_cases] if max_cases else paths, len(paths)


def file_sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_manifest(corpus, relative_path, manifest, paths):
    root = (corpus / relative_path).resolve()
    manifest = manifest.resolve()
    if not manifest.is_relative_to(root):
        raise ValueError("Manifest must be inside the selected corpus directory")
    document = json.loads(manifest.read_text(encoding="utf-8"))
    if document["schema_version"] != 1:
        raise ValueError("Unsupported corpus manifest version")
    hashes, logics = {}, {}
    for entry in document["cases"]:
        name = entry["path"]
        if "\\" in name or Path(name).is_absolute():
            raise ValueError(f"Manifest path must be relative and POSIX: {name}")
        path = (root / name).resolve()
        if not path.is_relative_to(root) or not path.is_file() or path.suffix != ".smt2":
            raise ValueError(f"Invalid manifest input: {name}")
        relative = path.relative_to(corpus).as_posix()
        if relative in hashes:
            raise ValueError(f"Duplicate manifest input: {name}")
        if not re.fullmatch(r"[0-9a-f]{64}", entry["sha256"]):
            raise ValueError(f"Invalid SHA-256 in manifest: {name}")
        if file_sha256(path) != entry["sha256"]:
            raise ValueError(f"Input SHA-256 mismatch: {name}")
        hashes[relative], logics[relative] = entry["sha256"], entry["logic"]
    if set(hashes) != {path.relative_to(corpus).as_posix() for path in paths}:
        raise ValueError("Manifest must list exactly the discovered SMT-LIB inputs")
    counts = Counter(logics.values())
    declared = document["per_logic"]
    expected_counts = ({entry["logic"]: declared for entry in document["archives"]}
                       if isinstance(declared, int) else declared)
    if (set(counts) != {entry["logic"] for entry in document["archives"]} or
            dict(counts) != expected_counts):
        raise ValueError("Manifest does not contain the declared sample size per logic")
    return {
        "manifest": {
            "path": manifest.relative_to(corpus).as_posix(),
            "sha256": file_sha256(manifest), "source": document["source"],
            "seed": document["seed"], "per_logic": document["per_logic"],
        },
        "input_sha256": hashes, "logics": logics,
    }


def memory_limit(megabytes):
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (megabytes * 1024**2,) * 2)


def read_log(path):
    with path.open("r", encoding="utf-8", errors="replace") as stream:
        return stream.read(65536)


def run_case(command, path, output, index, timeout, megabytes, log_directory="logs"):
    stem = f"{log_directory}/{index:06d}"
    row = {"path": path, "stdout": stem + ".stdout", "stderr": stem + ".stderr"}
    start = time.perf_counter()
    with (output / row["stdout"]).open("wb") as stdout, (output / row["stderr"]).open("wb") as stderr:
        try:
            result = subprocess.run(
                command, stdout=stdout, stderr=stderr, timeout=timeout,
                preexec_fn=(lambda: memory_limit(megabytes)) if megabytes else None)
            row["returncode"] = result.returncode
        except subprocess.TimeoutExpired:
            row["returncode"] = None
            row["outcome"] = "TIMEOUT"
    row["wall_seconds"] = time.perf_counter() - start
    text = read_log(output / row["stdout"]).strip()
    row["verdict"] = text[:4096]
    if "outcome" not in row:
        row["outcome"] = classify(row["returncode"], text)
    if row["outcome"] == "UNKNOWN":
        row["reason"] = text.removeprefix("UNKNOWN ")
    match = STATISTICS.search(read_log(output / row["stderr"]))
    if match:
        row["statistics"] = dict(zip(
            ("solve_ms", "marshal_ms", "check_ms", "expressions", "declarations", "proof_nodes"),
            [float(value) for value in match.groups()[:3]] +
            [int(value) for value in match.groups()[3:6]]))
        if match[7]:
            row["statistics"]["semantics"] = match[7]
    return row


def run_suite(args):
    corpus = args.corpus.resolve()
    paths, discovered = discover(corpus, args.corpus_path, 0)
    manifest = getattr(args, "manifest", None)
    metadata = verify_manifest(corpus, args.corpus_path, manifest, paths) if manifest else {}
    if args.max_cases:
        paths = paths[:args.max_cases]
    if getattr(args, "expected_cases", 0) and len(paths) != args.expected_cases:
        raise ValueError(f"Expected {args.expected_cases} inputs, selected {len(paths)}")
    checker = args.checker.expanduser().resolve()
    if args.memory_limit_mb and sys.platform != "linux":
        raise ValueError("The address-space limit requires Linux; use --memory-limit-mb 0 elsewhere")
    version = subprocess.run([str(checker), "--version"], check=True, capture_output=True,
                             text=True, timeout=10).stdout.strip()
    output = args.output
    (output / "logs").mkdir(parents=True, exist_ok=True)
    selection = {
        "corpus_path": args.corpus_path, "corpus_commit": args.corpus_commit,
        "z3_commit": os.environ.get("GITHUB_SHA", ""),
        "checker_version": version, "discovered": discovered,
        "paths": [path.relative_to(corpus).as_posix() for path in paths],
        "solver_timeout_ms": args.solver_timeout_ms,
        "case_timeout_seconds": args.case_timeout_seconds,
        "total_timeout_seconds": args.total_timeout_seconds,
        "memory_limit_mb": args.memory_limit_mb,
        **metadata,
    }
    (output / "selection.json").write_text(json.dumps(selection, indent=2) + "\n", encoding="utf-8")
    if manifest:
        (output / "input-manifest.json").write_bytes(manifest.read_bytes())
    deadline = time.perf_counter() + args.total_timeout_seconds
    outcomes = Counter()
    with (output / "results.jsonl").open("w", encoding="utf-8") as stream:
        for index, (path, relative) in enumerate(zip(paths, selection["paths"])):
            remaining = deadline - time.perf_counter()
            if remaining <= 0:
                row = {"path": relative, "outcome": "NOT_RUN", "reason": "Total time budget exhausted"}
            else:
                row = run_case(
                    [str(checker), "--stats", "--timeout-ms", str(args.solver_timeout_ms), str(path)],
                    relative, output, index, min(args.case_timeout_seconds, remaining),
                    args.memory_limit_mb)
            if metadata:
                row["logic"] = metadata["logics"][relative]
                row["input_sha256"] = metadata["input_sha256"][relative]
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            outcomes[row["outcome"]] += 1
            print(f'{index + 1}/{len(paths)} {row["outcome"]}: {relative}', flush=True)
    return int(any(outcomes[outcome] for outcome in ERRORS) or
               outcomes["NOT_RUN"] == len(paths) or (bool(manifest) and outcomes["NOT_RUN"] > 0))


def percentage(count, total):
    return f"{100 * count / total:.1f}%" if total else "n/a"


def cell(value):
    return str(value).replace("|", "\\|").replace("`", "'").replace("\n", " ").replace("\r", " ")


def read_diagnostics(path):
    summary, obligations = None, []
    with path.open(encoding="utf-8", errors="replace") as stream:
        for line in stream:
            fields = line.rstrip("\n").split("\t")
            if fields[:2] == ["diagnostic", "checked"] and len(fields) == 4:
                summary = {"pending": int(fields[2].removeprefix("pending=")),
                           "families": int(fields[3].removeprefix("families="))}
            elif fields[:2] == ["diagnostic", "rejected"]:
                return {"rejection": fields[2:]}
            elif fields[0] == "obligation" and len(fields) == 5:
                obligations.append({"rule": fields[1], "count": int(fields[2]),
                                    "first_index": int(fields[3]), "fingerprint": fields[4]})
    if summary is None:
        raise ValueError("Missing checker diagnostic summary")
    if (summary["families"] != len(obligations) or
            len({(item["rule"], item["fingerprint"]) for item in obligations}) != len(obligations) or
            summary["pending"] != sum(item["count"] for item in obligations) or
            any(item["count"] <= 0 or item["first_index"] < 0 for item in obligations)):
        raise ValueError("Inconsistent checker diagnostic obligation counts")
    return {**summary, "obligations": obligations}


def read_results(path):
    results, warnings = [], []
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    for index, line in enumerate(lines):
        try:
            results.append(json.loads(line))
        except json.JSONDecodeError:
            if index != len(lines) - 1 or line.endswith("\n"):
                raise
            warnings.append(f"Incomplete final record in {path.name} after interruption; raw log retained.")
    return results, warnings


def diagnose(args):
    output = args.output
    selection = json.loads((output / "selection.json").read_text(encoding="utf-8"))
    original, warnings = read_results(output / "results.jsonl")
    for warning in warnings:
        print(warning, file=sys.stderr)
    selected = [row for row in original if row["outcome"] in ("PARTIAL", "REJECT")]
    corpus = args.corpus.resolve()
    checker = args.checker.expanduser().resolve()
    if selection["memory_limit_mb"] and sys.platform != "linux":
        raise ValueError("The address-space limit requires Linux; use a Linux diagnostic runner")
    (output / "diagnostic-logs").mkdir(exist_ok=True)
    deadline = time.perf_counter() + args.total_timeout_seconds
    failed = False
    with (output / "diagnostics.jsonl").open("w", encoding="utf-8") as stream:
        for index, previous in enumerate(selected):
            relative = previous["path"]
            path = (corpus / relative).resolve()
            if not path.is_relative_to(corpus) or not path.is_file():
                raise ValueError(f"Diagnostic input must be inside the corpus: {relative}")
            expected_hash = selection.get("input_sha256", {}).get(relative)
            if expected_hash and file_sha256(path) != expected_hash:
                raise ValueError(f"Diagnostic input SHA-256 mismatch: {relative}")
            remaining = deadline - time.perf_counter()
            if remaining <= 0:
                row = {"path": relative, "outcome": "NOT_RUN",
                       "reason": "Diagnostic budget exhausted"}
            else:
                row = run_case(
                    [str(checker), "--stats", "--diagnostics", "--timeout-ms",
                     str(selection["solver_timeout_ms"]), str(path)],
                    relative, output, index,
                    min(2 * selection["case_timeout_seconds"], remaining),
                    selection["memory_limit_mb"], log_directory="diagnostic-logs")
                row["matches_original"] = row["verdict"] == previous["verdict"]
                if row["outcome"] in ("PARTIAL", "REJECT"):
                    try:
                        row["diagnostics"] = read_diagnostics(output / row["stderr"])
                        if row["outcome"] == "PARTIAL" and (
                                row["diagnostics"].get("pending") != int(row["verdict"].split()[1])):
                            raise ValueError("Diagnostic pending count disagrees with verdict")
                    except ValueError as error:
                        row["diagnostic_error"] = str(error)
                        failed = True
                failed |= row["outcome"] in ERRORS
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            print(f'{index + 1}/{len(selected)} diagnostic {row["outcome"]}: {relative}', flush=True)
    return int(failed)


def obligation_coverage(rows):
    groups = {}
    for row in rows:
        if not row.get("matches_original") or row.get("diagnostic_error"):
            continue
        obligations = row.get("diagnostics", {}).get("obligations", [])
        families = {(item["rule"], item["fingerprint"]) for item in obligations}
        for item in obligations:
            key = item["rule"], item["fingerprint"]
            group = groups.setdefault(key, {
                "rule": key[0], "fingerprint": key[1], "obligations": 0,
                "proofs": 0, "sole_family_proofs": 0, "example": row["path"]})
            group["obligations"] += item["count"]
            group["proofs"] += 1
            group["sole_family_proofs"] += len(families) == 1
    return sorted(groups.values(), key=lambda group: (
        -group["sole_family_proofs"], -group["proofs"], -group["obligations"],
        group["rule"], group["fingerprint"]))


def report(output):
    output.mkdir(parents=True, exist_ok=True)
    selection_path, results_path = output / "selection.json", output / "results.jsonl"
    selection = json.loads(selection_path.read_text(encoding="utf-8")) if selection_path.exists() else {}
    results, warnings = [], []
    if results_path.exists():
        results, warnings = read_results(results_path)
    recorded = {row["path"] for row in results}
    results.extend({"path": path, "outcome": "NOT_RUN", "reason": "Runner stopped before this case",
                    "logic": selection.get("logics", {}).get(path)}
                   for path in selection.get("paths", []) if path not in recorded)
    counts = Counter(row["outcome"] for row in results)
    tested = len(results) - counts["NOT_RUN"]
    times = [row["wall_seconds"] for row in results if "wall_seconds" in row]
    build_path = output / "build.json"
    build = json.loads(build_path.read_text(encoding="utf-8")) if build_path.exists() else {}
    phases = {
        name: sum(row.get("statistics", {}).get(name, 0) for row in results)
        for name in ("solve_ms", "marshal_ms", "check_ms")
    }
    diagnostic_path = output / "diagnostics.jsonl"
    diagnostics = []
    if diagnostic_path.exists():
        diagnostics, diagnostic_warnings = read_results(diagnostic_path)
        warnings.extend(diagnostic_warnings)
    obligations = obligation_coverage(diagnostics)
    summary = {
        "selection": selection, "build": build,
        "build_outcome": os.environ.get("BUILD_OUTCOME", "not recorded"),
        "corpus_outcome": os.environ.get("CORPUS_OUTCOME", "not recorded"),
        "runner_outcome": os.environ.get("RUNNER_OUTCOME", "not recorded"),
        "toolchain_outcome": os.environ.get("TOOLCHAIN_OUTCOME", "not recorded"),
        "harness_outcome": os.environ.get("HARNESS_OUTCOME", "not recorded"),
        "selected": len(results), "tested": tested,
        "counts": {outcome: counts[outcome] for outcome in OUTCOMES},
        "success_rate": counts["ACCEPT"] / tested if tested else None,
        "uncertified_rate": (tested - counts["ACCEPT"]) / tested if tested else None,
        "wall_seconds": sum(times),
        "median_seconds": statistics.median(times) if times else None,
        "p95_seconds": sorted(times)[math.ceil(0.95 * len(times)) - 1] if times else None,
        "phase_totals_ms": phases,
        "phase_statistics_cases": sum("statistics" in row for row in results),
        "warnings": warnings,
        "diagnostic_counts": dict(Counter(row["outcome"] for row in diagnostics)),
        "diagnostic_errors": sum("diagnostic_error" in row for row in diagnostics),
        "diagnostic_mismatches": sum(row.get("matches_original") is False for row in diagnostics),
        "obligation_families": obligations,
        "unknown_reasons": dict(Counter(row.get("reason", row.get("verdict", "not recorded"))
                                        for row in results if row["outcome"] == "UNKNOWN")),
        "per_logic": {
            logic: {
                "selected": sum(row.get("logic") == logic for row in results),
                "counts": {outcome: sum(row.get("logic") == logic and row["outcome"] == outcome
                                       for row in results) for outcome in OUTCOMES},
            } for logic in sorted({row["logic"] for row in results if row.get("logic")})
        },
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    with (output / "results.csv").open("w", newline="", encoding="utf-8") as stream:
        fields = ("path", "logic", "input_sha256", "outcome", "wall_seconds",
                  "returncode", "verdict", "reason")
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(results)
    lines = [
        f'# Pulse verification and native F* checker regressions: '
        f'{cell(selection.get("corpus_path", "no selection"))}', "",
        "**Scope:** the build verifies the in-memory Pulse checkers and their regressions. "
        "The SMT-LIB corpus executes the native extracted F* checker; Pulse is not linked into that executable.",
        "Build self-tests cover Pulse equality/rewriter, justification, and Farkas checkers; "
        "resolution and polynomial-certificate regressions; and native bridge/CLI tests.",
        "Only `ACCEPT` certifies an obligation-free closed refutation. `PARTIAL`, `REJECT`, "
        "`SAT`, and `UNKNOWN` are never counted as proof-checking successes.", "",
        f'- Build and self-tests: **{cell(summary["build_outcome"])}**; '
        f'corpus checkout: **{cell(summary["corpus_outcome"])}**; '
        f'regression runner: **{cell(summary["runner_outcome"])}**.',
        f'- Toolchain setup: **{cell(summary["toolchain_outcome"])}**; '
        f'harness tests: **{cell(summary["harness_outcome"])}**; '
        f'F*: `{cell(build.get("fstar_version", "not recorded"))}`; '
        f'OCaml: `{cell(build.get("ocaml_version", "not recorded"))}`.',
        f'- Build wall time: {build.get("wall_seconds", "not recorded")} seconds.',
        f'- Z3 commit: `{cell(selection.get("z3_commit", os.environ.get("GITHUB_SHA", "")))}`; '
        f'checker producer version: `{cell(selection.get("checker_version", "not recorded"))}`.',
        f'- Corpus commit: `{cell(selection.get("corpus_commit", "not recorded"))}`; '
        f'path: `{cell(selection.get("corpus_path", "not recorded"))}`.',
        f'- Discovered: {selection.get("discovered", 0)}; selected: {len(results)}; '
        f'attempted: {tested}; not run: {counts["NOT_RUN"]}.',
        f'- Proof-checking success rate: **{percentage(counts["ACCEPT"], tested)}**; '
        f'uncertified/failure rate: **{percentage(tested - counts["ACCEPT"], tested)}** '
        "(denominator: all attempted files, including SAT and unknown).",
        f'- Solver timeout: {selection.get("solver_timeout_ms", "n/a")} ms; '
        f'whole-case timeout: {selection.get("case_timeout_seconds", "n/a")} s; '
        f'total test budget: {selection.get("total_timeout_seconds", "n/a")} s; '
        f'address-space limit: {selection.get("memory_limit_mb", "n/a")} MiB (0 = unlimited).', "",
        "| Outcome | Files | Rate among attempted |",
        "|---|---:|---:|",
    ]
    for outcome in OUTCOMES:
        lines.append(f'| {outcome} | {counts[outcome]} | '
                     f'{percentage(counts[outcome], tested) if outcome != "NOT_RUN" else "not attempted"} |')
    if summary["unknown_reasons"]:
        lines += ["", "Solver UNKNOWN reasons (separate from whole-case timeouts and process errors):",
                  "", "| Reason | Files |", "|---|---:|"]
        for reason, count in sorted(summary["unknown_reasons"].items()):
            lines.append(f"| {cell(reason)} | {count} |")
    if "manifest" in selection:
        manifest = selection["manifest"]
        sizes = manifest["per_logic"]
        sample_size = (f"{sizes} inputs per logic" if isinstance(sizes, int) else
                       ", ".join(f"{logic}: {count}" for logic, count in sorted(sizes.items()))
                       + " inputs")
        lines += ["", f'Input manifest: `{cell(manifest["path"])}`; '
                  f'SHA-256: `{manifest["sha256"]}`. '
                  f'Seed {manifest["seed"]}; {sample_size}. '
                  "Every input SHA-256 was verified before executing any case."]
    if summary["per_logic"]:
        lines += ["", "## Per-logic coverage", "",
                  "| Logic | Selected | ACCEPT | PARTIAL | REJECT | SAT | UNKNOWN | TIMEOUT | Errors/crashes/protocol | NOT_RUN |",
                  "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|"]
        for logic, group in summary["per_logic"].items():
            values = group["counts"]
            lines.append(f'| {cell(logic)} | {group["selected"]} | '
                         + " | ".join(str(values[outcome]) for outcome in
                                      ("ACCEPT", "PARTIAL", "REJECT", "SAT", "UNKNOWN", "TIMEOUT"))
                         + f' | {sum(values[outcome] for outcome in ERRORS)} | {values["NOT_RUN"]} |')
    if not selection:
        lines += ["", "**No corpus selection was recorded; no test success is claimed.**"]
    for warning in warnings:
        lines += ["", f"**Warning:** {warning}"]
    if times:
        lines += ["", "## Timing", "",
                  f'Total case wall time: {sum(times):.3f} s; median: {summary["median_seconds"]:.3f} s; '
                  f'p95 (nearest rank): {summary["p95_seconds"]:.3f} s.',
                  f'Stats available for {summary["phase_statistics_cases"]}/{tested} attempted files. '
                  f'Phase totals for those files only: solve {phases["solve_ms"]:.3f} ms, '
                  f'marshal {phases["marshal_ms"]:.3f} ms, check {phases["check_ms"]:.3f} ms. '
                  "SAT, unknown, and interrupted runs may have no phase statistics."]
    if diagnostic_path.exists():
        lines += ["", "## Remaining obligation families", "",
                  "Separate diagnostic replays do not change coverage verdicts or measured case timings. "
                  "Only matching replays with consistent diagnostics contribute to this ranking. "
                  "A fingerprint is a diagnostic shape, not a certificate or proof of equivalence.",
                  f'Diagnostic outcomes: {cell(json.dumps(summary["diagnostic_counts"], sort_keys=True))}; '
                  f'errors: {summary["diagnostic_errors"]}; '
                  f'nonmatching replays: {summary["diagnostic_mismatches"]}.', "",
                  "| Rule | Fingerprint | Sole-family proofs | Proofs | Obligations | Example |",
                  "|---|---|---:|---:|---:|---|"]
        for group in obligations[:30]:
            lines.append(f'| {cell(group["rule"])} | {cell(group["fingerprint"])} | '
                         f'{group["sole_family_proofs"]} | {group["proofs"]} | '
                         f'{group["obligations"]} | {cell(group["example"])} |')
    lines += ["", "## Per-file results (first 100; full list in results.csv)", "",
              "| File | Outcome | Wall seconds |", "|---|---|---:|"]
    for row in results[:100]:
        elapsed = f'{row["wall_seconds"]:.3f}' if "wall_seconds" in row else "-"
        lines.append(f'| {cell(row["path"])} | {row["outcome"]} | {elapsed} |')
    lines += ["", "Inputs are recursively selected `.smt2` files, in sorted order, without modification. "
              "An optional JSON manifest verifies membership and input hashes; it is not executed. "
              "Manifest `.txt` lists and pre-generated `.proof` files are not executed. The native API "
              "checks the parsed final assertion set, not an incremental command transcript. "
              "These are coverage measurements of current proof production/checking, not validation "
              "of z3test's other proof backends or unconditional SMT-LIB soundness.",
              "Logs, incremental results.jsonl, results.csv, selection.json, and summary.json "
              "are retained as artifacts. Timeouts and unsupported/partial proofs are measurements; "
              "build/self-test failures, errors, crashes, and protocol mismatches fail the workflow.", ""]
    (output / "report.md").write_text("\n".join(lines), encoding="utf-8")


def positive_float(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return number


def nonnegative_int(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def solver_timeout(value):
    number = int(value)
    if not 0 < number <= 4294967295:
        raise argparse.ArgumentTypeError("must be between 1 and 4294967295")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    run = commands.add_parser("run")
    run.add_argument("--checker", type=Path, required=True)
    run.add_argument("--corpus", type=Path, required=True)
    run.add_argument("--corpus-path", default="regressions/proofs")
    run.add_argument("--corpus-commit", required=True)
    run.add_argument("--manifest", type=Path, help="Verify all inputs against this corpus JSON manifest")
    run.add_argument("--expected-cases", type=nonnegative_int, default=0)
    run.add_argument("--max-cases", type=nonnegative_int, default=0)
    run.add_argument("--solver-timeout-ms", type=solver_timeout, default=10000)
    run.add_argument("--case-timeout-seconds", type=positive_float, default=60)
    run.add_argument("--total-timeout-seconds", type=positive_float, default=1800)
    run.add_argument("--memory-limit-mb", type=nonnegative_int, default=0)
    run.add_argument("--output", type=Path, required=True)
    summarize = commands.add_parser("report")
    summarize.add_argument("--output", type=Path, required=True)
    diagnostic = commands.add_parser("diagnose", help="Separately replay PARTIAL/REJECT cases with diagnostics")
    diagnostic.add_argument("--checker", type=Path, required=True)
    diagnostic.add_argument("--corpus", type=Path, required=True)
    diagnostic.add_argument("--output", type=Path, required=True)
    diagnostic.add_argument("--total-timeout-seconds", type=positive_float, default=900)
    args = parser.parse_args()
    if args.command == "report":
        report(args.output)
        return 0
    if args.command == "diagnose":
        return diagnose(args)
    return run_suite(args)


if __name__ == "__main__":
    sys.exit(main())

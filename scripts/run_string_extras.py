#!/usr/bin/env python3
# Copyright (c) 2026 Microsoft Corporation
# SPDX-License-Identifier: MIT
"""Run the checked-in string benchmark sample with model validation."""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def load_corpus(corpus):
    manifest = json.loads((corpus / "manifest.json").read_text(encoding="utf-8"))
    entries = manifest["benchmarks"]
    paths = [entry["file"] for entry in entries]
    actual = {path.relative_to(corpus).as_posix() for path in corpus.rglob("*.smt2")}
    if not paths or len(paths) != len(set(paths)) or set(paths) != actual:
        raise ValueError("manifest must list every benchmark exactly once")
    for entry in entries:
        path = (corpus / entry["file"]).resolve()
        if not path.is_relative_to(corpus.resolve()):
            raise ValueError("benchmark path escapes corpus")
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            raise ValueError(f"benchmark checksum mismatch: {entry['file']}")
    return manifest


def classify(stdout, stderr, returncode, baseline):
    if re.search(r"invalid model|model validation fail", stdout + "\n" + stderr, re.IGNORECASE):
        return "model-validation-failure", True
    if returncode or "(error" in stdout or "(error" in stderr:
        return "error", True
    answers = re.findall(r"^(sat|unsat|unknown|timeout)\s*$", stdout, re.MULTILINE)
    status = answers[-1] if answers else "no-result"
    if status == "timeout":
        return status, False
    failed = status not in ("sat", "unsat")
    if baseline in ("sat", "unsat"):
        failed |= status != baseline
    return status, failed


def run_case(binary, corpus, entry, options, output):
    command = [str(binary), "-smt2", "-st", *options, str(corpus / entry["file"])]
    start = time.monotonic()
    try:
        result = subprocess.run(command, capture_output=True, text=True,
                                encoding="utf-8", errors="replace", timeout=15)
        stdout, stderr, returncode = result.stdout, result.stderr, result.returncode
        status, failed = classify(stdout, stderr, returncode, entry["baseline"])
    except subprocess.TimeoutExpired as error:
        stdout = (error.stdout or b"").decode("utf-8", errors="replace")
        stderr = (error.stderr or b"").decode("utf-8", errors="replace")
        returncode = None
        status, failed = classify(stdout + "\ntimeout\n", stderr, returncode, entry["baseline"])
    log = output / Path(entry["file"]).with_suffix(".log")
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text(stdout + "\n--- stderr ---\n" + stderr, encoding="utf-8")
    return {**entry, "status": status, "failed": failed, "returncode": returncode,
            "seconds": round(time.monotonic() - start, 6)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--corpus", type=Path,
                        default=Path(__file__).resolve().parents[1] / "benchmarks" / "string-extras")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    manifest = load_corpus(args.corpus)
    args.output.mkdir(parents=True, exist_ok=True)
    version = subprocess.check_output([str(args.binary.resolve()), "--version"], text=True).strip()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda entry: run_case(args.binary.resolve(), args.corpus.resolve(),
                                                     entry, manifest["options"], args.output),
                                manifest["benchmarks"]))
    failures = [entry for entry in results if entry["failed"]]
    model_failures = [entry for entry in failures if entry["status"] == "model-validation-failure"]
    counts = Counter(entry["status"] for entry in results)
    (args.output / "results.json").write_text(json.dumps({
        "version": version, "options": manifest["options"],
        "source_revision": manifest["revision"], "results": results,
    }, indent=2) + "\n", encoding="utf-8")
    summary = ["# String-extras benchmarks", "", version, "",
               f"Ran {len(results)} benchmarks; **{len(failures)} failures**.", "",
               ", ".join(f"{key}: {counts[key]}" for key in sorted(counts)), "",
               "Options: `" + " ".join(manifest["options"]) + "`", "",
               f"**{len(model_failures)} model validation failures**. "
               f"{counts['timeout']} timeouts (not failures).", "",
               "The 24 historical errors are not exempted from failure checks.", ""]
    if model_failures:
        summary += ["## Model validation failures", "",
                    "| Benchmark | Log |", "| --- | --- |"]
        summary += [f"| `{entry['source']}` | `{Path(entry['file']).with_suffix('.log').as_posix()}` |"
                    for entry in model_failures]
        summary += ["", "## All failures", ""]
    if failures:
        summary += ["| Benchmark | Baseline | Result |", "| --- | --- | --- |"]
        summary += [f"| `{entry['source']}` | {entry['baseline']} | {entry['status']} |"
                    for entry in failures]
    text = "\n".join(summary) + "\n"
    (args.output / "summary.md").write_text(text, encoding="utf-8")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
            stream.write(text)
    print(f"Ran {len(results)} benchmarks: {dict(counts)}; {len(failures)} failures")
    return bool(failures)


if __name__ == "__main__":
    raise SystemExit(main())

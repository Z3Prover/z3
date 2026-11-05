#!/usr/bin/env python3
# Copyright (c) 2026 Microsoft Corporation
# SPDX-License-Identifier: MIT
"""Run the Z3 determinism linter in one pass per translation unit."""
import argparse
import concurrent.futures
import json
import os
import pathlib
import re
import subprocess
import time
from affected import compilation_units, selection_id
from checks import CHECKS

VERSION = "21.1.8"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", choices=CHECKS, action="append",
                        help="select a check (repeatable); defaults to all Z3 checks")
    parser.add_argument("--clang-tidy", default="clang-tidy-21")
    parser.add_argument("--plugin", required=True, type=pathlib.Path)
    parser.add_argument("--build", required=True, type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    parser.add_argument("--source-root", type=pathlib.Path,
                        help="report only warnings under this checkout, using relative paths")
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    parser.add_argument("--filter", default=r"/src/", help="regex selecting source paths")
    parser.add_argument("--selection", type=pathlib.Path, help="PR selection produced by affected.py")
    parser.add_argument("--revision", choices=["base", "head"], help="side of the PR selection to scan")
    args = parser.parse_args()
    checks = sorted(set(args.check or CHECKS))
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if bool(args.selection) != bool(args.revision) or args.selection and not args.source_root:
        parser.error("--selection requires --revision and --source-root")
    version = subprocess.check_output([args.clang_tidy, "--version"], text=True)
    if not re.search(r"version " + re.escape(VERSION) + r"\b", version):
        parser.error(f"expected clang-tidy {VERSION}, got {version.strip()}")

    config = json.dumps({"Checks": "-*," + ",".join(checks), "WarningsAsErrors": "", "HeaderFilterRegex": ".*"})
    command = [args.clang_tidy, "--load=" + str(args.plugin.resolve()), "--config=" + config]
    # Fail clearly if the plugin was not loaded; unknown check globs can
    # otherwise silently select no checks.
    available = subprocess.check_output(command + ["--list-checks"], text=True)
    for check in checks:
        if check not in available.split():
            parser.error("plugin did not register " + check)
    database = json.loads((args.build / "compile_commands.json").read_text())
    sources = sorted({str((pathlib.Path(entry["directory"]) / entry["file"]).resolve())
                      for entry in database})
    sources = [source for source in sources if re.search(args.filter, source)]
    scope = None
    if args.selection:
        plan = json.loads(args.selection.read_text())
        units = compilation_units(args.source_root, args.build, args.filter)
        selected = plan[args.revision]
        keys = selected["sources"]
        if (plan["schema_version"] != 1 or plan["mode"] not in {"affected", "full"} or
                selected["total"] != len(units) or len(keys) != len(set(keys)) or
                not set(keys) <= units.keys() or plan["mode"] == "full" and set(keys) != units.keys()):
            parser.error("selection does not match the compilation database")
        sources = [units[key][0]["file"] for key in keys]
        scope = {"mode": plan["mode"], "selection_id": selection_id(plan), "revision": args.revision,
                 "selected": len(sources), "total": len(units)}
    if not sources and not scope:
        parser.error("no translation units selected")
    args.output.mkdir(parents=True, exist_ok=True)
    if args.selection:
        (args.output / "selection.json").write_text(args.selection.read_text())
    scan_start = time.monotonic()
    print(f"Checking {len(sources)} translation units with clang-tidy {VERSION} "
          f"using {args.jobs} workers", flush=True)
    print("Enabled checks: " + ", ".join(checks), flush=True)

    def run(item):
        index, source = item
        start = time.monotonic()
        log = args.output / f"{index:04d}-{pathlib.Path(source).name}.log"
        with log.open("w") as out:
            result = subprocess.run(command + ["--use-color=false", "-p", str(args.build.resolve()), source],
                                    stdout=out, stderr=subprocess.STDOUT)
        return {"source": source, "returncode": result.returncode, "log": str(log),
                "seconds": round(time.monotonic() - start, 2)}

    results = []
    warnings = set()
    pattern = re.compile(r"^(.+?):(\d+):(\d+): warning: (.+) \[(" +
                         "|".join(re.escape(check) for check in checks) + r")\]$", re.MULTILINE)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run, item) for item in enumerate(sources)]
        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            results.append(result)
            for path, line, column, message, check in pattern.findall(pathlib.Path(result["log"]).read_text()):
                if args.source_root:
                    try:
                        path = pathlib.Path(path).resolve().relative_to(args.source_root.resolve()).as_posix()
                    except ValueError:
                        continue
                warnings.add((path, line, column, message, check))
            if len(results) % 25 == 0 or result["returncode"] or len(results) == len(sources):
                print(f"{len(results)}/{len(sources)} checked; {len(warnings)} distinct warnings; "
                      f"{sum(r['returncode'] != 0 for r in results)} failed; "
                      f"{time.monotonic() - scan_start:.0f}s elapsed", flush=True)
    failed = sum(result["returncode"] != 0 for result in results)
    summary = {"checks": checks, "clang_tidy_version": version.strip(),
               "jobs": args.jobs, "elapsed_seconds": round(time.monotonic() - scan_start, 2),
               "warning_count": len(warnings), "failed_translation_units": failed,
               "translation_units": sorted(results, key=lambda r: r["source"]),
               "warnings": [{"file": path, "line": int(line), "column": int(column), "message": message,
                             "check": check}
                            for path, line, column, message, check in sorted(
                                warnings, key=lambda w: (w[0], int(w[1]), int(w[2]), w[3], w[4]))]}
    if scope:
        summary["scope"] = scope
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "warnings.txt").write_text("".join(
        f"{w['file']}:{w['line']}:{w['column']}: warning: {w['message']} [{w['check']}]\n"
        for w in summary["warnings"]))
    for check in checks:
        print(f"{check} warnings: {sum(w[4] == check for w in warnings)}", flush=True)
    print(f"Total warnings: {len(warnings)}"
          + (f" (incomplete: {failed} translation units failed)" if failed else ""), flush=True)
    # Warnings are advisory. Compiler errors and checker crashes are failures.
    return int(any(result["returncode"] for result in results))


if __name__ == "__main__":
    raise SystemExit(main())

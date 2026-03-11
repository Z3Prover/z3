#!/usr/bin/env python3
"""
static_analysis.py: run Clang Static Analyzer on Z3 source.

Usage:
    python static_analysis.py --build-dir build
    python static_analysis.py --build-dir build --output-dir /tmp/sa-results
    python static_analysis.py --build-dir build --debug
"""

import argparse
import logging
import os
import plistlib
import shutil
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, setup_logging

logger = logging.getLogger("z3agent")

SCAN_BUILD_NAMES = ["scan-build", "scan-build-14", "scan-build-15", "scan-build-16"]


def find_scan_build() -> str:
    """Locate the scan-build binary on PATH."""
    for name in SCAN_BUILD_NAMES:
        path = shutil.which(name)
        if path:
            logger.debug("found scan-build: %s", path)
            return path
    logger.error(
        "scan-build not found. Install clang-tools or set PATH. "
        "Searched: %s", ", ".join(SCAN_BUILD_NAMES)
    )
    sys.exit(1)


def run_configure(scan_build: str, build_dir: Path, output_dir: Path,
                  timeout: int) -> bool:
    """Run scan-build cmake to configure the project."""
    repo_root = build_dir.parent
    cmd = [
        scan_build,
        "-o", str(output_dir),
        "cmake",
        str(repo_root),
    ]
    logger.info("configuring: %s", " ".join(cmd))
    try:
        proc = subprocess.run(
            cmd, cwd=str(build_dir),
            capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        logger.error("cmake configuration timed out after %ds", timeout)
        return False

    if proc.returncode != 0:
        logger.error("cmake configuration failed (exit %d)", proc.returncode)
        logger.error("stderr: %s", proc.stderr[:2000])
        return False

    logger.info("configuration complete")
    return True


def run_build(scan_build: str, build_dir: Path, output_dir: Path,
              timeout: int) -> bool:
    """Run scan-build make to build and analyze."""
    nproc = os.cpu_count() or 4
    cmd = [
        scan_build,
        "-o", str(output_dir),
        "--status-bugs",
        "make",
        f"-j{nproc}",
    ]
    logger.info("building with analysis: %s", " ".join(cmd))
    try:
        proc = subprocess.run(
            cmd, cwd=str(build_dir),
            capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        logger.error("build timed out after %ds", timeout)
        return False

    # scan-build returns nonzero when bugs are found (due to --status-bugs),
    # so a nonzero exit code is not necessarily a build failure.
    if proc.returncode != 0:
        logger.info(
            "scan-build exited with code %d (nonzero may indicate findings)",
            proc.returncode,
        )
    else:
        logger.info("build complete, no bugs reported by scan-build")

    if proc.stderr:
        logger.debug("build stderr (last 2000 chars): %s", proc.stderr[-2000:])
    return True


def collect_plist_files(output_dir: Path) -> list:
    """Recursively find all .plist diagnostic files under the output directory."""
    plists = sorted(output_dir.rglob("*.plist"))
    logger.debug("found %d plist files in %s", len(plists), output_dir)
    return plists


def parse_plist_findings(plist_path: Path) -> list:
    """Extract findings from a single Clang plist diagnostic file.

    Returns a list of dicts with keys: file, line, col, category, type, description.
    """
    findings = []
    try:
        with open(plist_path, "rb") as f:
            data = plistlib.load(f)
    except Exception as exc:
        logger.warning("could not parse %s: %s", plist_path, exc)
        return findings

    source_files = data.get("files", [])
    for diag in data.get("diagnostics", []):
        location = diag.get("location", {})
        file_idx = location.get("file", 0)
        source_file = source_files[file_idx] if file_idx < len(source_files) else "<unknown>"
        findings.append({
            "file": source_file,
            "line": location.get("line", 0),
            "col": location.get("col", 0),
            "category": diag.get("category", "uncategorized"),
            "type": diag.get("type", ""),
            "description": diag.get("description", ""),
        })
    return findings


def collect_all_findings(output_dir: Path) -> list:
    """Parse every plist file under output_dir and return merged findings."""
    all_findings = []
    for plist_path in collect_plist_files(output_dir):
        all_findings.extend(parse_plist_findings(plist_path))
    return all_findings


def log_findings(db, run_id: int, findings: list):
    """Persist each finding to z3agent.db."""
    for f in findings:
        db.log_finding(
            run_id,
            category=f["category"],
            message=f["description"],
            severity=f.get("type"),
            file=f["file"],
            line=f["line"],
            details={"col": f["col"], "type": f["type"]},
        )


def print_findings(findings: list):
    """Print individual findings and a category summary."""
    if not findings:
        print("No findings reported.")
        return

    for f in findings:
        label = f["category"]
        if f["type"]:
            label = f["type"]
        print(f"[{label}] {f['file']}:{f['line']}: {f['description']}")

    print()
    counts = Counter(f["category"] for f in findings)
    print(f"Total findings: {len(findings)}")
    print("By category:")
    for cat, cnt in counts.most_common():
        print(f"  {cat}: {cnt}")


def main():
    parser = argparse.ArgumentParser(
        prog="static_analysis",
        description="Run Clang Static Analyzer on Z3 and log findings.",
    )
    parser.add_argument(
        "--build-dir", required=True,
        help="path to the CMake build directory",
    )
    parser.add_argument(
        "--output-dir", default=None,
        help="directory for scan-build results (default: BUILD/scan-results)",
    )
    parser.add_argument(
        "--timeout", type=int, default=1200,
        help="seconds allowed for the full analysis build",
    )
    parser.add_argument("--db", default=None, help="path to z3agent.db")
    parser.add_argument("--debug", action="store_true", help="verbose tracing")
    args = parser.parse_args()

    setup_logging(args.debug)

    scan_build = find_scan_build()

    build_dir = Path(args.build_dir).resolve()
    build_dir.mkdir(parents=True, exist_ok=True)

    output_dir = Path(args.output_dir) if args.output_dir else build_dir / "scan-results"
    output_dir = output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    db = Z3DB(args.db)
    run_id = db.start_run("static-analysis", f"build_dir={build_dir}")
    start = time.monotonic()

    if not run_configure(scan_build, build_dir, output_dir, timeout=args.timeout):
        elapsed = int((time.monotonic() - start) * 1000)
        db.finish_run(run_id, "error", elapsed, exit_code=1)
        db.close()
        sys.exit(1)

    if not run_build(scan_build, build_dir, output_dir, timeout=args.timeout):
        elapsed = int((time.monotonic() - start) * 1000)
        db.finish_run(run_id, "error", elapsed, exit_code=1)
        db.close()
        sys.exit(1)

    elapsed = int((time.monotonic() - start) * 1000)

    findings = collect_all_findings(output_dir)
    log_findings(db, run_id, findings)

    status = "clean" if len(findings) == 0 else "findings"
    db.finish_run(run_id, status, elapsed, exit_code=0)

    db.log(
        f"static analysis complete: {len(findings)} finding(s) in {elapsed}ms",
        run_id=run_id,
    )

    print_findings(findings)

    db.close()
    sys.exit(0)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
memory_safety.py: run sanitizer checks on Z3 test suite.

Usage:
    python memory_safety.py --sanitizer asan
    python memory_safety.py --sanitizer ubsan --debug
"""

import argparse
import logging
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, setup_logging

logger = logging.getLogger("z3agent")

SANITIZER_FLAGS = {
    "asan": "-fsanitize=address -fno-omit-frame-pointer",
    "ubsan": "-fsanitize=undefined -fno-omit-frame-pointer",
}

ASAN_ERROR = re.compile(r"ERROR:\s*AddressSanitizer:\s*(\S+)")
UBSAN_ERROR = re.compile(r":\d+:\d+:\s*runtime error:\s*(.+)")
LEAK_ERROR = re.compile(r"ERROR:\s*LeakSanitizer:")
LOCATION = re.compile(r"(\S+\.(?:cpp|c|h|hpp)):(\d+)")


def check_dependencies():
    """Fail early if required build tools are not on PATH."""
    missing = []
    if not shutil.which("cmake"):
        missing.append(("cmake", "sudo apt install cmake"))
    if not shutil.which("make"):
        missing.append(("make", "sudo apt install build-essential"))

    cc = shutil.which("clang") or shutil.which("gcc")
    if not cc:
        missing.append(("clang or gcc", "sudo apt install clang"))

    if missing:
        print("required tools not found:", file=sys.stderr)
        for tool, install in missing:
            print(f"  {tool}: {install}", file=sys.stderr)
        sys.exit(1)


def find_repo_root() -> Path:
    d = Path.cwd()
    for _ in range(10):
        if (d / "CMakeLists.txt").exists() and (d / "src").is_dir():
            return d
        parent = d.parent
        if parent == d:
            break
        d = parent
    logger.error("could not locate Z3 repository root")
    sys.exit(1)


def build_is_configured(build_dir: Path, sanitizer: str) -> bool:
    """Check whether the build directory already has a matching cmake config."""
    cache = build_dir / "CMakeCache.txt"
    if not cache.is_file():
        return False
    expected = SANITIZER_FLAGS[sanitizer].split()[0]
    return expected in cache.read_text()


def configure(build_dir: Path, sanitizer: str, repo_root: Path) -> bool:
    """Run cmake with the requested sanitizer flags."""
    flags = SANITIZER_FLAGS[sanitizer]
    build_dir.mkdir(parents=True, exist_ok=True)
    cmd = [
        "cmake", str(repo_root),
        f"-DCMAKE_C_FLAGS={flags}",
        f"-DCMAKE_CXX_FLAGS={flags}",
        f"-DCMAKE_EXE_LINKER_FLAGS={flags}",
        "-DCMAKE_BUILD_TYPE=Debug",
        "-DZ3_BUILD_TEST=ON",
    ]
    logger.info("configuring %s build in %s", sanitizer, build_dir)
    logger.debug("cmake command: %s", " ".join(cmd))
    proc = subprocess.run(cmd, cwd=build_dir, capture_output=True, text=True)
    if proc.returncode != 0:
        logger.error("cmake failed:\n%s", proc.stderr)
        return False
    return True


def compile_tests(build_dir: Path) -> bool:
    """Compile the test-z3 target."""
    nproc = os.cpu_count() or 4
    cmd = ["make", f"-j{nproc}", "test-z3"]
    logger.info("compiling test-z3 (%d parallel jobs)", nproc)
    proc = subprocess.run(cmd, cwd=build_dir, capture_output=True, text=True)
    if proc.returncode != 0:
        logger.error("compilation failed:\n%s", proc.stderr[-2000:])
        return False
    return True


def run_tests(build_dir: Path, timeout: int) -> dict:
    """Execute test-z3 under sanitizer runtime and capture output."""
    test_bin = build_dir / "test-z3"
    if not test_bin.is_file():
        logger.error("test-z3 not found at %s", test_bin)
        return {"stdout": "", "stderr": "binary not found", "exit_code": -1,
                "duration_ms": 0}

    env = os.environ.copy()
    env["ASAN_OPTIONS"] = "detect_leaks=1:halt_on_error=0:print_stacktrace=1"
    env["UBSAN_OPTIONS"] = "print_stacktrace=1:halt_on_error=0"

    cmd = [str(test_bin), "/a"]
    logger.info("running: %s", " ".join(cmd))
    start = time.monotonic()
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout,
            cwd=build_dir, env=env,
        )
    except subprocess.TimeoutExpired:
        ms = int((time.monotonic() - start) * 1000)
        logger.warning("test-z3 timed out after %dms", ms)
        return {"stdout": "", "stderr": "timeout", "exit_code": -1,
                "duration_ms": ms}

    ms = int((time.monotonic() - start) * 1000)
    logger.debug("exit_code=%d duration=%dms", proc.returncode, ms)
    return {
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "exit_code": proc.returncode,
        "duration_ms": ms,
    }


def parse_findings(output: str) -> list:
    """Extract sanitizer error reports from combined stdout and stderr."""
    findings = []
    lines = output.split("\n")

    for i, line in enumerate(lines):
        entry = None

        m = ASAN_ERROR.search(line)
        if m:
            entry = {"category": "asan", "message": m.group(1),
                     "severity": "high"}

        if not entry:
            m = LEAK_ERROR.search(line)
            if m:
                entry = {"category": "leak",
                         "message": "detected memory leaks",
                         "severity": "high"}

        if not entry:
            m = UBSAN_ERROR.search(line)
            if m:
                entry = {"category": "ubsan", "message": m.group(1),
                         "severity": "medium"}

        if not entry:
            continue

        file_path, line_no = None, None
        window = lines[max(0, i - 2):i + 5]
        for ctx in window:
            loc = LOCATION.search(ctx)
            if loc and "/usr/" not in loc.group(1):
                file_path = loc.group(1)
                line_no = int(loc.group(2))
                break

        entry["file"] = file_path
        entry["line"] = line_no
        entry["raw"] = line.strip()
        findings.append(entry)

    return findings


def deduplicate(findings: list) -> list:
    """Remove duplicate reports at the same category, file, and line."""
    seen = set()
    result = []
    for f in findings:
        key = (f["category"], f["file"], f["line"], f["message"])
        if key in seen:
            continue
        seen.add(key)
        result.append(f)
    return result


def main():
    parser = argparse.ArgumentParser(prog="memory-safety")
    parser.add_argument("--sanitizer", choices=["asan", "ubsan", "both"],
                        default="asan",
                        help="sanitizer to enable (default: asan)")
    parser.add_argument("--build-dir", default=None,
                        help="path to build directory")
    parser.add_argument("--timeout", type=int, default=600,
                        help="seconds before killing test run")
    parser.add_argument("--skip-build", action="store_true",
                        help="reuse existing instrumented build")
    parser.add_argument("--db", default=None,
                        help="path to z3agent.db")
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    setup_logging(args.debug)
    check_dependencies()
    repo_root = find_repo_root()

    sanitizers = ["asan", "ubsan"] if args.sanitizer == "both" else [args.sanitizer]
    all_findings = []

    db = Z3DB(args.db)

    for san in sanitizers:
        if args.build_dir:
            build_dir = Path(args.build_dir)
        else:
            build_dir = repo_root / "build" / f"sanitizer-{san}"

        run_id = db.start_run("memory-safety", f"sanitizer={san}")
        db.log(f"sanitizer: {san}, build: {build_dir}", run_id=run_id)

        if not args.skip_build:
            needs_configure = not build_is_configured(build_dir, san)
            if needs_configure and not configure(build_dir, san, repo_root):
                db.finish_run(run_id, "error", 0, exit_code=1)
                print(f"FAIL: cmake configuration failed for {san}")
                continue
            if not compile_tests(build_dir):
                db.finish_run(run_id, "error", 0, exit_code=1)
                print(f"FAIL: compilation failed for {san}")
                continue

        result = run_tests(build_dir, args.timeout)
        combined = result["stdout"] + "\n" + result["stderr"]
        findings = deduplicate(parse_findings(combined))

        for f in findings:
            db.log_finding(
                run_id,
                category=f["category"],
                message=f["message"],
                severity=f["severity"],
                file=f["file"],
                line=f["line"],
                details={"raw": f["raw"]},
            )

        status = "clean" if not findings else "findings"
        if result["exit_code"] == -1:
            status = "timeout" if "timeout" in result["stderr"] else "error"

        db.finish_run(run_id, status, result["duration_ms"], result["exit_code"])
        all_findings.extend(findings)
        print(f"{san}: {len(findings)} finding(s), {result['duration_ms']}ms")

    if all_findings:
        print(f"\nTotal: {len(all_findings)} finding(s)")
        for f in all_findings:
            loc = f"{f['file']}:{f['line']}" if f["file"] else "unknown location"
            print(f"  [{f['severity']}] {f['category']}: {f['message']} at {loc}")
        db.close()
        sys.exit(1)
    else:
        print("\nNo sanitizer findings.")
        db.close()
        sys.exit(0)


if __name__ == "__main__":
    main()

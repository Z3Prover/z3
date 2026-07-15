#!/usr/bin/env python3
"""Parse ASan/UBSan artifacts from the memory-safety workflow.

Reads the report directory produced by fetch-artifacts.sh, extracts
findings from per-PID log files and stdout captures, writes structured
JSON to /tmp/parsed-report.json.

Usage:
    parse_sanitizer_reports.py [report_dir]

report_dir defaults to /tmp/reports.
"""

import json
import os
import re
import sys
from pathlib import Path

REPORT_DIR = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("/tmp/reports")
OUT = Path("/tmp/parsed-report.json")

ASAN_DIR = REPORT_DIR / "asan-reports"
UBSAN_DIR = REPORT_DIR / "ubsan-reports"

# Patterns for real sanitizer findings (not Z3 internal errors).
ASAN_ERROR = re.compile(
    r"==\d+==ERROR: (AddressSanitizer|LeakSanitizer): (.+)"
)
ASAN_SUMMARY = re.compile(
    r"SUMMARY: (AddressSanitizer|LeakSanitizer): (\d+) byte"
)
UBSAN_ERROR = re.compile(
    r"(.+:\d+:\d+): runtime error: (.+)"
)
# Stack frame: #N 0xADDR in func file:line
STACK_FRAME = re.compile(
    r"\s+#(\d+) 0x[0-9a-f]+ in (.+?) (.+)"
)


def read_text(path):
    if path.is_file():
        return path.read_text(errors="replace")
    return ""


def find_pid_files(directory, prefix):
    """Return paths matching prefix.* (asan.12345, ubsan.67890, etc)."""
    if not directory.is_dir():
        return []
    return sorted(
        p for p in directory.iterdir()
        if p.name.startswith(prefix + ".") and p.name != prefix
    )


def parse_asan_block(text):
    """Pull individual ASan error blocks from a log."""
    findings = []
    current = None

    for line in text.splitlines():
        m = ASAN_ERROR.match(line)
        if m:
            if current:
                findings.append(current)
            current = {
                "tool": m.group(1),
                "type": m.group(2).strip(),
                "location": "",
                "frames": [],
                "raw": line,
            }
            continue

        if current and len(current["frames"]) < 5:
            fm = STACK_FRAME.match(line)
            if fm:
                frame = {"func": fm.group(2), "location": fm.group(3)}
                current["frames"].append(frame)
                if not current["location"] and ":" in fm.group(3):
                    current["location"] = fm.group(3).strip()

    if current:
        findings.append(current)
    return findings


def parse_ubsan_lines(text):
    """Pull UBSan runtime-error lines."""
    findings = []
    seen = set()
    for line in text.splitlines():
        m = UBSAN_ERROR.search(line)
        if m:
            key = (m.group(1), m.group(2))
            if key not in seen:
                seen.add(key)
                findings.append({
                    "tool": "UBSan",
                    "type": m.group(2).strip(),
                    "location": m.group(1).strip(),
                    "raw": line.strip(),
                })
    return findings


def scan_directory(directory, prefix, parse_pid_fn, log_pattern):
    """Scan a report directory and return structured results."""
    summary_text = read_text(directory / "summary.md")
    pid_files = find_pid_files(directory, prefix)

    pid_findings = []
    for pf in pid_files:
        pid_findings.extend(parse_pid_fn(pf.read_text(errors="replace")))

    log_findings = []
    log_hit_count = 0
    for logfile in sorted(directory.glob("*.log")):
        content = logfile.read_text(errors="replace")
        hits = len(log_pattern.findall(content))
        log_hit_count += hits
        log_findings.extend(parse_pid_fn(content))

    # deduplicate log_findings against pid_findings by (type, location)
    pid_keys = {(f["type"], f["location"]) for f in pid_findings}
    unique_log = [f for f in log_findings if (f["type"], f["location"]) not in pid_keys]

    all_findings = pid_findings + unique_log
    files = sorted(p.name for p in directory.iterdir()) if directory.is_dir() else []

    return {
        "summary": summary_text,
        "pid_file_count": len(pid_files),
        "log_hit_count": log_hit_count,
        "findings": all_findings,
        "finding_count": len(all_findings),
        "files": files,
    }


def load_suppressions():
    """Read suppressions from contrib/suppressions/sanitizers/."""
    base = Path("contrib/suppressions/sanitizers")
    result = {}
    for name in ("asan", "ubsan", "lsan"):
        path = base / f"{name}.txt"
        entries = []
        if path.is_file():
            for line in path.read_text().splitlines():
                line = line.strip()
                if line and not line.startswith("#"):
                    entries.append(line)
        result[name] = entries
    return result


def main():
    if not REPORT_DIR.is_dir():
        print(f"error: {REPORT_DIR} not found", file=sys.stderr)
        sys.exit(1)

    asan = scan_directory(ASAN_DIR, "asan", parse_asan_block, ASAN_ERROR)
    ubsan = scan_directory(UBSAN_DIR, "ubsan", parse_ubsan_lines, UBSAN_ERROR)
    suppressions = load_suppressions()

    report = {
        "asan": asan,
        "ubsan": ubsan,
        "suppressions": suppressions,
        "total_findings": asan["finding_count"] + ubsan["finding_count"],
    }

    OUT.write_text(json.dumps(report, indent=2))

    # human readable to stdout
    total = report["total_findings"]
    print(f"asan: {asan['finding_count']} findings ({asan['pid_file_count']} pid files, {asan['log_hit_count']} log hits)")
    print(f"ubsan: {ubsan['finding_count']} findings ({ubsan['pid_file_count']} pid files, {ubsan['log_hit_count']} log hits)")

    if total == 0:
        print("result: clean")
    else:
        print(f"result: {total} finding(s)")
        for f in asan["findings"]:
            print(f"  [{f['tool']}] {f['type']} at {f['location']}")
        for f in ubsan["findings"]:
            print(f"  [UBSan] {f['type']} at {f['location']}")

    if any(suppressions.values()):
        print("suppressions:")
        for tool, entries in suppressions.items():
            for e in entries:
                print(f"  {tool}: {e}")

    print(f"\njson: {OUT}")


if __name__ == "__main__":
    main()

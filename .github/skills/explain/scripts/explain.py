#!/usr/bin/env python3
"""
explain.py: interpret Z3 output in a readable form.

Usage:
    python explain.py --file output.txt
    echo "sat\n(model ...)" | python explain.py --stdin
"""

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "shared"))
from z3db import Z3DB, parse_model, parse_stats, parse_unsat_core, setup_logging


def detect_type(text: str) -> str:
    if "(define-fun" in text:
        return "model"
    if "(error" in text:
        return "error"
    if re.search(r":\S+\s+[\d.]+", text):
        return "stats"
    first = text.strip().split("\n")[0].strip()
    if first == "unsat":
        return "core"
    return "unknown"


def explain_model(text: str):
    model = parse_model(text)
    if not model:
        print("no model found in output")
        return
    print("satisfying assignment:")
    for name, val in model.items():
        # show hex for large integers (likely bitvectors)
        try:
            n = int(val)
            if abs(n) > 255:
                print(f"  {name} = {val} (0x{n:x})")
            else:
                print(f"  {name} = {val}")
        except ValueError:
            print(f"  {name} = {val}")


def explain_core(text: str):
    core = parse_unsat_core(text)
    if core:
        print(f"conflicting assertions ({len(core)}):")
        for label in core:
            print(f"  {label}")
    else:
        print("unsat (no named assertions for core extraction)")


def explain_stats(text: str):
    stats = parse_stats(text)
    if not stats:
        print("no statistics found")
        return
    print("performance breakdown:")
    for k in sorted(stats):
        print(f"  :{k} {stats[k]}")

    if "time" in stats:
        print(f"\ntotal time: {stats['time']}s")
    if "memory" in stats:
        print(f"peak memory: {stats['memory']} MB")


def explain_error(text: str):
    errors = re.findall(r'\(error\s+"([^"]+)"\)', text)
    if errors:
        print(f"Z3 reported {len(errors)} error(s):")
        for e in errors:
            print(f"  {e}")
    else:
        print("error in output but could not parse message")


def main():
    parser = argparse.ArgumentParser(prog="explain")
    parser.add_argument("--file")
    parser.add_argument("--stdin", action="store_true")
    parser.add_argument(
        "--type", choices=["model", "core", "stats", "error", "auto"], default="auto"
    )
    parser.add_argument("--db", default=None)
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    setup_logging(args.debug)

    if args.file:
        text = Path(args.file).read_text()
    elif args.stdin:
        text = sys.stdin.read()
    else:
        parser.error("provide --file or --stdin")
        return

    output_type = args.type if args.type != "auto" else detect_type(text)

    db = Z3DB(args.db)
    run_id = db.start_run("explain", text[:200])

    if output_type == "model":
        explain_model(text)
    elif output_type == "core":
        explain_core(text)
    elif output_type == "stats":
        explain_stats(text)
    elif output_type == "error":
        explain_error(text)
    else:
        print("could not determine output type")
        print("raw output:")
        print(text[:500])

    db.finish_run(run_id, "success", 0, 0)
    db.close()


if __name__ == "__main__":
    main()

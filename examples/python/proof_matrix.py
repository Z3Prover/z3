#!/usr/bin/env python3
"""Proof regression matrix: benchmarks x parameter cells x checking method.

Each benchmark is first solved without proofs to record the expected result.
Every parameter cell then re-solves it with a proof-producing configuration and
runs the checking method attached to that cell. One JSON record per
(benchmark, cell) is written, carrying a failure class:

  verified             the checker accepted every step without solver fallback
  unverified-fallback  the self checker had to call an SMT solver for some steps
  checker-rejected     a checker rejected a step
  no-proof             the run reported unsat but produced no checkable proof
                       (for example, the contradiction was found by preprocessing)
  not-applicable       the result was sat or unknown, so there is nothing to check
  disagree             the result differs from the proof-free run
  crash                nonzero exit, assertion violation, or internal error
  timeout              the time limit was reached
  no-checker           the cell records proof evidence but has no checker yet

A self-checker fallback is never reported as verified. The exit status is
nonzero if any record is classified checker-rejected, disagree, or crash.
"""
import argparse
import collections
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

_LOGIC = re.compile(r"\(set-logic\s+([A-Z_]+)\s*\)")
_RESULT = re.compile(r"^(sat|unsat|unknown)\s*$", re.MULTILINE)
_ERROR_MARKERS = ("ASSERTION VIOLATION", "internal error", "Segmentation", "UNEXPECTED CODE",
                  "VERIFY", "failed to verify", "Error:", "(error")
_PROOFS_LINE = re.compile(r"\(proofs((?:\s+[+-][\w-]+\s+\d+)*)\)")
_HINT_DECL = re.compile(r"\(declare-fun\s+([\w-]+)\s+\([^)]*\)\s+Proof\)")
_TH_LEMMA = re.compile(r"\(_ th-lemma ([\w-]+)(?: ([\w-]+))?")
_PROOF_RULE = re.compile(r"\((asserted|mp|mp~|unit-resolution|rewrite|rewrite\*|monotonicity|trans|trans\*|symm|refl|"
                         r"hypothesis|lemma|def-axiom|def-intro|apply-def|iff-true|iff-false|iff~|nnf-pos|nnf-neg|"
                         r"and-elim|not-or-elim|quant-inst|quant-intro|skolemize|th-lemma|proof-trail|assumption|"
                         r"commutativity|elim-unused|der|hyper-res|pull-quant|push-quant|distributivity|bind|true-axiom)\b")

CELLS = {
    "smt-clause-log": "sat.smt=true, solver.proof.log; checked by replaying the log through the built-in checker",
    "smt-clause-log-nopp": "as smt-clause-log with solve-eqs, propagate-values, and elim-unconstrained disabled, "
                           "so contradictions found by preprocessing (which the log does not cover) reach the core",
    "legacy-proof-object": "sat.smt=false, produce-proofs; proof object inventoried, Lean-checked when propositional",
    "legacy-clause-proof": "sat.smt=false, smt.clause_proof; proof trail inventoried (no checker yet)",
    "arith-validate": "smt.arith.validate self-validation oracle inside theory_lra",
}


def strip_commands(source):
    """Remove result-affecting front matter so the runner controls options and queries."""
    source = re.sub(r"\(set-option\s+:(produce-proofs|produce-unsat-cores|sat\.smt|smt\.clause_proof|"
                    r"solver\.proof\.[a-z_]+|smt\.arith\.validate|smt\.core\.validate)\s+[^)]*\)", "", source)
    source = re.sub(r"\(get-proof\)|\(get-model\)|\(get-unsat-core\)|\(exit\)", "", source)
    return source


def run_z3(z3, text, timeout, extra_args=()):
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(text)
        path = f.name
    start = time.time()
    try:
        proc = subprocess.run([z3, *extra_args, path], capture_output=True, text=True, timeout=timeout)
        return {"stdout": proc.stdout, "stderr": proc.stderr, "code": proc.returncode,
                "time": round(time.time() - start, 3), "timeout": False}
    except subprocess.TimeoutExpired as error:
        return {"stdout": error.stdout or "", "stderr": error.stderr or "", "code": None,
                "time": timeout, "timeout": True}
    finally:
        os.unlink(path)


def result_of(run):
    match = _RESULT.search(run["stdout"])
    return match.group(1) if match else None


def crashed(run):
    text = run["stdout"] + run["stderr"]
    return run["code"] not in (0, None) or any(marker in text for marker in _ERROR_MARKERS)


def base_record(benchmark, logic, cell, expected):
    return {"benchmark": str(benchmark), "logic": logic, "cell": cell, "expected": expected}


_PROOF_UNAVAILABLE = re.compile(r'\(error "[^"]*(proof is not available|proof construction is not enabled)[^"]*"\)')


def finish(record, run, checks):
    """Fill the common result fields and derive the failure class."""
    record["time"] = run["time"]
    record["result"] = result_of(run)
    proof_errors = _PROOF_UNAVAILABLE.search(run["stdout"] + run["stderr"]) is not None
    if run["timeout"]:
        record["status"] = "timeout"
    elif record["expected"] in ("sat", "unsat") and record["result"] != record["expected"]:
        record["status"] = "crash" if crashed(run) else "disagree"
        record["error"] = (run["stderr"] + run["stdout"])[-500:]
    elif record["result"] in ("sat", "unknown"):
        record["status"] = "not-applicable"
    elif crashed(run) and not proof_errors:
        record["status"] = "crash"
        record["error"] = (run["stderr"] + run["stdout"])[-500:]
    elif proof_errors:
        record["status"] = "no-proof"
        record["error"] = _PROOF_UNAVAILABLE.search(run["stdout"] + run["stderr"]).group(0)
    else:
        record["status"] = checks(record)
    return record


_NO_PREPROCESSING = ("(set-option :smt.solve_eqs false)\n(set-option :smt.propagate_values false)\n"
                     "(set-option :smt.elim_unconstrained false)\n")


def cell_smt_clause_log(z3, source, timeout, record, preprocessing=True):
    with tempfile.NamedTemporaryFile(suffix=".smt2", delete=False) as f:
        log = f.name
    try:
        options = '(set-option :sat.smt true)\n(set-option :solver.proof.log "%s")\n' % log
        if not preprocessing:
            options += _NO_PREPROCESSING
        run = run_z3(z3, options + source, timeout)

        def checks(record):
            text = Path(log).read_text() if os.path.exists(log) else ""
            infers = text.count("(infer")
            record["log_inferences"] = infers
            record["hints"] = sorted(set(_HINT_DECL.findall(text)))
            if infers == 0:
                return "no-proof"
            replay = run_z3(z3, text, timeout)
            record["replay_time"] = replay["time"]
            out = replay["stdout"] + replay["stderr"]
            if replay["timeout"]:
                return "timeout"
            counts = {}
            for match in _PROOFS_LINE.finditer(out):
                counts = {}
                for sign, name, number in re.findall(r"([+-])([\w-]+)\s+(\d+)", match.group(1)):
                    counts[sign + name] = int(number)
            record["hint_hits"] = {k[1:]: v for k, v in counts.items() if k[0] == "+"}
            record["hint_misses"] = {k[1:]: v for k, v in counts.items() if k[0] == "-"}
            fallbacks = out.count("(verified-smt")
            record["fallbacks"] = fallbacks
            if "did not verify" in out or "is not rup" in out or crashed(replay):
                record["error"] = out[-500:]
                return "checker-rejected"
            return "unverified-fallback" if fallbacks else "verified"
        return finish(record, run, checks)
    finally:
        if os.path.exists(log):
            os.unlink(log)


def _lean_check(source, proof_text):
    """Return a status from the Lean reconstruction, or None when the fragment is unsupported."""
    try:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import proof_certificate
        import proof_to_lean
    except ImportError:
        return None
    try:
        certificate = proof_certificate.export_certificate("(set-option :produce-proofs true)\n" + source)
    except Exception:
        return None
    try:
        text = proof_to_lean.reconstruct(certificate["source_smt2"], certificate)
    except proof_to_lean.ReconstructionError as error:
        return ("checker-rejected", "lean reconstruction: %s" % error)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(text)
        path = f.name
    try:
        proc = subprocess.run([str(proof_to_lean._CHECK_LEAN), path], capture_output=True, text=True, timeout=600)
    except subprocess.TimeoutExpired:
        return ("timeout", "lean check timed out")
    finally:
        os.unlink(path)
    if proc.returncode != 0:
        return ("checker-rejected", (proc.stderr + proc.stdout)[-500:])
    return ("verified", None)


def cell_legacy_proof_object(z3, source, timeout, record, lean):
    text = "(set-option :produce-proofs true)\n(set-option :sat.smt false)\n" + source
    text = re.sub(r"\(check-sat\)", "(check-sat)(get-proof)", text, count=1)
    run = run_z3(z3, text, timeout)

    def checks(record):
        proof = run["stdout"].split("\n", 1)[1] if "\n" in run["stdout"] else ""
        rules = collections.Counter(_PROOF_RULE.findall(proof))
        record["rules"] = dict(sorted(rules.items()))
        record["th_lemmas"] = dict(sorted(collections.Counter(
            " ".join(filter(None, m)) for m in _TH_LEMMA.findall(proof)).items()))
        if not rules:
            return "no-proof"
        if lean:
            outcome = _lean_check(source, proof)
            if outcome is not None:
                status, error = outcome
                record["checker"] = "lean"
                if error:
                    record["error"] = error
                return status
        return "no-checker"
    return finish(record, run, checks)


def cell_legacy_clause_proof(z3, source, timeout, record):
    text = "(set-option :smt.clause_proof true)\n(set-option :sat.smt false)\n" + source
    text = re.sub(r"\(check-sat\)", "(check-sat)(get-proof)", text, count=1)
    run = run_z3(z3, text, timeout)

    def checks(record):
        proof = run["stdout"]
        record["trail_steps"] = proof.count("(assumption") + proof.count("(infer") + proof.count("(del")
        record["rules"] = dict(sorted(collections.Counter(_PROOF_RULE.findall(proof)).items()))
        return "no-proof" if "proof-trail" not in proof else "no-checker"
    return finish(record, run, checks)


def cell_arith_validate(z3, source, timeout, record):
    text = "(set-option :smt.arith.validate true)\n(set-option :sat.smt false)\n" + source
    run = run_z3(z3, text, timeout)
    return finish(record, run, lambda record: "verified")


def run_benchmark(z3, path, cells, timeout, lean):
    original = Path(path).read_text(errors="replace")
    logic = (_LOGIC.search(original) or [None, "unknown"])[1]
    source = strip_commands(original)
    reference = run_z3(z3, source, timeout)
    expected = None if reference["timeout"] or crashed(reference) else result_of(reference)
    yield {"benchmark": str(path), "logic": logic, "cell": "reference", "expected": expected,
           "result": expected, "time": reference["time"],
           "status": "timeout" if reference["timeout"] else "crash" if crashed(reference) else "reference"}
    for cell in cells:
        record = base_record(path, logic, cell, expected)
        if cell == "smt-clause-log":
            yield cell_smt_clause_log(z3, source, timeout, record)
        elif cell == "smt-clause-log-nopp":
            yield cell_smt_clause_log(z3, source, timeout, record, preprocessing=False)
        elif cell == "legacy-proof-object":
            yield cell_legacy_proof_object(z3, source, timeout, record, lean)
        elif cell == "legacy-clause-proof":
            yield cell_legacy_clause_proof(z3, source, timeout, record)
        elif cell == "arith-validate":
            yield cell_arith_validate(z3, source, timeout, record)


def summarize(records):
    table = collections.defaultdict(collections.Counter)
    for record in records:
        if record["cell"] != "reference":
            table[(record["logic"], record["cell"])][record["status"]] += 1
    statuses = sorted({s for counter in table.values() for s in counter})
    width = max([len("%s / %s" % key) for key in table] + [12])
    lines = ["%-*s %s" % (width, "logic / cell", " ".join("%20s" % s for s in statuses))]
    for key in sorted(table):
        lines.append("%-*s %s" % (width, "%s / %s" % key, " ".join("%20d" % table[key][s] for s in statuses)))
    return "\n".join(lines)


def collect_benchmarks(paths):
    for entry in paths:
        entry = Path(entry)
        if entry.is_dir():
            yield from sorted(entry.rglob("*.smt2"))
        elif entry.suffix == ".txt":
            for line in entry.read_text().splitlines():
                line = line.strip()
                if line and not line.startswith("#"):
                    yield Path(line)
        else:
            yield entry


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("benchmarks", nargs="+", help="SMT-LIB files, directories, or .txt lists of files")
    parser.add_argument("--z3", default="z3", help="z3 executable (default: z3 on PATH)")
    parser.add_argument("--cells", default=",".join(CELLS), help="comma-separated cells (default: all): " +
                        "; ".join("%s = %s" % item for item in CELLS.items()))
    parser.add_argument("--timeout", type=float, default=60.0, help="seconds per solver invocation")
    parser.add_argument("--lean", action="store_true", help="Lean-check propositional legacy proof objects")
    parser.add_argument("--out", help="JSON lines output file (default: stdout only for the summary)")
    parser.add_argument("--limit", type=int, help="stop after this many benchmarks")
    args = parser.parse_args()
    cells = [c.strip() for c in args.cells.split(",") if c.strip()]
    unknown = [c for c in cells if c not in CELLS]
    if unknown:
        parser.error("unknown cells: %s" % ", ".join(unknown))
    records = []
    out = open(args.out, "a") if args.out else None
    for index, path in enumerate(collect_benchmarks(args.benchmarks)):
        if args.limit is not None and index >= args.limit:
            break
        for record in run_benchmark(args.z3, path, cells, args.timeout, args.lean):
            records.append(record)
            if out:
                out.write(json.dumps(record) + "\n")
                out.flush()
            if record["cell"] != "reference":
                print("%-22s %-10s %-20s %-8s %6.2fs %s" % (
                    Path(record["benchmark"]).name[:22], record["logic"], record["cell"], record["status"],
                    record.get("time") or 0, ("fallbacks=%d" % record["fallbacks"]) if record.get("fallbacks") else ""),
                    flush=True)
    if out:
        out.close()
    print()
    print(summarize(records))
    bad = [r for r in records if r["status"] in ("checker-rejected", "disagree", "crash")]
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

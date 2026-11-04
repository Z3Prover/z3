#!/usr/bin/env python3
"""Write the Markdown summary of scripts/ci_lean_proofs.sh.

The summary says what the run checked and where Lean certification stops:
what a lean-verified result means and what it trusts, the reconstruction
tests by module, every gated benchmark with its proof rules, and, when the
boundary probe ran, how far certification reaches on unchanged SMT-LIB and F*
benchmarks and why the rest is not certified. It reads the check list written
by ci_lean_proofs.sh, the unittest logs it names, and the JSON lines records of
z3test's scripts/proofs/proof_matrix.py. Only the Python standard library is
used, so the summary is written even when the z3 bindings are broken.
"""

import argparse
import ast
import collections
import json
import re
import sys
from pathlib import Path

CORES = {"legacy-proof-object": "legacy proof object", "smt-clause-log-nopp": "clause log"}
NOT_CERTIFIED = ("unsupported", "timeout", "not-applicable", "no-proof", "checker-rejected", "disagree", "crash")
# Probe outcomes that point at a defect rather than at the edge of the supported fragment.
ALARMS = ("checker-rejected", "disagree", "crash")
_TEST_LINE = re.compile(r"^(test\w*) \(([\w.]+)\)")
_OUTCOME = re.compile(r" \.\.\. (ok|FAIL|ERROR|skipped(?: (.*))?|expected failure|unexpected success)\s*$")


def parse_unittest_log(text):
    """Return {module: Counter(outcome)} and {reason: count} of skips from a unittest -v log."""
    modules = collections.defaultdict(collections.Counter)
    skips = collections.Counter()
    current = None
    for line in text.splitlines():
        match = _TEST_LINE.match(line)
        if match:
            current = match.group(2).split(".")[0]
        outcome = _OUTCOME.search(line)
        if current is None or outcome is None:
            continue
        kind = outcome.group(1)
        if kind.startswith("skipped"):
            modules[current]["skipped"] += 1
            skips[(outcome.group(2) or "").strip("'\"") or "no reason given"] += 1
        elif kind == "ok" or kind == "expected failure":
            modules[current]["passed"] += 1
        else:
            modules[current]["failed"] += 1
        current = None
    return modules, skips


def module_description(path):
    """First sentence of a test module's header comment or docstring."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return ""
    try:
        docstring = ast.get_docstring(ast.parse(text))
    except SyntaxError:
        docstring = None
    if not docstring:
        lines = []
        for line in text.splitlines():
            if not line.startswith("#"):
                break
            line = line.lstrip("#").strip()
            if line and not line.startswith("Copyright"):
                lines.append(line)
        docstring = " ".join(lines)
    docstring = " ".join(docstring.split())
    sentence = re.split(r"(?<=[a-z0-9)])[.:] ", docstring + " ", maxsplit=1)[0].rstrip(". :")
    return sentence[:157] + "..." if len(sentence) > 160 else sentence


def supported_fragments(source):
    """The fragments the reconstructor accepts, read from proof_to_lean.py without importing it."""
    try:
        tree = ast.parse((source / "examples" / "python" / "proof_to_lean.py").read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        return []
    for node in tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name) and node.targets[0].id == "_FRAGMENTS"):
            try:
                return list(ast.literal_eval(node.value))
            except ValueError:
                return []
    return []


def read_records(path):
    if path is None or not path.is_file():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def read_checks(path):
    checks = []
    for line in path.read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if len(fields) >= 5:
            name, kind, gates, code, seconds = fields[:5]
            checks.append({"name": name, "kind": kind, "gates": gates == "gate", "exit": int(code),
                           "seconds": int(seconds), "log": fields[5] if len(fields) > 5 else ""})
    return checks


def cell(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def duration(seconds):
    seconds = int(round(seconds))
    return "%dm%02ds" % divmod(seconds, 60) if seconds >= 60 else "%ds" % seconds


def table(header, rows):
    lines = ["| " + " | ".join(header) + " |", "|" + "|".join(" --- " for _ in header) + "|"]
    lines += ["| " + " | ".join(cell(value) for value in row) + " |" for row in rows]
    return lines


# Lean output that means a resource limit stopped the check, not that a proof step is wrong.
LEAN_LIMITS = (
    ("maximum number of heartbeats", "Lean heartbeat limit (maxHeartbeats) reached"),
    ("excessive memory consumption", "Lean kernel memory limit reached"),
    ("maximum number of case-splits", "grind case-split limit reached"),
    ("maximum recursion depth", "Lean recursion depth limit reached"),
    ("deep recursion", "Lean deep recursion detected"),
    ("`simp` failed: maximum number of steps exceeded", "simp step limit (maxSteps) reached"),
)
LEAN_LIMIT = "Lean limit"
_PATH = re.compile(r"(?:/[^\s:/]+)+/?")


def lean_error(text):
    """The first Lean error message of a checker's output, without paths, positions, and hashes."""
    killed = re.fullmatch(r"\s*Lean worker exited with code -9\s*", text)
    if killed:
        return ("the reconstruction worker was killed (SIGKILL), most likely by the out-of-memory killer; "
                "the checker's own limits did not stop it")
    text = _PATH.sub("<path>", text)
    match = re.search(r"error: (.*)", text)
    message = match.group(1) if match else " ".join(text.split())
    message = re.sub(r"<path>(:\d+)*:? ?", "", message)
    message = re.sub(r"Build completed successfully \(\d+ jobs\)\. ?(Checking ?)?", "", message)
    message = re.sub(r"[0-9a-f]{16,}", "<hash>", message)
    message = re.sub(r"_private\.[\w.<>]*\.", "", message)
    return message.strip()


def classify(record):
    """(outcome, reason, defect) of a record that is not lean-verified; reasons drop instance details."""
    status = record["status"]
    error = str(record.get("error") or "")
    if status == "not-applicable":
        return status, "z3 did not report unsat (result: %s)" % (record.get("result") or "none"), False
    if status == "timeout":
        return status, " ".join(error.split()) or "time limit reached", False
    if status == "checker-rejected":
        for marker, reason in LEAN_LIMITS:
            if marker in error:
                return LEAN_LIMIT, reason, False
        reason = lean_error(error)
        if "unknown constant" in reason:
            reason += " (follows an earlier failed lemma; see the artifact)"
    else:
        reason = " ".join(error.split())
    reason = re.sub(r"\b(node|step|line|character|clause|index) \d+", r"\1 N", reason)
    reason = re.sub(r"(?<![\w!])\d+(\.\d+)?\b|(?<=_)\d+\b", "N", reason)
    reason = re.sub(r"(declaration|signature|symbol|function|constant): [\w!.|]+", r"\1: <name>", reason)
    reason = (reason[:160] + "...") if len(reason) > 160 else (reason or status)
    return status, reason, status in ALARMS


def rule_summary(rules, limit=5):
    if not rules:
        return ""
    top = sorted(rules.items(), key=lambda item: (-item[1], item[0]))
    text = ", ".join("%s %d" % item for item in top[:limit])
    return text + (", +%d more" % (len(top) - limit) if len(top) > limit else "")


def scope_section(fragments, toolchain):
    lines = ["### What a lean-verified result means", ""]
    lines.append(
        "z3 solved the unchanged SMT-LIB input with proofs enabled; `examples/python/proof_certificate.py` "
        "turned its native proof (the legacy proof object, or the `sat.smt` clause log with solve-eqs, "
        "propagate-values, elim-unconstrained, and bound-simplifier disabled) into a certificate; "
        "`examples/python/proof_to_lean.py` rebuilt it as a Lean proof that the input's assertions are "
        "unsatisfiable; and the Lean kernel%s accepted that proof with `--trust=0` and warnings as errors, "
        "so `sorry` fails." % (" (%s)" % toolchain if toolchain else ""))
    lines += ["", "**Checked, not trusted:** z3's search, its proof object and clause log, the certificate, "
              "the clause-log trimmer, and every inference step: each step is re-proved in Lean.", ""]
    lines += ["**Trusted:**", "",
              "- *The statement.* Z3's SMT-LIB parser (through the Python API) and the encoder in "
              "`proof_to_lean.py` that states the Lean theorem from the input. The input's digest names the "
              "theorem; it is not a proof that the theorem means what the SMT-LIB file means.",
              "- *The Lean kernel* of the pinned toolchain and, for every theory slice, the three standard axioms "
              "(`propext`, `Classical.choice`, `Quot.sound`) through Lean core's `Rat` and `grind`; Boolean "
              "proofs are axiom-free.",
              "- *Two modelling choices,* each argued in the exporter documentation: Real variables range over "
              "Lean's `Rat` (sound for linear arithmetic), and all uninterpreted sorts share one carrier type "
              "(sound for unsatisfiability).", ""]
    if fragments:
        lines.append("**In scope:** quantifier-free %s input with a single `check-sat`. Everything else "
                     "(quantifiers, arrays, bit-vectors, datatypes, nonlinear arithmetic, strings, floating "
                     "point, ...) is rejected before any proof is produced and reported as `unsupported`. "
                     "Sat results and models are not checked." % ", ".join("`%s`" % f for f in fragments))
        lines.append("")
    return lines


def unittest_section(checks, source, z3test):
    lines = []
    for check in checks:
        if check["kind"] != "unittest" or not check["log"] or not Path(check["log"]).is_file():
            continue
        modules, skips = parse_unittest_log(Path(check["log"]).read_text(encoding="utf-8", errors="replace"))
        lines += ["### %s" % check["name"], ""]
        if not modules:
            lines += ["No test results found in the log (exit %d)." % check["exit"], ""]
            continue
        rows, totals = [], collections.Counter()
        for module in sorted(modules):
            counts = modules[module]
            totals.update(counts)
            path = next((p for p in (source / "examples" / "python" / (module + ".py"),
                                     z3test / "scripts" / "proofs" / (module + ".py")) if p.is_file()), None)
            rows.append(["`%s`" % module, module_description(path) if path else "",
                         sum(counts.values()), counts["passed"],
                         ("**%d**" % counts["failed"]) if counts["failed"] else 0, counts["skipped"]])
        rows.append(["**total**", "", sum(totals.values()), totals["passed"],
                     ("**%d**" % totals["failed"]) if totals["failed"] else 0, totals["skipped"]])
        lines += table(["module", "covers", "tests", "passed", "failed", "skipped"], rows)
        if skips:
            lines += ["", "Skipped tests, by reason: " +
                      "; ".join("%s (%d)" % (reason, count) for reason, count in skips.most_common())]
        lines.append("")
    return lines


def gate_section(records):
    records = [r for r in records if r.get("cell") in CORES]
    if not records:
        return []
    lines = ["### Gated benchmarks", "",
             "Every benchmark below must be lean-verified for the run to pass. These are small inputs, "
             "each written to exercise particular proof rules; the probe below measures reach on real benchmarks.",
             ""]
    rows = []
    for r in records:
        rows.append([Path(r["benchmark"]).name, r.get("logic", ""), r.get("fragment", ""), CORES[r["cell"]],
                     ("**%s**" % r["status"]) if r["status"] != "lean-verified" else r["status"],
                     "%.2fs" % (r.get("solve_time") or 0), "%.2fs" % (r.get("check_time") or 0),
                     "%d" % r["proof_size"] if r.get("proof_size") else "", rule_summary(r.get("rules"))])
    lines += table(["benchmark", "logic", "fragment", "proof source", "result", "solve", "Lean check",
                    "certificate bytes", "most frequent proof rules"], rows)
    failed = [r for r in records if r["status"] != "lean-verified"]
    for r in failed:
        lines += ["", "- `%s` (%s): %s" % (Path(r["benchmark"]).name, CORES[r["cell"]],
                                           cell(classify(r)[1]))]
    return lines + [""]


def corpus_of(path, corpora):
    best = None
    for label, directory in corpora:
        try:
            Path(path).resolve().relative_to(directory)
        except ValueError:
            continue
        if best is None or len(str(directory)) > len(str(best[1])):
            best = (label, directory)
    return best[0] if best else "other"


def outcome(record):
    return "lean-verified" if record["status"] == "lean-verified" else classify(record)[0]


def outcome_text(counter):
    order = list(dict.fromkeys(["lean-verified", "unsupported", "timeout", LEAN_LIMIT] + list(NOT_CERTIFIED)))
    parts = []
    for status in order + sorted(set(counter) - set(order)):
        if counter[status]:
            text = "%d %s" % (counter[status], status)
            parts.append("**%s**" % text if status in ALARMS else text)
    return ", ".join(parts)


def probe_section(records, corpora, timeout, lean_timeout):
    if not records:
        return []
    by_benchmark = collections.OrderedDict()
    for r in records:
        by_benchmark.setdefault(r["benchmark"], {})[r["cell"]] = r
    groups = collections.OrderedDict()
    for benchmark, cells in by_benchmark.items():
        logic = next(iter(cells.values())).get("logic", "logic_unknown")
        logic = "(no set-logic)" if logic == "logic_unknown" else logic
        groups.setdefault((corpus_of(benchmark, corpora), logic), []).append(cells)
    total = len(by_benchmark)
    certified = sum(1 for cells in by_benchmark.values()
                    if any(cells.get(c, {}).get("status") == "lean-verified" for c in CORES))
    lines = ["### Boundary probe (informational: does not fail the run)", "",
             "Unchanged benchmarks outside the gate, run through both proof sources with a %s solver limit "
             "and a %s Lean limit per benchmark. **%d of %d** benchmarks were lean-verified from at least one "
             "proof source." % (duration(timeout), duration(lean_timeout), certified, total), ""]
    rows = []
    for (corpus, logic), items in groups.items():
        unsat = sum(1 for cells in items if cells.get("reference", {}).get("result") == "unsat")
        either = sum(1 for cells in items
                     if any(cells.get(c, {}).get("status") == "lean-verified" for c in CORES))
        outcomes = [outcome_text(collections.Counter(outcome(cells[c]) for cells in items if c in cells))
                    for c in CORES]
        rows.append([corpus, logic, len(items), unsat, either] + outcomes)
    lines += table(["corpus", "logic", "benchmarks", "z3 unsat within limit", "lean-verified (either source)",
                    "legacy proof object", "clause log"], rows)
    lines += ["", "#### Why the rest is not certified", ""]
    reasons = collections.OrderedDict()
    for (corpus, logic), items in groups.items():
        for cells in items:
            for c in CORES:
                r = cells.get(c)
                if r is None or r["status"] == "lean-verified":
                    continue
                key = classify(r)
                entry = reasons.setdefault(key, {"cores": collections.Counter(), "logics": {},
                                                 "example": Path(r["benchmark"]).name})
                entry["cores"][c] += 1
                entry["logics"].setdefault(logic, set()).add(r["benchmark"])
    ordered = sorted(reasons.items(), key=lambda item: -sum(item[1]["cores"].values()))
    for _, entry in ordered:
        entry["logics"] = collections.Counter({logic: len(names) for logic, names in entry["logics"].items()})
    rows = [["**%s**" % status if defect else status, reason,
             entry["cores"]["legacy-proof-object"], entry["cores"]["smt-clause-log-nopp"],
             ", ".join("%s %d" % item for item in entry["logics"].most_common(4))
             + (", ..." if len(entry["logics"]) > 4 else ""), entry["example"]]
            for (status, reason, defect), entry in ordered[:25]]
    if not rows:
        return lines + ["Nothing to explain: every probed benchmark was lean-verified from both proof sources.", ""]
    lines += table(["outcome", "reason", "legacy", "clause log", "benchmarks by logic", "example"], rows)
    if len(ordered) > 25:
        lines += ["", "%d less frequent reasons are in the probe records." % (len(ordered) - 25)]
    if any(status == LEAN_LIMIT for status, _, _ in reasons):
        lines += ["", "`%s`: the certificate was produced but Lean stopped at a resource limit (heartbeats, kernel "
              "memory, grind case splits, simp steps) before accepting or refuting it; such proofs need a cheaper "
              "reconstruction, not a fix to z3's proof." % LEAN_LIMIT]
    alarms = [r for cells in by_benchmark.values() for c, r in cells.items()
              if c in CORES and r["status"] != "lean-verified" and classify(r)[2]]
    lines += ["", "#### Possible defects", ""]
    if alarms:
        lines += ["Certificates the reconstructor or Lean rejected for a reason other than a resource limit, "
                  "results that differ from the proof-free run, and crashes. Unlike the outcomes above, these "
                  "may be bugs in z3's proofs or in the reconstruction:", ""]
        lines += ["- `%s` (%s, %s): %s" % (Path(r["benchmark"]).name, CORES[r["cell"]], r["status"],
                                           cell(lean_error(str(r.get("error") or ""))[:300]))
                  for r in alarms]
    else:
        lines.append("None: every rejection was a Lean resource limit, no result disagreed with the proof-free "
                     "run, and nothing crashed.")
    return lines + [""]


def check_result(check):
    """A gating check passes on exit 0; the probe exits 1 whenever an input is not certified, which is its
    normal outcome, and fails only on a harness or configuration error."""
    if check["gates"]:
        return "pass" if check["exit"] == 0 else "**FAIL** (exit %d)" % check["exit"]
    return "done" if check["exit"] in (0, 1) else "**FAIL** (exit %d)" % check["exit"]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--checks", type=Path, required=True,
                        help="tab-separated check list: name, kind, gate|probe, exit status, seconds, log")
    parser.add_argument("--source", type=Path, required=True, help="Z3 checkout")
    parser.add_argument("--z3test", type=Path, required=True, help="z3test checkout")
    parser.add_argument("--gate", type=Path, help="proof_matrix.py records of the gated benchmarks")
    parser.add_argument("--probe", type=Path, help="proof_matrix.py records of the boundary probe")
    parser.add_argument("--corpus", action="append", default=[], metavar="LABEL=DIR",
                        help="name a probed benchmark directory in the probe table (repeatable)")
    parser.add_argument("--probe-timeout", type=float, default=0, help="solver limit of the probe, seconds")
    parser.add_argument("--probe-lean-timeout", type=float, default=0, help="Lean limit of the probe, seconds")
    parser.add_argument("--context", action="append", default=[], metavar="TEXT",
                        help="a line identifying the inputs, such as commits and versions (repeatable)")
    parser.add_argument("--artifacts-url", help="where the certificates and Lean files can be downloaded")
    args = parser.parse_args()
    checks = read_checks(args.checks)
    corpora = []
    for item in args.corpus:
        label, _, directory = item.partition("=")
        corpora.append((label, Path(directory).resolve()))
    toolchain = ""
    try:
        toolchain = (args.source / "lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError:
        pass
    failed = [c for c in checks if c["exit"] != 0 and (c["gates"] or c["exit"] != 1)]
    # A probe-only run (one corpus per CI job) leaves the scope and the gate to the gate job's summary.
    probe_only = bool(checks) and not any(c["gates"] for c in checks)
    title = "Lean boundary probe: %s" % ", ".join(label for label, _ in corpora) if probe_only else "Lean proof checks"
    lines = ["## %s: %s" % (title, "**FAILED**" if failed else "done" if probe_only else "passed"), ""]
    lines += ["%s  " % cell(text) for text in args.context]
    if args.context:
        lines.append("")
    rows = [[c["name"], "yes" if c["gates"] else "no (informational)", check_result(c), duration(c["seconds"])]
            for c in checks]
    lines += table(["check", "gates the run", "result", "time"], rows) + [""]
    if probe_only:
        lines += ["What a lean-verified result means, what is trusted, and the gated checks are in the "
                  "*Lean proof checks* summary of the same run.", ""]
    else:
        lines += scope_section(supported_fragments(args.source), toolchain)
    lines += unittest_section(checks, args.source, args.z3test)
    lines += gate_section(read_records(args.gate))
    lines += probe_section(read_records(args.probe), corpora, args.probe_timeout, args.probe_lean_timeout)
    if args.artifacts_url:
        lines += ["Certificates, checked Lean files, and the JSON records: [run artifacts](%s)." % args.artifacts_url,
                  ""]
    sys.stdout.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()

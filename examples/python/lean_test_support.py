"""Kernel checks for the proof_to_lean tests: one Lean run per certificate, batches, and a slow tier.

Most certificates of the tests check in a tenth of a second, while each run of
scripts/check_lean.sh costs about half a second to start Lean and to build the
project. So the tests

- check a certificate once, with its `#print axioms` report in the same run
  (`check`), instead of once in `proof_to_lean.check_and_write` and again for
  the report;
- build the Lean project once per test process and skip `lake build` after
  that (`Z3_LEAN_SKIP_BUILD`);
- check the documented inputs of a test in a few Lean files rather than one
  file each (`prefetch`): the batch's report of each certificate is kept under
  the certificate's exact text, and `check` of that text takes it instead of
  running Lean again. A batch Lean rejects is not kept, so the certificates of
  a failing batch are checked one at a time and fail as they would alone;
- skip the stress tests, whose inputs exercise the reconstruction's limits of
  size and memory rather than a feature, unless `Z3_LEAN_SLOW_TESTS=1`.

Concatenated certificates check as they do alone: every certificate is its own
`namespace ... end` block, which scopes its names and options, and outside the
blocks a file has only its imports and comments (the reconstruction emits no
instance, attribute, notation, or other global command). A text above
`proof_to_lean._SERIAL_ELABORATION_CHARS`, which turns on serial elaboration
for its whole file, is never batched.
"""

import hashlib
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import proof_to_lean

SLOW_TESTS = os.environ.get("Z3_LEAN_SLOW_TESTS") == "1"
_BATCH_CHARS = 2000000
_built = False
_checked = {}  # sha256 of a checked file's text -> its report


def slow(reason):
    """Skip a stress test unless Z3_LEAN_SLOW_TESTS=1."""
    return unittest.skipUnless(SLOW_TESTS, "slow Lean test, run with Z3_LEAN_SLOW_TESTS=1: " + reason)


def namespace(source):
    return "Z3Proofs.NativeCertificate.p" + hashlib.sha256(source.encode()).hexdigest()


def run_check_lean(path):
    """Run scripts/check_lean.sh on one file; only the first run of the process builds the Lean project."""
    global _built
    environment = dict(os.environ)
    if _built:
        environment["Z3_LEAN_SKIP_BUILD"] = "1"
    result = subprocess.run([str(proof_to_lean._CHECK_LEAN), str(path)], text=True, capture_output=True,
                            env=environment)
    if "Lean checks passed." in result.stdout:
        _built = True
    return result


def _with_axioms(source, text, theorems):
    ns = namespace(source)
    return text + "".join("\n#print axioms %s.%s\n" % (ns, theorem) for theorem in theorems)


def _key(checked):
    return hashlib.sha256(checked.encode()).hexdigest()


def check(test, source, certificate=None, text=None, theorems=("unsat",)):
    """Reconstruct the certificate (unless its text is given), kernel-check it once, and return
    (text, report): the Lean text and the `#print axioms` output of the theorems, on one line."""
    if text is None:
        text = proof_to_lean.reconstruct(source, certificate)
    checked = _with_axioms(source, text, theorems)
    report = _checked.pop(_key(checked), None)
    if report is not None:
        return text, report
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "checked.lean"
        output.write_text(checked)
        result = run_check_lean(output)
    if result.returncode != 0:
        output = result.stdout + result.stderr
        errors = [line for line in output.splitlines() if "error" in line]
        raise test.failureException("Lean rejected the certificate:\n%s\n...\n%s"
                                    % ("\n".join(errors[:5]), output[-3000:]))
    return text, " ".join(result.stdout.split())


def _report_of(report, source, theorems):
    """The part of a batch's report about the theorems of one certificate."""
    ns = namespace(source)
    parts = []
    for theorem in theorems:
        start = report.find("'%s.%s'" % (ns, theorem))
        if start < 0:
            return None
        ends = [position for position in (report.find(" 'Z3Proofs.NativeCertificate.", start + 1),
                                          report.find(" Lean checks passed.", start)) if position >= 0]
        parts.append(report[start:min(ends or [len(report)])])
    return " ".join(parts)


def prefetch(certificates, theorems=("unsat",)):
    """Kernel-check (source, certificate) pairs in batches, so that `check` of each takes the batch's
    report. Certificates that fail to reconstruct, and batches Lean rejects, are left to `check`."""
    items, seen = [], set()
    for source, certificate in certificates:
        try:
            text = proof_to_lean.reconstruct(source, certificate)
        except Exception:  # noqa: BLE001 -- `check` reports it at the input
            continue
        checked = _with_axioms(source, text, theorems)
        if len(text) > proof_to_lean._SERIAL_ELABORATION_CHARS or _key(checked) in seen:
            continue
        seen.add(_key(checked))
        items.append((source, checked))
    # First fit: a group holds each namespace once (the same input on two cores) and at most
    # _BATCH_CHARS of text.
    groups = []  # [items, namespaces, size]
    for source, checked in items:
        ns = namespace(source)
        for group in groups:
            if ns not in group[1] and group[2] + len(checked) <= _BATCH_CHARS:
                break
        else:
            group = [[], set(), 0]
            groups.append(group)
        group[0].append((source, checked))
        group[1].add(ns)
        group[2] += len(checked)
    for group, _, _ in groups:
        imports, bodies = [], []
        for _, checked in group:
            lines = checked.split("\n")
            imports += [line for line in lines if line.startswith("import ") and line not in imports]
            bodies.append("\n".join(line for line in lines if not line.startswith("import ")))
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "batch.lean"
            output.write_text("\n".join(imports) + "\n" + "\n\n".join(bodies))
            result = run_check_lean(output)
        if result.returncode != 0:
            continue
        report = " ".join(result.stdout.split())
        for source, checked in group:
            part = _report_of(report, source, theorems)
            if part is not None:
                _checked[_key(checked)] = part

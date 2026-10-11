############################################
# Copyright (c) 2026 Microsoft Corporation
#
# Audit native preprocessing proof evidence before Lean reconstruction.
############################################
"""Audit solve-eqs followed by SMT search, with and without proof generation."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import z3

from proof_certificate import (
    ProofExportError, _certificate_from_proof, parse_propositional_assertions,
)
from proof_to_lean import ReconstructionError, check_and_write


def _run_pipeline(source, pipeline, proofs_enabled, timeout_ms):
    context = z3.Context(proof=proofs_enabled)
    assertions = parse_propositional_assertions(source, context)
    if pipeline == "simplifier":
        solver = z3.Simplifier("solve-eqs", ctx=context).add(z3.SimpleSolver(ctx=context))
    elif pipeline == "tactic":
        solver = z3.Then(z3.Tactic("solve-eqs", ctx=context), z3.Tactic("smt", ctx=context)).solver()
    else:
        raise ValueError("unknown preprocessing pipeline: %s" % pipeline)
    solver.set(timeout=timeout_ms)
    solver.add(assertions)
    result = solver.check()
    statistics = {key: value for key, value in solver.statistics()}
    report = {
        "pipeline": pipeline,
        "proofs_enabled": proofs_enabled,
        "result": str(result),
        "statistics": statistics,
        "preprocessing_observed": statistics.get("solve-eqs-elim-vars", 0) > 0,
        "branching_search_observed": (
            statistics.get("decisions", 0) > 0 and statistics.get("conflicts", 0) > 0),
        "proof_status": "unavailable" if proofs_enabled else "disabled",
        "diagnostics": [],
    }
    if result != z3.unsat:
        reason = solver.reason_unknown() if result == z3.unknown else "no refutation exists"
        report["diagnostics"].append("%s: %s" % (result, reason))
        return report
    if not proofs_enabled:
        return report

    try:
        proof = solver.proof()
        report["native_proof"] = proof.sexpr()
        certificate = _certificate_from_proof(source, assertions, proof)
        report["rule_counts"] = certificate["rule_counts"]
    except (z3.Z3Exception, ProofExportError) as error:
        report["proof_status"] = "native-proof-error"
        report["diagnostics"].append(str(error))
        return report

    try:
        with tempfile.TemporaryDirectory() as directory:
            check_and_write(source, certificate, Path(directory) / "checked.lean")
    except ReconstructionError as error:
        report["proof_status"] = "reconstruction-rejected"
        report["diagnostics"].append(str(error))
    except subprocess.CalledProcessError as error:
        report["proof_status"] = "lean-rejected"
        report["diagnostics"].append(
            "Lean checking exited with code %d:\n%s%s" % (
                error.returncode, error.stdout or "", error.stderr or ""))
    else:
        report["proof_status"] = "lean-checked"
    return report


def audit_preprocessing(source, *, require_search=False, timeout_ms=10000):
    """Report coverage separately from proof validity; never certify a bypass."""
    if type(timeout_ms) is not int or timeout_ms <= 0:
        raise ValueError("timeout_ms must be a positive integer")
    runs = [_run_pipeline(source, pipeline, proofs, timeout_ms)
            for pipeline in ("simplifier", "tactic") for proofs in (False, True)]
    for run in runs:
        if not run["preprocessing_observed"]:
            run["diagnostics"].append("No solve-eqs variable elimination was reported.")
        if require_search and not run["branching_search_observed"]:
            run["diagnostics"].append("No branching search with conflicts was reported.")
    complete = all(
        run["result"] == "unsat"
        and run["preprocessing_observed"]
        and (not require_search or run["branching_search_observed"])
        and (not run["proofs_enabled"] or run["proof_status"] == "lean-checked")
        for run in runs)
    return {
        "z3_version": z3.get_full_version(),
        "require_search": require_search,
        "complete": complete,
        "runs": runs,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="original propositional SMT-LIB input")
    parser.add_argument("--require-search", action="store_true",
                        help="also require positive decision and conflict counts")
    parser.add_argument("--timeout-ms", type=int, default=10000,
                        help="positive timeout per solver invocation (default: 10000)")
    args = parser.parse_args()
    try:
        with args.input.open(encoding="utf-8", newline="") as stream:
            source = stream.read()
        report = audit_preprocessing(
            source, require_search=args.require_search, timeout_ms=args.timeout_ms)
    except (ProofExportError, z3.Z3Exception, OSError, ValueError) as error:
        parser.exit(2, "%s: error: %s\n" % (parser.prog, error))
    json.dump(report, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")
    if not report["complete"]:
        parser.exit(1, "solve-eqs proof coverage is incomplete; see the audit report.\n")


if __name__ == "__main__":
    main()

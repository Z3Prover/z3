"""Independent optimality-certificate verifier."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping

import z3

from .objective import objective_for_weights
from .parse import parse_file
from .problem import Problem, _collect_constants


class CertificateError(ValueError):
    pass


def verify_certificate(problem: Problem | str | Path, certificate: Mapping[str, Any] | str | Path) -> bool:
    """Return ``True`` only when an independently rebuilt certificate passes."""
    try:
        _verify_or_raise(problem, certificate)
        return True
    except (CertificateError, OSError, ValueError, z3.Z3Exception):
        return False


def verify_certificate_or_raise(problem: Problem | str | Path, certificate: Mapping[str, Any] | str | Path) -> None:
    _verify_or_raise(problem, certificate)


def _load_certificate(certificate: Mapping[str, Any] | str | Path) -> Mapping[str, Any]:
    if isinstance(certificate, (str, Path)):
        return json.loads(Path(certificate).read_text(encoding="utf-8"))
    return certificate


def _verify_or_raise(problem: Problem | str | Path, certificate: Mapping[str, Any] | str | Path) -> None:
    instance = parse_file(problem) if isinstance(problem, (str, Path)) else problem
    cert = _load_certificate(certificate)
    if cert.get("status") != "OPTIMAL":
        raise CertificateError("certificate status is not OPTIMAL")
    try:
        reported_lb = int(cert["lower_bound"])
        reported_ub = int(cert["upper_bound"])
    except (KeyError, TypeError, ValueError) as exc:
        raise CertificateError("certificate has no integer lower_bound/upper_bound") from exc
    if reported_lb != reported_ub:
        raise CertificateError("certificate bounds do not meet")
    if "cost" in cert and int(cert["cost"]) != reported_ub:
        raise CertificateError("certificate cost disagrees with upper_bound")

    # Fresh context and fresh solvers are deliberately used here; no solver
    # object or model from the parallel run is trusted.
    ctx = z3.Context()
    translated = instance.translate(ctx)
    constants = _collect_constants(tuple(translated.hard) + tuple(s.formula for s in translated.soft))
    assignment = cert.get("assignment")
    if not isinstance(assignment, Mapping):
        raise CertificateError("certificate assignment is missing")
    hard_solver = z3.Solver(ctx=ctx)
    hard_solver.add(*translated.hard)
    for name, value in assignment.items():
        decl = constants.get(str(name))
        if decl is None:
            raise CertificateError(f"assignment names unknown symbol {name!r}")
        hard_solver.add(decl() == _value_for_sort(decl.range(), value, ctx))
    if hard_solver.check() != z3.sat:
        raise CertificateError("certificate assignment does not satisfy hard constraints")
    model = hard_solver.model()
    falsified = frozenset(s.index for s in translated.soft if not z3.is_true(model.eval(s.formula, model_completion=True)))
    objective = objective_for_weights(instance.weights)
    recomputed = objective.cost(falsified)
    if recomputed != reported_ub:
        raise CertificateError(f"recomputed incumbent cost {recomputed} != reported UB {reported_ub}")
    if "falsified" in cert and frozenset(int(i) for i in cert["falsified"]) != falsified:
        raise CertificateError("certificate falsified set disagrees with incumbent model")

    raw_cores = cert.get("cores")
    if not isinstance(raw_cores, list):
        raise CertificateError("certificate core collection is missing")
    cores: list[frozenset[int]] = []
    for raw_core in raw_cores:
        try:
            core = frozenset(int(i) for i in raw_core)
        except (TypeError, ValueError) as exc:
            raise CertificateError("invalid core encoding") from exc
        if any(i < 0 or i >= len(translated.soft) for i in core):
            raise CertificateError("certificate core index out of range")
        # A fresh Solver per core is part of the independent check.
        core_solver = z3.Solver(ctx=ctx)
        core_solver.add(*translated.hard)
        core_solver.add(*(translated.soft[i].formula for i in sorted(core)))
        if core_solver.check() != z3.unsat:
            raise CertificateError(f"recorded core is not unsatisfiable: {sorted(core)}")
        cores.append(core)
    computed_lb, hitting_set = objective.minimum_hitting_set(cores)
    if computed_lb != reported_lb:
        raise CertificateError(f"minimum hitting-set cost {computed_lb} != reported LB {reported_lb}")
    if "hitting_set" in cert:
        hs = frozenset(int(i) for i in cert["hitting_set"])
        if any(i < 0 or i >= len(translated.soft) for i in hs):
            raise CertificateError("certificate hitting set index out of range")
        if objective.cost(hs) != reported_lb or any(not (hs & core) for core in cores):
            raise CertificateError("certificate hitting set is not a minimum hitting set")


def _value_for_sort(sort: z3.SortRef, value: Any, ctx: z3.Context) -> z3.AstRef:
    if sort.kind() == z3.Z3_BOOL_SORT:
        if isinstance(value, bool):
            return z3.BoolVal(value, ctx=ctx)
        if str(value).lower() in {"true", "false"}:
            return z3.BoolVal(str(value).lower() == "true", ctx=ctx)
        raise CertificateError(f"invalid Boolean assignment value {value!r}")
    text = str(value)
    try:
        if sort.kind() == z3.Z3_INT_SORT:
            return z3.IntVal(text, ctx=ctx)
        if sort.kind() == z3.Z3_REAL_SORT:
            return z3.RealVal(text, ctx=ctx)
        if sort.kind() == z3.Z3_BV_SORT:
            return z3.BitVecVal(int(text, 0), sort.size(), ctx=ctx)
        if sort.kind() == z3.Z3_STRING_SORT:
            return z3.StringVal(text, ctx=ctx)
    except Exception:
        pass
    # Model sexprs such as ``(- 1)`` or ``(/ 1.0 2.0)`` are expressions, not
    # numeral strings. Parse them in a typed declaration script and return the
    # right-hand side of the equality.
    try:
        script = f"(declare-const __certificate_value {sort.sexpr()})\n(assert (= __certificate_value {text}))"
        parsed = z3.parse_smt2_string(script, ctx=ctx)
        return parsed[-1].arg(1)
    except Exception as exc:
        raise CertificateError(f"invalid value {value!r} for sort {sort}") from exc

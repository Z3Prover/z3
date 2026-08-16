"""WCNF and SMT-LIB2 MaxSMT readers."""
from __future__ import annotations

from pathlib import Path
from typing import Iterable

import z3

from .problem import Problem, _declarations_for_ast


def parse_file(path: str | Path, ctx: z3.Context | None = None) -> Problem:
    """Parse a revised/legacy WCNF file or an SMT-LIB2 ``assert-soft`` file."""
    p = Path(path)
    text = p.read_text(encoding="utf-8")
    suffix = p.suffix.lower()
    if suffix in {".wcnf", ".cnf", ".mwcnf"} or _looks_like_wcnf(text):
        return parse_wcnf(text, source_path=str(p), ctx=ctx)
    return parse_smt2_file(p, text=text, ctx=ctx)


def parse_wcnf(text: str, *, source_path: str | None = None, ctx: z3.Context | None = None) -> Problem:
    """Parse revised WCNF and legacy ``p wcnf``/``p cnf`` headers."""
    header_kind: str | None = None
    top: int | None = None
    clauses: list[tuple[str | int, list[int]]] = []
    max_var = 0
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("c") or line.startswith("#"):
            continue
        if line.startswith("p "):
            toks = line.split()
            if len(toks) >= 2:
                header_kind = toks[1].lower()
            if header_kind == "wcnf" and len(toks) >= 5:
                try:
                    top = int(toks[4])
                except ValueError:
                    top = None
            continue
        toks = line.split()
        if not toks:
            continue
        if header_kind == "cnf":
            # Plain DIMACS clauses have no weight prefix.  This prototype's
            # documented CNF mode treats each complete clause as unit-soft.
            marker: str | int = 1
            lit_toks = toks
        elif toks[0].lower() == "h":
            marker = "h"
            lit_toks = toks[1:]
        else:
            try:
                marker = int(toks[0])
            except ValueError as exc:
                raise ValueError(f"invalid WCNF clause prefix: {toks[0]!r}") from exc
            lit_toks = toks[1:]

        lits: list[int] = []
        terminated = False
        for tok in lit_toks:
            try:
                lit = int(tok)
            except ValueError as exc:
                raise ValueError(f"invalid DIMACS literal: {tok!r}") from exc
            if lit == 0:
                terminated = True
                break
            max_var = max(max_var, abs(lit))
            lits.append(lit)
        if not terminated:
            raise ValueError("WCNF clause must terminate with 0")
        clauses.append((marker, lits))

    ctx = ctx or z3.Context()
    vars_ = [z3.Bool(f"x{i}", ctx=ctx) for i in range(1, max_var + 1)]
    hard: list[z3.BoolRef] = []
    soft: list[tuple[z3.BoolRef, int]] = []
    for marker, lits in clauses:
        formula = _clause(lits, vars_, ctx)
        is_hard = marker == "h" or (
            top is not None and isinstance(marker, int) and marker >= top
        )
        if is_hard:
            hard.append(formula)
        else:
            if not isinstance(marker, int) or marker <= 0:
                raise ValueError("soft WCNF clauses require positive integer weights")
            soft.append((formula, marker))
    declarations = "\n".join(f"(declare-fun x{i} () Bool)" for i in range(1, max_var + 1))
    return Problem(
        hard,
        soft,
        declarations=declarations,
        source_format="wcnf",
        source_path=source_path,
        metadata={"variables": max_var, "header": header_kind, "top": top},
    )


def _clause(lits: Iterable[int], vars_: list[z3.BoolRef], ctx: z3.Context) -> z3.BoolRef:
    vals: list[z3.BoolRef] = []
    for lit in lits:
        v = vars_[abs(lit) - 1]
        vals.append(v if lit > 0 else z3.Not(v))
    if not vals:
        return z3.BoolVal(False, ctx=ctx)
    return vals[0] if len(vals) == 1 else z3.Or(vals)


def parse_smt2_file(path: str | Path, *, text: str | None = None, ctx: z3.Context | None = None) -> Problem:
    p = Path(path)
    text = p.read_text(encoding="utf-8") if text is None else text
    ctx = ctx or z3.Context()
    opt = z3.Optimize(ctx=ctx)
    try:
        opt.from_file(str(p))
    except z3.Z3Exception as exc:
        raise ValueError(f"could not parse SMT-LIB2 file {p}") from exc
    hard = list(opt.assertions())
    soft: list[tuple[z3.AstRef, int]] = []
    for objective in opt.objectives():
        formula_weights = _extract_assert_soft_objectives(objective)
        if formula_weights is None:
            raise ValueError(
                "SMT-LIB2 input contains an unsupported Optimize objective; "
                "expected assert-soft objectives of the form If(formula, 0, weight)"
            )
        soft.extend(formula_weights)
    expressions = hard + [f for f, _ in soft]
    declarations = _declarations_for_ast(expressions)
    return Problem(
        hard,
        soft,
        declarations=declarations,
        source_format="smt2",
        source_path=str(p),
        metadata={"objectives": len(soft), "input": str(p)},
    )


def _extract_assert_soft_objectives(obj: z3.AstRef) -> list[tuple[z3.AstRef, int]] | None:
    """Extract one or more assert-soft ITEs from Optimize's sum objective."""
    if obj.decl().kind() == z3.Z3_OP_ADD:
        result: list[tuple[z3.AstRef, int]] = []
        for child in obj.children():
            part = _extract_assert_soft_objectives(child)
            if part is None:
                return None
            result.extend(part)
        return result
    one = _extract_assert_soft_objective(obj)
    return [one] if one is not None else None


def _extract_assert_soft_objective(obj: z3.AstRef) -> tuple[z3.AstRef, int] | None:
    """Extract ``If(soft, 0, weight)`` from Optimize.assert_soft output."""
    candidate = obj
    if candidate.decl().kind() == z3.Z3_OP_UMINUS and candidate.num_args() == 1:
        candidate = candidate.arg(0)
    if candidate.decl().kind() != z3.Z3_OP_ITE or candidate.num_args() != 3:
        return None
    cond, when_true, when_false = candidate.children()
    if z3.is_rational_value(when_true) and when_true.as_long() == 0 and z3.is_rational_value(when_false):
        return cond, when_false.as_long()
    if z3.is_rational_value(when_false) and when_false.as_long() == 0 and z3.is_rational_value(when_true):
        return z3.Not(cond), when_true.as_long()
    return None


def _looks_like_wcnf(text: str) -> bool:
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith(("c", "#")):
            continue
        if line.startswith("p "):
            return len(line.split()) > 1 and line.split()[1].lower() in {"wcnf", "cnf"}
        if line.startswith("h "):
            return True
    return False

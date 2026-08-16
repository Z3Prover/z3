"""Parsers for the benchmark layer.

The public API is :func:`parse_file`, which returns a ``ParsedProblem`` with
``hard`` and ``soft`` members.  No global Z3 objects are cached: callers can
pass a fresh ``z3.Context`` to build a problem suitable for an isolated
worker thread.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Union

import z3


class ParseError(ValueError):
    """Raised when a benchmark is not a supported, well-formed instance."""


@dataclass
class ParsedProblem:
    """Common in-memory representation used by the prototype.

    ``soft`` preserves source order and stores ``(formula, positive_weight)``.
    ``context`` is the context supplied by the caller (or ``None`` for Z3's
    main context).
    """

    hard: list[z3.BoolRef]
    soft: list[tuple[z3.BoolRef, int]]
    context: Optional[z3.Context] = None


def _text_from_source(source: Union[str, Path]) -> tuple[str, str]:
    """Return ``(text, display_name)`` for a path or literal input text."""
    if isinstance(source, Path):
        path = source
    elif isinstance(source, str) and ("\n" in source or "\r" in source):
        return source, "<string>"
    else:
        path = Path(source)
    try:
        return path.read_text(encoding="utf-8"), str(path)
    except OSError as exc:
        raise ParseError(f"cannot read {path}: {exc}") from exc
    except UnicodeDecodeError as exc:
        raise ParseError(f"{path} is not valid UTF-8: {exc}") from exc


def _clause(literals: list[z3.BoolRef], ctx: Optional[z3.Context]) -> z3.BoolRef:
    if not literals:
        return z3.BoolVal(False, ctx=ctx)
    return z3.Or(literals)


def _literal(token: str, ctx: Optional[z3.Context], name: str, line_no: int) -> z3.BoolRef:
    try:
        value = int(token, 10)
    except ValueError as exc:
        raise ParseError(f"{name}:{line_no}: expected integer literal, got {token!r}") from exc
    if value == 0:
        raise ParseError(f"{name}:{line_no}: zero is only allowed as a clause terminator")
    atom = z3.Bool(f"x{abs(value)}", ctx=ctx)
    return atom if value > 0 else z3.Not(atom)


def parse_wcnf(source: Union[str, Path], ctx: Optional[z3.Context] = None) -> ParsedProblem:
    """Parse new-format WCNF and old ``p wcnf``/``p cnf`` DIMACS.

    New-format clauses use ``h <literals> 0`` for hard clauses and
    ``<weight> <literals> 0`` for soft clauses.  In old ``p wcnf`` files,
    weights greater than or equal to the header's ``top`` value are hard.
    Plain ``p cnf`` has no hard/soft marker, so clauses are interpreted as
    unit-weight soft clauses (the useful MaxSAT interpretation); this is
    documented in the benchmark README.
    """
    text, name = _text_from_source(source)
    header_kind: Optional[str] = None
    declared_vars: Optional[int] = None
    declared_clauses: Optional[int] = None
    top: Optional[int] = None
    clauses: list[tuple[Optional[int], list[int], int]] = []

    for line_no, raw_line in enumerate(text.splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("c") or line.startswith("#"):
            continue
        tokens = line.split()
        if tokens[0].lower() == "p":
            if header_kind is not None:
                raise ParseError(f"{name}:{line_no}: duplicate DIMACS header")
            if len(tokens) < 4:
                raise ParseError(f"{name}:{line_no}: malformed DIMACS header")
            header_kind = tokens[1].lower()
            if header_kind not in {"wcnf", "cnf"}:
                raise ParseError(f"{name}:{line_no}: unsupported DIMACS kind {tokens[1]!r}")
            try:
                declared_vars = int(tokens[2], 10)
                declared_clauses = int(tokens[3], 10)
                if declared_vars < 0 or declared_clauses < 0:
                    raise ValueError
                if header_kind == "wcnf":
                    if len(tokens) < 5:
                        raise ValueError("missing top weight")
                    top = int(tokens[4], 10)
                    if top <= 0:
                        raise ValueError("top weight must be positive")
            except ValueError as exc:
                raise ParseError(f"{name}:{line_no}: malformed DIMACS header values") from exc
            continue

        is_new_hard = tokens[0].lower() == "h"
        if is_new_hard:
            if len(tokens) < 2:
                raise ParseError(f"{name}:{line_no}: hard clause has no terminator")
            clause_tokens = tokens[1:]
            weight: Optional[int] = None
        elif header_kind == "cnf":
            clause_tokens = tokens
            weight = 1
        else:
            try:
                weight = int(tokens[0], 10)
            except ValueError as exc:
                raise ParseError(
                    f"{name}:{line_no}: expected 'h' or integer weight prefix"
                ) from exc
            if weight <= 0:
                raise ParseError(f"{name}:{line_no}: soft weight must be positive")
            clause_tokens = tokens[1:]

        if not clause_tokens or clause_tokens[-1] != "0":
            raise ParseError(f"{name}:{line_no}: clause must end with 0")
        if any(tok == "0" for tok in clause_tokens[:-1]):
            raise ParseError(f"{name}:{line_no}: tokens after an early zero")
        literal_tokens = clause_tokens[:-1]
        values: list[int] = []
        literals: list[z3.BoolRef] = []
        for tok in literal_tokens:
            lit = _literal(tok, ctx, name, line_no)
            try:
                value = int(tok, 10)
            except ValueError:  # _literal already emits the useful message.
                raise AssertionError("unreachable")
            if declared_vars is not None and abs(value) > declared_vars:
                raise ParseError(
                    f"{name}:{line_no}: variable {abs(value)} exceeds header nvars {declared_vars}"
                )
            values.append(value)
            literals.append(lit)
        clauses.append((weight, values, line_no))

    if header_kind is None and not clauses:
        raise ParseError(f"{name}: no DIMACS header or clauses found")
    if declared_clauses is not None and declared_clauses != len(clauses):
        raise ParseError(
            f"{name}: header declares {declared_clauses} clauses, found {len(clauses)}"
        )

    hard: list[z3.BoolRef] = []
    soft: list[tuple[z3.BoolRef, int]] = []
    for weight, values, _line_no in clauses:
        formula = _clause(
            [
                (z3.Bool(f"x{abs(v)}", ctx=ctx) if v > 0 else z3.Not(z3.Bool(f"x{abs(v)}", ctx=ctx)))
                for v in values
            ],
            ctx,
        )
        if is_hard := (weight is None or (header_kind == "wcnf" and top is not None and weight >= top)):
            hard.append(formula)
        else:
            soft.append((formula, int(weight)))
    return ParsedProblem(hard=hard, soft=soft, context=ctx)


def _is_zero(expr: z3.ExprRef) -> bool:
    if z3.is_int_value(expr):
        return expr.as_long() == 0
    return z3.is_rational_value(expr) and expr.numerator_as_long() == 0


def _extract_soft_terms(expr: z3.ExprRef) -> list[tuple[z3.BoolRef, int]]:
    """Extract Z3's ``If(soft, 0, weight)`` objective terms recursively."""
    if z3.is_app(expr) and expr.decl().kind() == z3.Z3_OP_ITE and expr.num_args() == 3:
        condition, when_true, when_false = expr.children()
        is_integral_weight = z3.is_int_value(when_false) or (
            z3.is_rational_value(when_false) and when_false.denominator_as_long() == 1
        )
        if z3.is_bool(condition) and _is_zero(when_true) and is_integral_weight:
            weight = (
                when_false.as_long()
                if z3.is_int_value(when_false)
                else when_false.numerator_as_long()
            )
            if weight <= 0:
                raise ParseError(f"assert-soft weight must be positive, got {weight}")
            return [(condition, weight)]
    if z3.is_app(expr):
        result: list[tuple[z3.BoolRef, int]] = []
        for child in expr.children():
            result.extend(_extract_soft_terms(child))
        return result
    return []


def parse_smt2(source: Union[str, Path], ctx: Optional[z3.Context] = None) -> ParsedProblem:
    """Parse an SMT-LIB2 optimization file via ``Optimize.from_file``.

    Z3 represents each ``assert-soft`` in an objective as ``If(formula, 0,
    weight)``.  The terms are recursively recovered from ``objectives()`` so
    source weights are retained.  Files with only ordinary ``minimize``/
    ``maximize`` objectives are rejected because they do not define the
    MaxSMT soft-constraint interface.
    """
    text, name = _text_from_source(source)
    # Optimize.from_file accepts a path, not an input string.  Keep parsing
    # pure by using a temporary file only for literal input text.
    temporary: Optional[Path] = None
    path = Path(name)
    try:
        if name == "<string>":
            import tempfile

            fd, temp_name = tempfile.mkstemp(suffix=".smt2")
            import os

            os.close(fd)
            temporary = Path(temp_name)
            temporary.write_text(text, encoding="utf-8")
            path = temporary
        opt = z3.Optimize(ctx=ctx)
        try:
            opt.from_file(str(path))
        except z3.Z3Exception as exc:
            raise ParseError(f"{name}: invalid SMT-LIB2 optimization input: {exc}") from exc
        hard = list(opt.assertions())
        soft: list[tuple[z3.BoolRef, int]] = []
        for objective in opt.objectives():
            soft.extend(_extract_soft_terms(objective))
        if not soft:
            raise ParseError(f"{name}: no assert-soft constraints found in objectives()")
        return ParsedProblem(hard=hard, soft=soft, context=ctx)
    finally:
        if temporary is not None:
            try:
                temporary.unlink()
            except OSError:
                pass


def parse_file(path: Union[str, Path], ctx: Optional[z3.Context] = None) -> ParsedProblem:
    """Dispatch to WCNF/CNF or SMT-LIB2 based on the filename suffix."""
    suffix = Path(path).suffix.lower()
    if suffix in {".smt", ".smt2", ".smtlib"}:
        return parse_smt2(path, ctx=ctx)
    if suffix in {".wcnf", ".cnf", ".dimacs"}:
        return parse_wcnf(path, ctx=ctx)
    raise ParseError(f"unsupported benchmark extension {suffix!r} for {path}")


# Short alias useful to callers that already use ``parse`` as their loader.
parse = parse_file

__all__ = ["ParseError", "ParsedProblem", "parse", "parse_file", "parse_smt2", "parse_wcnf"]

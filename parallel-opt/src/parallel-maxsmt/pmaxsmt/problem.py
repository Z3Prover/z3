"""Context-neutral MaxSMT problem representation.

``Problem`` stores formulas as SMT-LIB expressions plus declarations.  That is
intentional: a worker receives only strings/integers and reconstructs every Z3
AST in its own isolated context.  ``TranslatedProblem`` is private to the
calling thread and is the only object exposing ASTs.
"""
from __future__ import annotations

from dataclasses import dataclass
import re
import threading
from typing import Any, Callable, Iterable, Sequence

import z3


# Creating tens of thousands of Python AST wrappers concurrently magnifies the
# process-wide z3py reference-count lock contention.  Keep the fast,
# context-local batch parses sequential instead of letting them contend for
# that lock for an order of magnitude longer.
_TRANSLATION_PARSE_LOCK = threading.Lock()


@dataclass(frozen=True)
class SoftConstraint:
    index: int
    formula: str
    weight: int = 1
    name: str | None = None

    def __post_init__(self) -> None:
        if self.index < 0:
            raise ValueError("soft index must be non-negative")
        if int(self.weight) <= 0:
            raise ValueError("soft weight must be a positive integer")
        object.__setattr__(self, "weight", int(self.weight))


@dataclass(frozen=True)
class TranslatedSoftConstraint:
    index: int
    formula: z3.BoolRef
    weight: int
    name: str | None = None


@dataclass(frozen=True)
class TranslatedProblem:
    context: z3.Context
    hard: tuple[z3.BoolRef, ...]
    soft: tuple[TranslatedSoftConstraint, ...]

    @property
    def soft_formulas(self) -> tuple[z3.BoolRef, ...]:
        return tuple(s.formula for s in self.soft)


@dataclass(frozen=True, init=False)
class Problem:
    """A serializable hard/soft MaxSMT instance.

    The constructor accepts Z3 expressions or expression strings.  For string
    expressions, ``declarations`` must contain declarations needed by those
    expressions.  ``from_formulas`` is convenient for constructing instances
    from expressions in tests and applications.
    """

    hard: tuple[str, ...]
    soft: tuple[SoftConstraint, ...]
    declarations: str
    source_format: str
    source_path: str | None
    metadata: dict[str, Any]

    def __init__(
        self,
        hard: Sequence[Any] = (),
        soft: Sequence[Any] = (),
        *,
        declarations: str = "",
        source_format: str = "programmatic",
        source_path: str | None = None,
        metadata: dict[str, Any] | None = None,
    ) -> None:
        hard_values = tuple(_expr_text(x) for x in hard)
        soft_values: list[SoftConstraint] = []
        for idx, item in enumerate(soft):
            if isinstance(item, SoftConstraint):
                if item.index != idx:
                    soft_values.append(SoftConstraint(idx, item.formula, item.weight, item.name))
                else:
                    soft_values.append(item)
                continue
            if isinstance(item, tuple) and len(item) in (2, 3):
                formula = _expr_text(item[0])
                weight = int(item[1])
                name = item[2] if len(item) == 3 else None
            else:
                formula, weight, name = _expr_text(item), 1, None
            soft_values.append(SoftConstraint(idx, formula, weight, name))
        object.__setattr__(self, "hard", hard_values)
        object.__setattr__(self, "soft", tuple(soft_values))
        object.__setattr__(self, "declarations", declarations.strip())
        object.__setattr__(self, "source_format", source_format)
        object.__setattr__(self, "source_path", source_path)
        object.__setattr__(self, "metadata", dict(metadata or {}))

    @classmethod
    def from_formulas(
        cls,
        hard: Sequence[Any],
        soft: Sequence[Any],
        *,
        source_format: str = "programmatic",
        source_path: str | None = None,
        metadata: dict[str, Any] | None = None,
    ) -> "Problem":
        all_expr = list(hard) + [_soft_formula(x) for x in soft]
        declarations = _declarations_for_ast(all_expr)
        return cls(
            hard,
            soft,
            declarations=declarations,
            source_format=source_format,
            source_path=source_path,
            metadata=metadata,
        )

    @classmethod
    def from_payload(cls, payload: dict[str, Any]) -> "Problem":
        """Rebuild a problem from a JSON-safe worker payload."""
        soft = [
            SoftConstraint(int(s["index"]), str(s["formula"]), int(s["weight"]), s.get("name"))
            for s in payload.get("soft", [])
        ]
        return cls(
            tuple(str(x) for x in payload.get("hard", [])),
            soft,
            declarations=str(payload.get("declarations", "")),
            source_format=str(payload.get("source_format", "payload")),
            source_path=payload.get("source_path"),
            metadata=payload.get("metadata", {}),
        )

    def to_payload(self) -> dict[str, Any]:
        return {
            "hard": list(self.hard),
            "soft": [
                {"index": s.index, "formula": s.formula, "weight": s.weight, "name": s.name}
                for s in self.soft
            ],
            "declarations": self.declarations,
            "source_format": self.source_format,
            "source_path": self.source_path,
            "metadata": dict(self.metadata),
        }

    @property
    def weights(self) -> tuple[int, ...]:
        return tuple(s.weight for s in self.soft)

    @property
    def is_weighted(self) -> bool:
        return any(w != 1 for w in self.weights)

    def translate(
        self,
        ctx: z3.Context | None = None,
        *,
        interrupted: Callable[[], bool] | None = None,
    ) -> TranslatedProblem:
        """Parse all formulas into ``ctx`` in one context-local text round-trip."""
        ctx = ctx or z3.Context()
        texts = self.hard + tuple(item.formula for item in self.soft)
        formulas = _parse_exprs(
            texts,
            self.declarations,
            ctx,
            interrupted=interrupted,
        )
        hard_count = len(self.hard)
        hard = formulas[:hard_count]
        soft = tuple(
            TranslatedSoftConstraint(
                item.index,
                formulas[hard_count + offset],
                item.weight,
                item.name,
            )
            for offset, item in enumerate(self.soft)
        )
        return TranslatedProblem(ctx, hard, soft)

    def source_script(self) -> str:
        lines: list[str] = []
        if self.declarations:
            lines.append(self.declarations)
        for h in self.hard:
            lines.append(f"(assert {h})")
        for s in self.soft:
            weight = s.weight
            lines.append(f"(assert-soft {s.formula} :weight {weight})")
        return "\n".join(lines) + "\n"


def _soft_formula(item: Any) -> Any:
    if isinstance(item, SoftConstraint):
        return item.formula
    if isinstance(item, tuple):
        return item[0]
    return item


def _expr_text(expr: Any) -> str:
    if isinstance(expr, str):
        return expr.strip()
    if isinstance(expr, z3.AstRef):
        return expr.sexpr()
    if isinstance(expr, bool):
        return "true" if expr else "false"
    raise TypeError(f"expected a Z3 expression or SMT-LIB expression, got {type(expr)!r}")


def _parse_exprs(
    expressions: Sequence[str],
    declarations: str,
    ctx: z3.Context,
    *,
    interrupted: Callable[[], bool] | None = None,
) -> tuple[z3.BoolRef, ...]:
    assertions: list[str] = []
    for expression in expressions:
        if interrupted is not None and interrupted():
            raise InterruptedError("problem translation interrupted")
        assertions.append(f"(assert {expression})")
    if interrupted is not None and interrupted():
        raise InterruptedError("problem translation interrupted")
    script = "\n".join(
        ([declarations] if declarations else []) + assertions
    )
    if script:
        script += "\n"
    with _TRANSLATION_PARSE_LOCK:
        if interrupted is not None and interrupted():
            raise InterruptedError("problem translation interrupted")
        try:
            parsed = z3.parse_smt2_string(script, ctx=ctx)
        except z3.Z3Exception as exc:
            raise ValueError("could not reconstruct formulas in worker context") from exc
        if interrupted is not None and interrupted():
            raise InterruptedError("problem translation interrupted")
        if len(parsed) != len(expressions):
            raise ValueError(
                f"parsed {len(parsed)} formulas, expected {len(expressions)}"
            )
        # Indexing the AstVector creates the Python AstRef wrappers, so it must
        # remain under the same lock as parsing to avoid refcount contention.
        formulas = tuple(parsed[index] for index in range(len(parsed)))
    return formulas


def _split_commands(script: str) -> list[str]:
    """Split top-level SMT-LIB commands, respecting strings and comments."""
    commands: list[str] = []
    start: int | None = None
    depth = 0
    in_string = False
    escaped = False
    i = 0
    while i < len(script):
        ch = script[i]
        if ch == ";" and not in_string:
            j = script.find("\n", i)
            i = len(script) if j < 0 else j + 1
            continue
        if ch == '"' and not escaped:
            in_string = not in_string
        if ch == "\\" and in_string and not escaped:
            escaped = True
        else:
            escaped = False
        if not in_string:
            if ch == "(" and depth == 0:
                start = i
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and start is not None:
                    commands.append(script[start : i + 1].strip())
                    start = None
        i += 1
    return commands


def _declarations_for_ast(expressions: Iterable[Any]) -> str:
    asts = [e for e in expressions if isinstance(e, z3.AstRef)]
    if not asts:
        return ""
    ctx = asts[0].ctx
    solver = z3.Solver(ctx=ctx)
    for e in asts:
        solver.add(e)
    commands = _split_commands(solver.sexpr())
    return "\n".join(c for c in commands if c.startswith("(declare-") or c.startswith("(define-"))


_SMT_SYMBOL = r"(?:\|[^|]*\||[^\s()]+)"
_DECLARE_CONST = re.compile(rf"^\(declare-const\s+({_SMT_SYMBOL})\s+")
_DECLARE_FUN0 = re.compile(
    rf"^\((?:declare-fun|define-fun)\s+({_SMT_SYMBOL})\s+\(\s*\)\s+"
)


def _constant_declaration_tokens(declarations: str) -> dict[str, str]:
    """Map z3py constant names to their original, safely quoted SMT tokens."""
    result: dict[str, str] = {}
    for command in _split_commands(declarations):
        match = _DECLARE_CONST.match(command) or _DECLARE_FUN0.match(command)
        if match is None:
            continue
        token = match.group(1)
        # z3py returns the unquoted symbol name for declarations reconstructed
        # from SMT-LIB.  Preserve the source token for safe binding assertions.
        name = token[1:-1] if token.startswith("|") and token.endswith("|") else token
        result.setdefault(name, token)
    return result


def _collect_constants(
    exprs: Iterable[z3.AstRef],
    interrupted: Callable[[], bool] | None = None,
) -> dict[str, z3.FuncDeclRef]:
    result: dict[str, z3.FuncDeclRef] = {}
    seen: set[int] = set()

    def visit(e: z3.AstRef) -> None:
        if interrupted is not None and interrupted():
            raise InterruptedError("symbol collection interrupted")
        # ``hash(e)`` is stable inside this context and avoids recursively
        # walking the same expression DAG many times.
        try:
            key = hash(e)
        except Exception:
            key = id(e)
        if key in seen:
            return
        seen.add(key)
        if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            result.setdefault(e.decl().name(), e.decl())
        for child in e.children():
            visit(child)

    for expr in exprs:
        if interrupted is not None and interrupted():
            raise InterruptedError("symbol collection interrupted")
        visit(expr)
    return result

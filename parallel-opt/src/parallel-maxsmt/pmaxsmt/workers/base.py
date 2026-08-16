"""Worker primitives and context-local model serialization."""
from __future__ import annotations

import random
import threading
from typing import Callable, Iterable

import z3

from ..coordinator import Coordinator, CoordinatorSnapshot
from ..objective import objective_for_weights
from ..problem import (
    Problem,
    TranslatedProblem,
    _constant_declaration_tokens,
    _split_commands,
)


# z3py 5.0.0 increments and decrements native AST references from whichever
# Python thread creates or releases an AstRef.  Different Z3 contexts may run
# native checks concurrently, but racing these wrapper-level refcount calls
# corrupted models under the eight-worker stress test.  Serialize wrapper-level
# reference activity rather than solver checks, preserving parallel search.
_Z3_AST_REF_LOCK = threading.RLock()
_z3py = z3.z3
if not getattr(_z3py.Z3_inc_ref, "_pmaxsmt_locked", False):
    _z3_inc_ref = _z3py.Z3_inc_ref
    _z3_dec_ref = _z3py.Z3_dec_ref

    def _locked_inc_ref(*args):
        with _Z3_AST_REF_LOCK:
            return _z3_inc_ref(*args)

    def _locked_dec_ref(*args):
        with _Z3_AST_REF_LOCK:
            return _z3_dec_ref(*args)

    _locked_inc_ref._pmaxsmt_locked = True
    _locked_dec_ref._pmaxsmt_locked = True
    _z3py.Z3_inc_ref = _locked_inc_ref
    _z3py.Z3_dec_ref = _locked_dec_ref



def _take_smt_term(text: str, start: int) -> tuple[str, int]:
    """Return one SMT-LIB term/token and the following offset."""
    length = len(text)
    while start < length and text[start].isspace():
        start += 1
    if start >= length:
        return "", start
    if text[start] == "(":
        depth = 0
        in_string = False
        index = start
        while index < length:
            char = text[index]
            if char == '"':
                if in_string and index + 1 < length and text[index + 1] == '"':
                    index += 2
                    continue
                in_string = not in_string
            elif not in_string:
                if char == "(":
                    depth += 1
                elif char == ")":
                    depth -= 1
                    if depth == 0:
                        return text[start : index + 1], index + 1
            index += 1
        return text[start:], length
    if text[start] == '"':
        index = start + 1
        while index < length:
            if text[index] == '"':
                if index + 1 < length and text[index + 1] == '"':
                    index += 2
                    continue
                return text[start : index + 1], index + 1
            index += 1
        return text[start:], length
    if text[start] == "|":
        end = text.find("|", start + 1)
        end = length - 1 if end < 0 else end
        return text[start : end + 1], end + 1
    end = start
    while end < length and not text[end].isspace() and text[end] not in "()":
        end += 1
    return text[start:end], end


def _model_definitions(model: z3.ModelRef) -> Iterable[tuple[str, bool | str]]:
    """Serialize zero-arity model definitions without 34k wrapper eval calls."""
    for command in _split_commands(model.sexpr()):
        content = command[1:-1]
        keyword, offset = _take_smt_term(content, 0)
        if keyword != "define-fun":
            continue
        token, offset = _take_smt_term(content, offset)
        arguments, offset = _take_smt_term(content, offset)
        _sort, offset = _take_smt_term(content, offset)
        value, _ = _take_smt_term(content, offset)
        if arguments.replace(" ", "") != "()" or not token or not value:
            continue
        name = token[1:-1] if token.startswith("|") and token.endswith("|") else token
        yield name, True if value == "true" else False if value == "false" else value

class WorkerBase(threading.Thread):
    daemon = True

    def __init__(
        self,
        worker_id: str,
        role: str,
        problem_payload: dict,
        coordinator: Coordinator,
        stop_event: threading.Event,
        *,
        seed: int = 0,
        check_timeout_ms: int = 250,
        startup_barrier: threading.Barrier | None = None,
    ) -> None:
        super().__init__(name=f"pmaxsmt-{role}-{worker_id}")
        self.worker_id = str(worker_id)
        self.role = role
        self.problem_payload = problem_payload
        self.coordinator = coordinator
        self.stop_event = stop_event
        self.seed = int(seed)
        self.rng = random.Random(self.seed)
        self.check_timeout_ms = max(1, int(check_timeout_ms))
        self.startup_barrier = startup_barrier
        self.ctx: z3.Context | None = None
        self.translated: TranslatedProblem | None = None
        self.problem: Problem | None = None
        self.objective = objective_for_weights([s["weight"] for s in problem_payload.get("soft", [])])
        self.error: str | None = None
        self.invalid_model_count = 0
        cached_tokens = problem_payload.get("_constant_tokens")
        self._original_constant_tokens: dict[str, str] = (
            cached_tokens
            if isinstance(cached_tokens, dict)
            else _constant_declaration_tokens(str(problem_payload.get("declarations", "")))
        )
        self._context_lifecycle_lock = threading.Lock()

        self.coordinator.register_worker(self.worker_id, self.role)

    def run(self) -> None:
        try:
            # Context and every AST are created by this thread.  The only
            # context operation performed externally during shutdown is the
            # documented interrupt() call.
            self.ctx = z3.Context()
            self.problem = Problem.from_payload(self.problem_payload)
            self.translated = self.problem.translate(self.ctx, interrupted=self.interrupted)
            if self.startup_barrier is not None:
                self.startup_barrier.wait()

            self.run_worker()
        except Exception as exc:  # workers must not silently disappear
            if not self.stop_event.is_set() and not self.coordinator.is_done():
                self.error = f"{type(exc).__name__}: {exc}"
                self.coordinator.trace.emit(self.worker_id, self.role, "error", status="UNKNOWN", message=self.error)
        finally:
            # Drop persistent AST references on their owning worker thread.
            # The inc/dec lock above also protects unavoidable late temporary
            # cleanup, while this keeps the common teardown path lock-free.
            if self.startup_barrier is not None:
                self.startup_barrier.abort()
            self._release_context_objects()
            self.coordinator.worker_done(self.worker_id)

    def _release_context_objects(self) -> None:
        """Delete the owned context once instead of decrementing every AST.

        All ASTs are private to this worker and no native solver call remains
        when ``finally`` runs.  Deleting the owning reference-counted context
        first makes subsequent AstRef finalizers no-ops, avoiding tens of
        thousands of serialized ``Z3_dec_ref`` calls during shutdown.
        """
        with self._context_lifecycle_lock:
            ctx = self.ctx
            if ctx is not None and ctx.ref() is not None:
                # Context deletion is one short native lifetime operation; use
                # the same process-wide order as wrapper inc/dec calls.
                with _Z3_AST_REF_LOCK:
                    z3.z3.Z3_del_context(ctx.ref())
                ctx.owner = False
                ctx.ctx = None
                ctx.eh = None
            self.translated = None
            self.ctx = None

    def run_worker(self) -> None:
        raise NotImplementedError

    def snapshot(self) -> CoordinatorSnapshot:
        return self.coordinator.snapshot()

    def wait(self, version: int, seconds: float = 0.02) -> CoordinatorSnapshot:
        return self.coordinator.wait_for_update(version, seconds)

    def interrupted(self) -> bool:
        return self.stop_event.is_set() or self.coordinator.is_done()

    def interrupt(self) -> None:
        # Serialize the one permitted cross-thread context operation with the
        # owning worker's final Z3_del_context call.
        with self._context_lifecycle_lock:
            if self.ctx is not None:
                try:
                    self.ctx.interrupt()
                except Exception:
                    pass

    def _optimize(self) -> z3.Optimize:
        assert self.ctx is not None
        optimize = z3.Optimize(ctx=self.ctx)
        optimize.set(timeout=self.check_timeout_ms)
        return optimize

    def _model_payload(self, model: z3.ModelRef) -> dict[str, bool | str]:
        # The declaration-derived name set is immutable and cached once for the
        # worker.  Re-walking every hard and soft formula cost seconds on the
        # 40k-soft evaluation instances and produced the same set each time.
        originals = self._original_constant_tokens
        result: dict[str, bool | str] = {}
        for name, value in _model_definitions(model):
            if self.interrupted():
                raise InterruptedError("model serialization interrupted")
            if name in originals:
                result[name] = value
        return result

    def _falsified(self, model: z3.ModelRef) -> frozenset[int]:
        assert self.translated is not None
        result: set[int] = set()
        for soft in self.translated.soft:
            if self.interrupted():
                raise InterruptedError("model measurement interrupted")
            if not z3.is_true(model.eval(soft.formula, model_completion=True)):
                result.add(soft.index)
        return frozenset(result)

    def _publish_model(self, model: z3.ModelRef) -> bool:
        """Measure and publish without holding the process-wide refcount lock.

        Individual z3py inc/dec operations still take ``_Z3_AST_REF_LOCK`` via
        the wrappers above.  The lock is always released before entering the
        coordinator, establishing the sole lock order: refcount, then none,
        then coordinator.
        """
        return self._publish_model_locked(model)

    def _publish_model_locked(self, model: z3.ModelRef) -> bool:
        """Publish a model only after validating hard constraints locally."""
        assert self.translated is not None
        if self.interrupted():
            return False
        violated: list[int] = []
        for index, hard in enumerate(self.translated.hard):
            if self.interrupted():
                return False
            if not z3.is_true(model.eval(hard, model_completion=True)):
                violated.append(index)
        if violated:
            self.invalid_model_count += 1
            snap = self.snapshot()
            self.coordinator.trace.emit(
                self.worker_id,
                self.role,
                "invalid_model_discarded",
                snap.lower_bound,
                snap.upper_bound,
                snap.status,
                violated_hard=len(violated),
                first_violated_hard=violated[0],
            )
            return False
        falsified = self._falsified(model)
        assignment = self._model_payload(model)
        # Correction sets are heuristic data.  They are still published for
        # every feasible model, including models that do not improve the
        # incumbent, but are kept entirely out of the proof lower bound.
        self.coordinator.publish_correction_set(self.worker_id, self.role, falsified, original=True)
        return self.coordinator.publish_model(
            self.worker_id,
            self.role,
            assignment,
            falsified,
            self.objective.cost(falsified),
        )

    def _assumption_problem(self, enabled: Iterable[int]) -> tuple[z3.Solver, dict[int, z3.BoolRef]]:
        """Build hard constraints and selector implications for soft IDs."""
        assert self.translated is not None and self.ctx is not None
        solver = z3.Solver(ctx=self.ctx)
        solver.set(timeout=self.check_timeout_ms)
        solver.add(*self.translated.hard)
        selectors: dict[int, z3.BoolRef] = {}
        for soft in self.translated.soft:
            if self.interrupted():
                raise InterruptedError("assumption construction interrupted")
            selector = z3.Bool(
                f"{self.role}_{self.worker_id}_sel_{soft.index}", ctx=self.ctx
            )
            selectors[soft.index] = selector
            solver.add(z3.Implies(selector, soft.formula))
        return solver, {index: selectors[index] for index in enabled}

    def _extract_original_core(self, solver: z3.Solver, selectors: dict[int, z3.BoolRef]) -> frozenset[int]:
        reverse = {str(value): index for index, value in selectors.items()}
        return frozenset(
            reverse[str(assumption)]
            for assumption in solver.unsat_core()
            if str(assumption) in reverse
        )


def boolean_symbols(
    translated: TranslatedProblem,
    interrupted: Callable[[], bool] | None = None,
) -> dict[str, z3.BoolRef]:
    result: dict[str, z3.BoolRef] = {}
    seen: set[int] = set()

    def walk(expression: z3.AstRef) -> None:
        if interrupted is not None and interrupted():
            raise InterruptedError("Boolean symbol collection interrupted")
        try:
            key = hash(expression)
        except Exception:
            key = id(expression)
        if key in seen:
            return
        seen.add(key)
        if (
            z3.is_const(expression)
            and expression.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and expression.sort().kind() == z3.Z3_BOOL_SORT
        ):
            result.setdefault(str(expression.decl().name()), expression)
        for child in expression.children():
            walk(child)

    for expression in translated.hard:
        walk(expression)
    for soft in translated.soft:
        walk(soft.formula)
    return result

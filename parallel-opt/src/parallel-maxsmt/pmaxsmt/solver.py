"""Parallel anytime driver and Z3 baseline."""
from __future__ import annotations

from dataclasses import dataclass, asdict
from pathlib import Path
import threading
import time
from typing import Any

import z3

from .certify import verify_certificate_or_raise
from .coordinator import Coordinator
from .objective import objective_for_weights
from .parse import parse_file
from .problem import Problem, _constant_declaration_tokens, _parse_exprs
from .roles import RoleSpec, default_roles
from .trace import TraceWriter
from .workers import BackboneWorker, HSWorker, MSSWorker, MaxResWorker, ZOptWorker


@dataclass(frozen=True)
class SolveResult:
    status: str
    lower_bound: int
    upper_bound: int | None
    assignment: dict[str, bool | str] | None
    falsified: frozenset[int] | None
    certificate: dict[str, Any] | None
    elapsed: float
    roles: dict[str, int]
    worker_errors: dict[str, str]
    threads_alive: tuple[str, ...]

    def as_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["falsified"] = sorted(self.falsified) if self.falsified is not None else None
        value["threads_alive"] = list(self.threads_alive)
        return value


def _incumbent_is_feasible(
    problem: Problem,
    assignment: dict[str, bool | str],
    falsified: frozenset[int],
    upper_bound: int,
) -> bool:
    """Rebuild and remeasure an incumbent in a caller-owned fresh context.

    Assignment equalities are parsed in the same batch as the original
    formulas.  This preserves the independent context boundary without the
    former full AST walk and 34k individual ``Solver.add`` calls.
    """
    try:
        tokens = _constant_declaration_tokens(problem.declarations)
        bindings: list[str] = []
        for name, value in assignment.items():
            token = tokens.get(str(name))
            if token is None:
                return False
            value_text = (
                "true" if value is True else "false" if value is False else str(value)
            )
            bindings.append(f"(= {token} {value_text})")

        ctx = z3.Context()
        expressions = (
            *problem.hard,
            *(soft.formula for soft in problem.soft),
            *bindings,
        )
        parsed = _parse_exprs(expressions, problem.declarations, ctx)
        hard_end = len(problem.hard)
        soft_end = hard_end + len(problem.soft)
        solver = z3.Solver(ctx=ctx)
        solver.add(*parsed[:hard_end])
        solver.add(*parsed[soft_end:])
        if solver.check() != z3.sat:
            return False
        model = solver.model()
        measured_falsified = frozenset(
            soft.index
            for soft, formula in zip(problem.soft, parsed[hard_end:soft_end])
            if not z3.is_true(model.eval(formula, model_completion=True))
        )
        return measured_falsified == falsified and (
            objective_for_weights(problem.weights).cost(measured_falsified)
            == upper_bound
        )
    except (InterruptedError, ValueError, z3.Z3Exception):
        return False


def _finalization_reserve(problem: Problem) -> tuple[float, float]:
    """Estimate shutdown and fresh-gate time from immutable problem size.

    The coefficients include headroom over measured 40k-soft costs on the
    supported Python/Z3 versions.  They reserve work inside the caller's
    budget rather than extending the timeout after search ends.
    """
    formula_count = len(problem.hard) + len(problem.soft)
    constant_count = len(_constant_declaration_tokens(problem.declarations))
    shutdown = 0.25 + formula_count * 0.000007
    gate = 0.10 + (formula_count + constant_count) * 0.000030
    return shutdown, gate


class ParallelMaxSMTSolver:
    """Asynchronous static-role parallel MaxSMT prototype."""

    def __init__(
        self,
        problem: Problem | str | Path,
        *,
        roles: RoleSpec | None = None,
        threads: int | None = None,
        seed: int = 0,
        timeout: float | None = None,
        trace: TraceWriter | None = None,
        check_timeout_ms: int = 250,
        verify_optimal: bool = True,
    ) -> None:
        self.problem = parse_file(problem) if isinstance(problem, (str, Path)) else problem
        if threads is None:
            threads = roles.total if roles is not None else 1
        self.roles = roles or default_roles(threads)
        if self.roles.total != threads:
            raise ValueError("role allocation total must equal thread count")
        self.seed = int(seed)
        self.timeout = timeout
        self.trace = trace or TraceWriter()
        self.check_timeout_ms = max(1, int(check_timeout_ms))
        self.verify_optimal = bool(verify_optimal)
        self.stop_event = threading.Event()
        self.coordinator = Coordinator(
            objective_for_weights(self.problem.weights),
            len(self.problem.soft),
            trace=self.trace,
        )
        self.workers: list[threading.Thread] = []
        self._startup_barrier: threading.Barrier | None = None

    def _make_workers(self) -> list[threading.Thread]:
        classes = {
            "hs": HSWorker,
            "mss": MSSWorker,
            "backbone": BackboneWorker,
            "maxres": MaxResWorker,
            "zopt": ZOptWorker,
        }
        payload = self.problem.to_payload()
        # Every worker shares this immutable declaration-derived cache.  Model
        # publication no longer re-walks all formulas for every incumbent.
        payload["_constant_tokens"] = _constant_declaration_tokens(
            self.problem.declarations
        )
        self._startup_barrier = None
        result: list[threading.Thread] = []
        ordinal = 0
        for role, count in self.roles.items():
            for index in range(count):
                worker_id = f"{role}-{index}"
                worker = classes[role](
                    worker_id,
                    role,
                    payload,
                    self.coordinator,
                    self.stop_event,
                    seed=self.seed + ordinal * 1009,
                    check_timeout_ms=self.check_timeout_ms,
                    startup_barrier=None,
                )
                result.append(worker)
                ordinal += 1
        return result

    def solve(self, timeout: float | None = None) -> SolveResult:
        budget = self.timeout if timeout is None else timeout
        started = time.perf_counter()
        deadline = None if budget is None else started + max(0.0, float(budget))
        shutdown_reserve = 0.0
        search_deadline = deadline
        if deadline is not None:
            shutdown_reserve, _gate_reserve = _finalization_reserve(self.problem)
            # Shutdown is charged inside the requested budget.  The optimized
            # fresh-context soundness gate is the only bounded tail margin.
            search_deadline = max(started, deadline - shutdown_reserve)
        self.coordinator.set_hitting_set_limits(
            deadline=search_deadline,
            interrupted=self.stop_event.is_set,
        )
        self.workers = self._make_workers()
        pending = list(self.workers)
        # On very large inputs, let one model-oriented worker finish its first
        # context-local publication before the remaining contexts begin their
        # refcount-heavy translations.  This preserves an anytime incumbent
        # without serializing the subsequent portfolio search.
        if len(self.problem.soft) >= 10_000 and len(pending) > 1:
            producer = next(
                (worker for worker in pending if getattr(worker, "role", "") == "mss"),
                pending[0],
            )
            producer.start()
            pending.remove(producer)
            head_start_deadline = time.perf_counter() + 2.5
            if search_deadline is not None:
                head_start_deadline = min(head_start_deadline, search_deadline)
            while (
                self.coordinator.upper_bound is None
                and not self.coordinator.is_done()
                and time.perf_counter() < head_start_deadline
            ):
                time.sleep(0.005)
        for worker in pending:
            worker.start()
        timed_out = False
        try:
            while not self.coordinator.is_done():
                if search_deadline is not None and time.perf_counter() >= search_deadline:
                    timed_out = True
                    break
                time.sleep(0.005)
        except KeyboardInterrupt:
            timed_out = True
        finally:
            self.stop_event.set()
            if self._startup_barrier is not None:
                self._startup_barrier.abort()
            # A context interrupt is the documented exception to Z3's
            # cross-thread ownership rule and makes shutdown cooperative even
            # while a native Optimize/Solver check is active.
            for worker in self.workers:
                if hasattr(worker, "interrupt"):
                    worker.interrupt()  # type: ignore[attr-defined]
            join_deadline = (
                time.perf_counter() + 10.0
                if deadline is None
                else max(time.perf_counter(), deadline)
            )
            for worker in self.workers:
                remaining = max(0.0, join_deadline - time.perf_counter())
                worker.join(remaining)
            for worker in self.workers:
                if worker.is_alive() and hasattr(worker, "interrupt"):
                    worker.interrupt()  # type: ignore[attr-defined]
            # A tiny caller budget can expire before freshly started native
            # contexts observe the first interrupt.  Give every still-live
            # worker a second, shared bounded shutdown window instead of
            # returning while those contexts continue to publish updates.
            second_join_deadline = time.perf_counter() + 2.0
            for worker in self.workers:
                if worker.is_alive():
                    remaining = max(
                        0.0, second_join_deadline - time.perf_counter()
                    )
                    worker.join(remaining)

        snap = self.coordinator.snapshot()
        status = snap.status
        assignment = snap.incumbent_assignment
        falsified = snap.incumbent_falsified
        upper_bound = snap.upper_bound
        incumbent_valid = (
            upper_bound is None
            or (
                assignment is not None
                and falsified is not None
                and _incumbent_is_feasible(
                    self.problem, assignment, falsified, upper_bound
                )
            )
        )
        if not incumbent_valid:
            self.trace.emit(
                "coordinator",
                "coordinator",
                "invalid_final_incumbent",
                snap.lower_bound,
                snap.upper_bound,
                snap.status,
            )
            status = "UNKNOWN"
            assignment = None
            falsified = None
            upper_bound = None
        elif status == "RUNNING":
            status = "SAT" if upper_bound is not None else "UNKNOWN"
        certificate = self.coordinator.certificate() if status == "OPTIMAL" else None
        if certificate is not None and self.verify_optimal:
            verify_certificate_or_raise(self.problem, certificate)
        errors = {
            worker.worker_id: worker.error
            for worker in self.workers
            if getattr(worker, "error", None)
        }
        alive = tuple(worker.name for worker in self.workers if worker.is_alive())
        self.trace.emit(
            "coordinator",
            "coordinator",
            "finished",
            snap.lower_bound,
            upper_bound,
            status,
            timed_out=timed_out,
        )
        # Keep this immediately before result construction: elapsed is the
        # caller-observed solve work, including shutdown, gate, and verification.
        elapsed = time.perf_counter() - started
        return SolveResult(
            status,
            snap.lower_bound,
            upper_bound,
            assignment,
            falsified,
            certificate,
            elapsed,
            self.roles.as_dict(),
            errors,
            alive,
        )


def z3_optimize_baseline(problem: Problem | str | Path, *, timeout: float | None = None, engine: str | None = None) -> dict[str, Any]:
    """Run a fresh-context Z3 Optimize baseline for evaluation."""
    instance = parse_file(problem) if isinstance(problem, (str, Path)) else problem
    ctx = z3.Context()
    translated = instance.translate(ctx)
    opt = z3.Optimize(ctx=ctx)
    if timeout is not None:
        opt.set(timeout=max(1, int(timeout * 1000)))
    if engine:
        try:
            opt.set("maxsat_engine", engine)
        except z3.Z3Exception:
            pass
    opt.add(*translated.hard)
    for sft in translated.soft:
        opt.add_soft(sft.formula, weight=str(sft.weight))
    started = time.perf_counter()
    result = opt.check()
    elapsed = time.perf_counter() - started
    if result == z3.unsat:
        return {"status": "UNSAT", "cost": None, "elapsed": elapsed, "engine": engine or "default"}
    try:
        model = opt.model()
        if not all(
            z3.is_true(model.eval(hard, model_completion=True))
            for hard in translated.hard
        ):
            raise z3.Z3Exception("Optimize incumbent violates a hard constraint")
        falsified = frozenset(
            soft.index
            for soft in translated.soft
            if not z3.is_true(model.eval(soft.formula, model_completion=True))
        )
    except z3.Z3Exception:
        return {"status": "UNKNOWN", "cost": None, "elapsed": elapsed, "engine": engine or "default"}
    return {
        "status": "SAT" if result == z3.unknown else "OPTIMAL",
        "cost": objective_for_weights(instance.weights).cost(falsified),
        "elapsed": elapsed,
        "engine": engine or "default",
    }

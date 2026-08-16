"""Fully asynchronous, versioned coordinator.

Workers exchange immutable/plain Python messages. No Z3 AST, model, Solver, or
Optimize object is stored in this module or sent through its queue.
"""
from __future__ import annotations

from dataclasses import dataclass
import queue
import threading
import time
from typing import Any, Callable, Iterable, Mapping

from .objective import HittingSetInterrupted, Objective
from .trace import TraceWriter


@dataclass(frozen=True)
class CandidateModel:
    worker_id: str
    role: str
    assignment: dict[str, bool | str]
    falsified: frozenset[int]
    cost: int


@dataclass(frozen=True)
class CoreFound:
    worker_id: str
    role: str
    core: frozenset[int]
    original: bool = True


@dataclass(frozen=True)
class CorrectionSetFound:
    worker_id: str
    role: str
    correction_set: frozenset[int]
    original: bool = True


@dataclass(frozen=True)
class BoundUpdate:
    worker_id: str
    role: str
    lower_bound: int


@dataclass(frozen=True)
class BackboneUpdate:
    worker_id: str
    role: str
    literal: tuple[str, bool]
    validated: bool
    countermodel: dict[str, bool | str] | None = None


@dataclass(frozen=True)
class BackboneRefuted:
    worker_id: str
    role: str
    literal: tuple[str, bool]
    countermodel: dict[str, bool | str]


@dataclass(frozen=True)
class CoordinatorSnapshot:
    version: int
    lower_bound: int
    upper_bound: int | None
    status: str
    incumbent_assignment: dict[str, bool | str] | None
    incumbent_falsified: frozenset[int] | None
    cores: tuple[frozenset[int], ...]
    correction_sets: tuple[frozenset[int], ...]
    validated_backbones: frozenset[tuple[str, bool]]
    candidate_backbones: tuple[tuple[str, bool], ...]
    refuted_backbones: tuple[tuple[str, bool], ...]


class Coordinator:
    """Merge monotonic asynchronous updates with short critical sections."""

    def __init__(self, objective: Objective, soft_count: int, *, trace: TraceWriter | None = None):
        if soft_count != objective.size:
            raise ValueError("objective size must equal soft constraint count")
        self.objective = objective
        self.soft_count = int(soft_count)
        self.trace = trace or TraceWriter()
        self._lock = threading.Lock()
        self._condition = threading.Condition(self._lock)
        self._events: queue.SimpleQueue[Any] = queue.SimpleQueue()
        self._version = 0
        self._cores: set[frozenset[int]] = set()
        self._correction_sets: set[frozenset[int]] = set()
        self._lower_bound = 0
        self._upper_bound: int | None = None
        self._incumbent_assignment: dict[str, bool | str] | None = None
        self._incumbent_falsified: frozenset[int] | None = None
        self._status = "RUNNING"
        self._validated_backbones: set[tuple[str, bool]] = set()
        self._candidate_backbones: dict[tuple[str, bool], str] = {}
        self._refuted_backbones: dict[
            tuple[str, bool], dict[str, bool | str]
        ] = {}
        self._worker_states: dict[str, str] = {}
        self._core_generation = 0
        self._hitting_set_deadline: float | None = None
        self._hitting_set_interrupted: Callable[[], bool] | None = None

    @property
    def events(self) -> queue.SimpleQueue[Any]:
        return self._events

    @property
    def version(self) -> int:
        with self._lock:
            return self._version


    def set_hitting_set_limits(
        self,
        *,
        deadline: float | None,
        interrupted: Callable[[], bool] | None = None,
    ) -> None:
        """Set cooperative limits without coupling the objective to the solver."""
        with self._lock:
            self._hitting_set_deadline = deadline
            self._hitting_set_interrupted = interrupted
    def register_worker(self, worker_id: str, role: str) -> None:
        with self._condition:
            self._worker_states[str(worker_id)] = str(role)
            self._version += 1
            self._condition.notify_all()

    def worker_done(self, worker_id: str) -> None:
        with self._condition:
            self._worker_states[str(worker_id)] = "done"
            self._version += 1
            self._condition.notify_all()

    def publish_model(
        self,
        worker_id: str,
        role: str,
        assignment: Mapping[str, bool | str],
        falsified: Iterable[int],
        cost: int | None = None,
    ) -> bool:
        fs = frozenset(int(i) for i in falsified)
        if any(i < 0 or i >= self.soft_count for i in fs):
            raise ValueError("model contains an out-of-range falsified soft index")
        measured = self.objective.cost(fs)
        if cost is not None and int(cost) != measured:
            raise ValueError(f"model cost {cost} does not match falsified set cost {measured}")
        cost = measured
        # The model path is the coordinator's final boundary: every accepted
        # or redundant feasible model contributes heuristic correction data,
        # while lower-bound recomputation below still reads cores only.
        self.publish_correction_set(worker_id, role, fs, original=True)
        plain = {str(k): (bool(v) if isinstance(v, bool) else str(v)) for k, v in assignment.items()}
        accepted = False
        with self._condition:
            if self._status in {"UNSAT", "OPTIMAL"}:
                return False
            if self._upper_bound is None or cost < self._upper_bound:
                self._upper_bound = cost
                self._incumbent_assignment = plain
                self._incumbent_falsified = fs
                accepted = True
                self._version += 1
                self._events.put(CandidateModel(str(worker_id), str(role), plain, fs, cost))
                self.trace.emit(worker_id, role, "incumbent", self._lower_bound, cost, self._status)
                self._check_optimal_locked()
                self._condition.notify_all()
        return accepted

    def publish_core(
        self,
        worker_id: str,
        role: str,
        core: Iterable[int],
        *,
        original: bool = True,
    ) -> bool:
        # SOUNDNESS TRAP: MaxRes workers reason over fresh def-* variables and
        # offset-adjusted transformed softs. Such a core is not an original
        # problem core and must never enter the global proof store.
        if not original:
            raise ValueError("transformed MaxRes cores cannot enter the global core store")
        c = frozenset(int(i) for i in core)
        if any(i < 0 or i >= self.soft_count for i in c):
            raise ValueError("core index out of range; only original soft IDs are accepted")
        if not c:
            self.publish_unsat(worker_id, role)
            return True
        # Exact branch-and-bound is deliberately outside the coordinator lock.
        # A concurrent core publication invalidates the snapshot and triggers a
        # retry; an interrupted retry records the valid core but conservatively
        # retains the previous certified lower bound.
        while True:
            with self._condition:
                if c in self._cores:
                    return False
                candidate_cores = tuple(self._cores | {c})
                generation = self._core_generation
                deadline = self._hitting_set_deadline
                interrupted = self._hitting_set_interrupted
            try:
                computed, _ = self.objective.minimum_hitting_set(
                    candidate_cores,
                    deadline=deadline,
                    interrupted=interrupted,
                )
            except HittingSetInterrupted:
                with self._condition:
                    if c in self._cores:
                        return False
                    self._record_core_locked(worker_id, role, c, None)
                    return True
            with self._condition:
                if c in self._cores:
                    return False
                if self._core_generation != generation:
                    continue
                self._record_core_locked(worker_id, role, c, computed)
                return True

    def _record_core_locked(
        self,
        worker_id: str,
        role: str,
        core: frozenset[int],
        computed: int | None,
    ) -> None:
        """Store a core while holding ``_condition``; never perform search here."""
        candidate_lower = self._lower_bound if computed is None else max(
            self._lower_bound, computed
        )
        if self._upper_bound is not None and candidate_lower > self._upper_bound:
            raise ValueError(
                "inconsistent original core lower bound exceeds incumbent upper bound"
            )
        self._cores.add(core)
        self._core_generation += 1
        self._lower_bound = candidate_lower
        self._version += 1
        self._events.put(CoreFound(str(worker_id), str(role), core, True))
        self.trace.emit(
            worker_id,
            role,
            "core",
            self._lower_bound,
            self._upper_bound,
            self._status,
            size=len(core),
        )
        self._check_optimal_locked()
        self._condition.notify_all()

    def publish_correction_set(
        self,
        worker_id: str,
        role: str,
        correction_set: Iterable[int],
        *,
        original: bool = True,
    ) -> bool:
        """Publish a feasible model's falsified original soft IDs.

        Correction sets guide private MaxRes/dual-MaxRes transformations only;
        unlike cores, they never participate in the certified lower bound.
        """
        if not original:
            raise ValueError("transformed correction sets cannot enter the correction-set store")
        c = frozenset(int(i) for i in correction_set)
        if any(i < 0 or i >= self.soft_count for i in c):
            raise ValueError("correction-set index out of range; only original soft IDs are accepted")
        with self._condition:
            if c in self._correction_sets:
                return False
            self._correction_sets.add(c)
            self._version += 1
            self._events.put(CorrectionSetFound(str(worker_id), str(role), c, True))
            self.trace.emit(
                worker_id,
                role,
                "correction_set",
                self._lower_bound,
                self._upper_bound,
                self._status,
                size=len(c),
            )
            self._condition.notify_all()
            return True

    def add_correction_set(self, correction_set: Iterable[int], *, original: bool = True) -> bool:
        """Convenience API for tests/tools submitting an asynchronous correction set."""
        return self.publish_correction_set("external", "external", correction_set, original=original)

    def publish_bound(self, worker_id: str, role: str, lower_bound: int) -> bool:
        bound = int(lower_bound)
        if bound < 0:
            raise ValueError("lower bound must be non-negative")
        with self._condition:
            if bound <= self._lower_bound:
                return False
            if self._upper_bound is not None and bound > self._upper_bound:
                raise ValueError(
                    "inconsistent lower bound exceeds incumbent upper bound"
                )
            self._lower_bound = bound
            self._version += 1
            self._events.put(BoundUpdate(str(worker_id), str(role), bound))
            self.trace.emit(worker_id, role, "bound", self._lower_bound, self._upper_bound, self._status)
            self._check_optimal_locked()
            self._condition.notify_all()
            return True

    def publish_unsat(self, worker_id: str, role: str) -> None:
        with self._condition:
            if self._status == "OPTIMAL":
                return
            if self._upper_bound is not None:
                raise ValueError("cannot publish UNSAT after a feasible incumbent")
            self._status = "UNSAT"
            self._version += 1
            self.trace.emit(worker_id, role, "unsat", self._lower_bound, self._upper_bound, self._status)
            self._condition.notify_all()

    def publish_backbone_candidate(
        self, worker_id: str, role: str, literal: tuple[str, bool]
    ) -> None:
        """Record a literal that agrees across every feasible sample so far."""
        lit = (str(literal[0]), bool(literal[1]))
        with self._condition:
            if lit in self._validated_backbones or lit in self._refuted_backbones:
                return
            if lit in self._candidate_backbones:
                return
            self._candidate_backbones[lit] = "sampled-consensus"
            self._version += 1
            self._events.put(
                BackboneUpdate(str(worker_id), str(role), lit, False, None)
            )
            self.trace.emit(
                worker_id,
                role,
                "backbone_candidate",
                self._lower_bound,
                self._upper_bound,
                self._status,
                literal=lit,
                countermodel=False,
            )
            self._condition.notify_all()

    def publish_backbone_refuted(
        self,
        worker_id: str,
        role: str,
        literal: tuple[str, bool],
        countermodel: Mapping[str, bool | str],
    ) -> None:
        """Record a sampled candidate's hard-feasible counterexample."""
        lit = (str(literal[0]), bool(literal[1]))
        plain = {
            str(name): (bool(value) if isinstance(value, bool) else str(value))
            for name, value in countermodel.items()
        }
        with self._condition:
            if lit in self._refuted_backbones:
                return
            self._candidate_backbones.pop(lit, None)
            self._refuted_backbones[lit] = plain
            self._version += 1
            self._events.put(
                BackboneRefuted(str(worker_id), str(role), lit, plain)
            )
            self.trace.emit(
                worker_id,
                role,
                "backbone_refuted",
                self._lower_bound,
                self._upper_bound,
                self._status,
                literal=lit,
                countermodel=True,
            )
            self._condition.notify_all()

    def publish_backbone(
        self,
        worker_id: str,
        role: str,
        literal: tuple[str, bool],
        *,
        validated: bool,
        countermodel: Mapping[str, bool | str] | None = None,
    ) -> None:
        """Publish validation, retaining compatibility with the old API."""
        if not validated:
            if countermodel is None:
                self.publish_backbone_candidate(worker_id, role, literal)
            else:
                self.publish_backbone_refuted(
                    worker_id, role, literal, countermodel
                )
            return
        lit = (str(literal[0]), bool(literal[1]))
        with self._condition:
            self._candidate_backbones.pop(lit, None)
            self._validated_backbones.add(lit)
            self._version += 1
            self._events.put(
                BackboneUpdate(str(worker_id), str(role), lit, True, None)
            )
            self.trace.emit(
                worker_id,
                role,
                "backbone_validated",
                self._lower_bound,
                self._upper_bound,
                self._status,
                literal=lit,
                countermodel=False,
            )
            self._condition.notify_all()

    def _check_optimal_locked(self) -> None:
        if self._status == "RUNNING" and self._upper_bound is not None and self._lower_bound == self._upper_bound:
            self._status = "OPTIMAL"

    def _snapshot_locked(self) -> CoordinatorSnapshot:
        return CoordinatorSnapshot(
            self._version,
            self._lower_bound,
            self._upper_bound,
            self._status,
            dict(self._incumbent_assignment) if self._incumbent_assignment is not None else None,
            self._incumbent_falsified,
            tuple(sorted(self._cores, key=lambda c: (len(c), tuple(sorted(c))))),
            tuple(sorted(self._correction_sets, key=lambda c: (len(c), tuple(sorted(c))))),
            frozenset(self._validated_backbones),
            tuple(sorted(self._candidate_backbones)),
            tuple(sorted(self._refuted_backbones)),
        )

    def snapshot(self) -> CoordinatorSnapshot:
        with self._lock:
            return self._snapshot_locked()

    def wait_for_update(self, version: int, timeout: float | None = None) -> CoordinatorSnapshot:
        with self._condition:
            if self._version <= version:
                self._condition.wait(timeout)
            return self._snapshot_locked()

    @property
    def lower_bound(self) -> int:
        return self.snapshot().lower_bound

    @property
    def upper_bound(self) -> int | None:
        return self.snapshot().upper_bound

    @property
    def cores(self) -> tuple[frozenset[int], ...]:
        return self.snapshot().cores

    @property
    def correction_sets(self) -> tuple[frozenset[int], ...]:
        return self.snapshot().correction_sets

    def add_core(self, core: Iterable[int], *, original: bool = True) -> bool:
        """Convenience API for tests/tools submitting an asynchronous core."""
        return self.publish_core("external", "external", core, original=original)

    def is_done(self) -> bool:
        with self._lock:
            return self._status in {"OPTIMAL", "UNSAT"}

    def certificate(self) -> dict[str, Any] | None:
        with self._lock:
            if self._upper_bound is None or self._status != "OPTIMAL":
                return None
            # The incumbent's falsified set is already an upper-bound witness.
            # Once the certified lower bound meets that cost it is also a
            # minimum hitting set, so certificate creation need not repeat the
            # exponential search (or hold the coordinator lock while doing so).
            hitting_set = frozenset(self._incumbent_falsified or ())
            if self.objective.cost(hitting_set) != self._lower_bound or any(
                not (hitting_set & core) for core in self._cores
            ):
                raise ValueError(
                    "optimal incumbent is not a lower-bound hitting-set witness"
                )
            return {
                "status": "OPTIMAL",
                "lower_bound": self._lower_bound,
                "upper_bound": self._upper_bound,
                "cost": self._upper_bound,
                "assignment": dict(self._incumbent_assignment or {}),
                "falsified": sorted(hitting_set),
                "cores": [sorted(c) for c in sorted(self._cores, key=lambda c: (len(c), tuple(sorted(c))))],
                "hitting_set": sorted(hitting_set),
                "created_at": time.time(),
            }

    def worker_state(self) -> dict[str, str]:
        with self._lock:
            return dict(self._worker_states)

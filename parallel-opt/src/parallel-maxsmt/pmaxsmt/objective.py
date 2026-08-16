"""Objective abstractions for MaxSMT.

The solver only relies on :class:`Objective`'s plain-Python operations.  This
keeps objective handling extensible: a new penalty scheme can implement this
interface without changing any worker implementation.
"""
from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
import time
from typing import Callable, Iterable, Mapping, Sequence



class HittingSetInterrupted(InterruptedError):
    """Raised when an exact hitting-set search reaches its cooperative limit."""


class Objective(ABC):
    """Immutable penalty objective over integer soft-constraint IDs.

    ``weights`` is deliberately a plain tuple, so it is safe to send the
    objective metadata to a worker thread.  Formula ASTs never belong here.
    """

    weights: tuple[int, ...]

    def __init__(self, weights: Sequence[int]):
        ws = tuple(int(w) for w in weights)
        if any(w <= 0 for w in ws):
            raise ValueError("soft-constraint weights must be positive integers")
        self.weights = ws

    @property
    def size(self) -> int:
        return len(self.weights)

    @abstractmethod
    def cost(self, falsified: Iterable[int]) -> int:
        """Return the penalty for a set of falsified soft IDs."""

    def cost_from_truth(self, truth: Mapping[int, bool]) -> int:
        return self.cost(i for i in range(self.size) if not truth.get(i, False))

    @abstractmethod
    def minimum_hitting_set(
        self,
        cores: Iterable[Iterable[int]],
        *,
        deadline: float | None = None,
        interrupted: Callable[[], bool] | None = None,
    ) -> tuple[int, frozenset[int]]:
        """Return an exact minimum objective cost hitting every core.

        ``deadline`` and ``interrupted`` are cooperative limits.  An aborted
        search raises :class:`HittingSetInterrupted`; callers must retain their
        previous certified lower bound rather than treating a partial search
        result as proof.
        """

    def zero_cost(self) -> int:
        return 0


@dataclass(frozen=True)
class UnweightedObjective(Objective):
    """Unit penalty for every falsified soft constraint."""

    weights: tuple[int, ...]

    def __init__(self, size_or_weights: int | Sequence[int]):
        if isinstance(size_or_weights, int):
            if size_or_weights < 0:
                raise ValueError("objective size must be non-negative")
            ws = (1,) * size_or_weights
        else:
            ws = tuple(int(w) for w in size_or_weights)
            if any(w != 1 for w in ws):
                raise ValueError("unweighted objective requires unit weights")
        object.__setattr__(self, "weights", ws)

    def cost(self, falsified: Iterable[int]) -> int:
        fs = set(int(i) for i in falsified)
        if any(i < 0 or i >= len(self.weights) for i in fs):
            raise ValueError("falsified soft index out of range")
        return len(fs)

    def minimum_hitting_set(
        self,
        cores: Iterable[Iterable[int]],
        *,
        deadline: float | None = None,
        interrupted: Callable[[], bool] | None = None,
    ) -> tuple[int, frozenset[int]]:
        return _minimum_hitting_set(
            self.weights, cores, deadline=deadline, interrupted=interrupted
        )


@dataclass(frozen=True)
class WeightedObjective(Objective):
    """Positive-integer weighted penalty objective."""

    weights: tuple[int, ...]

    def __init__(self, weights: Sequence[int] | Mapping[int, int]):
        if isinstance(weights, Mapping):
            if not weights:
                ws = ()
            else:
                n = max(int(i) for i in weights) + 1
                ws = tuple(int(weights[i]) for i in range(n))
        else:
            ws = tuple(int(w) for w in weights)
        if any(w <= 0 for w in ws):
            raise ValueError("soft-constraint weights must be positive integers")
        object.__setattr__(self, "weights", ws)

    def cost(self, falsified: Iterable[int]) -> int:
        fs = set(int(i) for i in falsified)
        if any(i < 0 or i >= len(self.weights) for i in fs):
            raise ValueError("falsified soft index out of range")
        return sum(self.weights[i] for i in fs)

    def minimum_hitting_set(
        self,
        cores: Iterable[Iterable[int]],
        *,
        deadline: float | None = None,
        interrupted: Callable[[], bool] | None = None,
    ) -> tuple[int, frozenset[int]]:
        return _minimum_hitting_set(
            self.weights, cores, deadline=deadline, interrupted=interrupted
        )


def objective_for_weights(weights: Sequence[int]) -> Objective:
    """Choose the unit or weighted implementation from a weight vector."""
    ws = tuple(int(w) for w in weights)
    return UnweightedObjective(len(ws)) if all(w == 1 for w in ws) else WeightedObjective(ws)


def _minimum_hitting_set(
    weights: Sequence[int],
    cores: Iterable[Iterable[int]],
    *,
    deadline: float | None = None,
    interrupted: Callable[[], bool] | None = None,
) -> tuple[int, frozenset[int]]:
    """Exact minimum-weight hitting set by branch-and-bound.

    Cores are normalized and validated here because this function is also used
    by certificate verification.  Empty cores represent an infeasible hard
    problem and have no finite hitting set; callers handle that as ``None`` at
    the problem level, while this low-level API reports ``(0, empty)`` so the
    bound remains conservative.
    """
    def check_interrupted() -> None:
        if (deadline is not None and time.perf_counter() >= deadline) or (
            interrupted is not None and interrupted()
        ):
            raise HittingSetInterrupted("minimum hitting-set search interrupted")

    n = len(weights)
    normalized: list[frozenset[int]] = []
    for core in cores:
        check_interrupted()
        c = frozenset(int(i) for i in core)
        if any(i < 0 or i >= n for i in c):
            raise ValueError("core index out of range")
        if not c:
            return 0, frozenset()
        if c not in normalized:
            normalized.append(c)
    if not normalized:
        return 0, frozenset()
    # Remove cores that are supersets of another core: hitting the smaller one
    # implies hitting the larger one, and the operation preserves the optimum.
    minimal: list[frozenset[int]] = []
    for c in sorted(normalized, key=lambda x: (len(x), tuple(sorted(x)))):
        check_interrupted()
        if not any(d <= c for d in minimal):
            minimal.append(c)

    best_cost = sum(weights)
    best_set: frozenset[int] = frozenset(range(n))

    def lower_bound(uncovered: list[frozenset[int]]) -> int:
        # Disjoint-core bound is cheap and admissible for branch-and-bound.
        chosen: set[int] = set()
        total = 0
        for core in sorted(uncovered, key=len):
            check_interrupted()
            if chosen.isdisjoint(core):
                total += min(weights[i] for i in core)
                chosen.update(core)
        return total

    def search(selected: frozenset[int], selected_cost: int, uncovered: list[frozenset[int]]) -> None:
        nonlocal best_cost, best_set
        check_interrupted()
        if not uncovered:
            if selected_cost < best_cost or (selected_cost == best_cost and tuple(sorted(selected)) < tuple(sorted(best_set))):
                best_cost, best_set = selected_cost, selected
            return
        if selected_cost + lower_bound(uncovered) > best_cost:
            return
        core = min(uncovered, key=lambda c: (len(c), tuple(sorted(c))))
        choices = sorted(core, key=lambda i: (weights[i], i))
        for i in choices:
            check_interrupted()
            if i in selected:
                continue
            new_cost = selected_cost + weights[i]
            if new_cost > best_cost:
                continue
            new_uncovered = [c for c in uncovered if i not in c]
            search(selected | {i}, new_cost, new_uncovered)

    search(frozenset(), 0, minimal)
    return best_cost, best_set

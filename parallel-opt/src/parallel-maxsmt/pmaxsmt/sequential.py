"""Internal one-worker baseline sharing the parallel code paths."""
from __future__ import annotations

from pathlib import Path

from .problem import Problem
from .roles import RoleSpec
from .solver import ParallelMaxSMTSolver, SolveResult
from .trace import TraceWriter


class SequentialMaxSMTSolver(ParallelMaxSMTSolver):
    """Run exactly one original-core/IHS worker with the same coordinator."""

    def __init__(
        self,
        problem: Problem | str | Path,
        *,
        seed: int = 0,
        timeout: float | None = None,
        trace: TraceWriter | None = None,
        check_timeout_ms: int = 250,
        verify_optimal: bool = True,
    ) -> None:
        super().__init__(
            problem,
            roles=RoleSpec(hs=1, mss=0, backbone=0, maxres=0, zopt=0),
            threads=1,
            seed=seed,
            timeout=timeout,
            trace=trace,
            check_timeout_ms=check_timeout_ms,
            verify_optimal=verify_optimal,
        )

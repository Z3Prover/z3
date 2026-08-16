"""Implicit hitting-set / original-core worker."""
from __future__ import annotations

import time
import z3

from .base import WorkerBase
from ..objective import HittingSetInterrupted


class HSWorker(WorkerBase):
    """IHS worker adapted from ``examples/python/hs.py``.

    Its cores always refer to original soft IDs.  The worker's private
    Optimize is used for minimum-cost hitting sets; the coordinator
    independently recomputes the same exact lower bound from the core store.
    """

    def _pick_hitting_set(self, cores: tuple[frozenset[int], ...]) -> tuple[int, frozenset[int]]:
        assert self.ctx is not None
        if not cores:
            return 0, frozenset()
        opt = z3.Optimize(ctx=self.ctx)
        opt.set(timeout=self.check_timeout_ms)
        choices: dict[int, z3.BoolRef] = {}
        for index in range(self.objective.size):
            if self.interrupted():
                return 0, frozenset()
            choices[index] = z3.Bool(
                f"{self.role}_{self.worker_id}_hit_{index}", ctx=self.ctx
            )
        for core in cores:
            if self.interrupted():
                return 0, frozenset()
            opt.add(z3.Or([choices[index] for index in core]))
        terms: list[z3.ArithRef] = []
        for index in range(self.objective.size):
            if self.interrupted():
                return 0, frozenset()
            terms.append(z3.If(choices[index], self.objective.weights[index], 0))
        opt.minimize(z3.Sum(terms))

        result = opt.check()
        if result == z3.sat:
            model = opt.model()
            selected: set[int] = set()
            for index, choice in choices.items():
                if self.interrupted():
                    return 0, frozenset()
                if z3.is_true(model.eval(choice, model_completion=True)):
                    selected.add(index)
            hs = frozenset(selected)
            return self.objective.cost(hs), hs

        # A timeout here is not a proof.  The pure-Python fallback remains a
        # heuristic picker and must stop cooperatively with the worker.
        try:
            return self.objective.minimum_hitting_set(
                cores, interrupted=self.interrupted
            )
        except HittingSetInterrupted:
            return 0, frozenset()

    def _query(self, disabled: frozenset[int]) -> bool:
        assert self.translated is not None and self.ctx is not None
        enabled: list[int] = []
        for soft in self.translated.soft:
            if self.interrupted():
                return False
            if soft.index not in disabled:
                enabled.append(soft.index)

        solver, selectors = self._assumption_problem(enabled)
        result = solver.check(list(selectors.values()))
        if result == z3.sat:
            self._publish_model(solver.model())
            return True
        if result == z3.unsat:
            core = self._extract_original_core(solver, selectors)
            if not core:
                self.coordinator.publish_unsat(self.worker_id, self.role)
                return False
            core = self._reduce_core(core)
            self.coordinator.publish_core(self.worker_id, self.role, core, original=True)
            return False
        return False

    def _reduce_core(self, core: frozenset[int]) -> frozenset[int]:
        """Deletion-based reduction, retaining only original selector IDs."""
        if len(core) <= 1:
            return core
        current = list(core)
        changed = True
        while changed and not self.interrupted() and len(current) > 1:
            changed = False
            for idx in list(current):
                if self.interrupted():
                    break
                trial = [i for i in current if i != idx]
                solver, selectors = self._assumption_problem(trial)
                result = solver.check(list(selectors.values()))
                if result == z3.unsat:
                    reduced = self._extract_original_core(solver, selectors)
                    if reduced and len(reduced) < len(current):
                        current = list(reduced)
                        changed = True
                        break
        return frozenset(current)

    def run_worker(self) -> None:
        last_version = -1
        while not self.interrupted():
            snap = self.snapshot()
            if snap.version == last_version:
                self.wait(last_version, 0.03)
                continue
            last_version = snap.version
            lower, hs = self._pick_hitting_set(snap.cores)
            self.coordinator.publish_bound(self.worker_id, self.role, lower)
            if self.interrupted():
                break
            self._query(hs)
            # ``publish_model`` or ``publish_core`` changes the version; if
            # neither did (e.g. unknown), yielding prevents a busy loop.
            if self.coordinator.version == last_version:
                time.sleep(0.01)

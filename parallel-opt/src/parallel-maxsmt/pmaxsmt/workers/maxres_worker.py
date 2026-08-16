"""Private weighted MaxRes / dual-MaxRes exploration worker.

The transformed representation is deliberately private.  Original cores are
sound proof objects and may be shared with the coordinator; correction sets
and transformed ``def-*`` artifacts are only search guidance.
"""
from __future__ import annotations

import time

import z3

from .base import WorkerBase


class MaxResWorker(WorkerBase):
    """Search a private MaxRes/dual-MaxRes representation.

    The coordinator supplies immutable original-index cores and correction sets.
    This worker applies the hs.py small-set heuristic to its private soft list,
    then optimizes that transformed list in its own Z3 context.  A transformed
    model is always re-measured against the original soft formulas before it is
    published, so no transformed cost or core can enter certification.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.private_offset = 0
        self.private_best_cost: int | None = None
        self.last_action: str | None = None
        self._seen_cores: set[frozenset[int]] = set()
        self._seen_correction_sets: set[frozenset[int]] = set()
        self._private_soft: list[tuple[z3.BoolRef, int, frozenset[int]]] = []
        self._counter = 0
        # hs.py's adaptive maxres selection parameters.
        self.small_set_size = 6
        self.small_set_threshold = 1
        self.num_max_res_failures = 0
        self.corr_set_enabled = True

    def _release_context_objects(self) -> None:
        super()._release_context_objects()
        self._private_soft.clear()

    def _fresh(self, prefix: str) -> z3.BoolRef:
        assert self.ctx is not None
        self._counter += 1
        return z3.Bool(f"{self.role}_{self.worker_id}_{prefix}_{self._counter}", ctx=self.ctx)

    def _ensure_private_soft(self) -> None:
        if self._private_soft or self.translated is None:
            return
        for soft in self.translated.soft:
            if self.stop_event.is_set():
                raise InterruptedError("private soft construction interrupted")
            self._private_soft.append(
                (soft.formula, soft.weight, frozenset({soft.index}))
            )

    def relax_core(self, core: frozenset[int]) -> None:
        """Apply a weighted MaxRes-style relaxation to private softs."""
        if not core or self.translated is None:
            return
        self._ensure_private_soft()
        by_id = {s.index: s for s in self.translated.soft}
        if any(i not in by_id for i in core):
            return
        w_min = min(by_id[i].weight for i in core)
        self.private_offset += w_min
        updated: list[tuple[z3.BoolRef, int, frozenset[int]]] = []
        for formula, weight, origin in self._private_soft:
            if self.stop_event.is_set():
                raise InterruptedError("MaxRes relaxation interrupted")
            if origin.isdisjoint(core):
                updated.append((formula, weight, origin))
                continue
            residual = max(0, weight - w_min)
            if residual:
                updated.append((formula, residual, origin))
            # The fresh relaxation literal is private.  It lets the transformed
            # residual carry the charged w_min without exporting a fake core.
            relax = self._fresh("def")
            updated.append((z3.Or(formula, relax), w_min, origin))
        self._private_soft = updated

    def restrict_cs(self, correction_set: frozenset[int]) -> None:
        """Apply a private dual-MaxRes correction-set restriction."""
        if not correction_set or self.translated is None:
            return
        self._ensure_private_soft()
        if any(i < 0 or i >= self.objective.size for i in correction_set):
            return
        prefix = z3.BoolVal(False, ctx=self.ctx)
        rewritten: list[tuple[z3.BoolRef, int, frozenset[int]]] = []
        for formula, weight, origin in self._private_soft:
            if self.stop_event.is_set():
                raise InterruptedError("correction-set restriction interrupted")
            if origin.isdisjoint(correction_set):
                rewritten.append((formula, weight, origin))
                continue
            prefix = z3.Or(prefix, formula)
            rewritten.append((z3.And(prefix, formula), weight, origin))
        self._private_soft = rewritten

    @staticmethod
    def has_many_small_sets(sets: tuple[frozenset[int], ...] | list[frozenset[int]], small_set_size: int = 6, threshold: int = 1) -> bool:
        """Port hs.py's ``has_many_small_sets`` heuristic."""
        return threshold <= sum(1 for item in sets if 0 < len(item) <= small_set_size)

    @staticmethod
    def get_small_disjoint_sets(sets: tuple[frozenset[int], ...] | list[frozenset[int]], small_set_size: int = 6) -> list[frozenset[int]]:
        """Select small pairwise-disjoint sets, as in hs.py."""
        nonempty = [frozenset(s) for s in sets if s]
        if not nonempty:
            return []
        by_size = sorted(nonempty, key=lambda s: (len(s), tuple(sorted(s))))
        min_size = min(len(s) for s in by_size)
        selected_ids: set[int] = set()
        result: list[frozenset[int]] = []
        for size in range(min_size, min_size + 3):
            for item in by_size:
                if len(item) == size and item.isdisjoint(selected_ids):
                    result.append(item)
                    selected_ids.update(item)
        return result

    def _available(self, sets: tuple[frozenset[int], ...], seen: set[frozenset[int]]) -> tuple[frozenset[int], ...]:
        return tuple(item for item in sets if item not in seen)

    def maxres(self, snap) -> bool:
        """Apply one adaptive core-relaxation or correction-set restriction."""
        available_cores = self._available(snap.cores, self._seen_cores)
        available_cs = self._available(snap.correction_sets, self._seen_correction_sets)

        if self.has_many_small_sets(available_cores, self.small_set_size, self.small_set_threshold) or (
            not self.corr_set_enabled
            and not self.has_many_small_sets(available_cs, self.small_set_size, self.small_set_threshold)
            and self.num_max_res_failures > 0
        ):
            choices = self.get_small_disjoint_sets(available_cores, self.small_set_size)
            if choices:
                self.num_max_res_failures = 0
                for core in choices:
                    if self.stop_event.is_set():
                        raise InterruptedError("MaxRes core processing interrupted")
                    self._seen_cores.add(core)
                    self.small_set_size = max(4, min(self.small_set_size, len(core) - 2))
                    self.relax_core(core)
                self.corr_set_enabled = True
                self.last_action = "relax_core"
                return True

        if self.corr_set_enabled and self.has_many_small_sets(
            available_cs, self.small_set_size, self.small_set_threshold
        ):
            choices = self.get_small_disjoint_sets(available_cs, self.small_set_size)
            if choices:
                self.num_max_res_failures = 0
                for correction_set in choices:
                    if self.stop_event.is_set():
                        raise InterruptedError("MaxRes correction-set processing interrupted")
                    self._seen_correction_sets.add(correction_set)
                    self.restrict_cs(correction_set)
                self.corr_set_enabled = False
                self.last_action = "restrict_cs"
                return True

        self.num_max_res_failures += 1
        if self.num_max_res_failures > 3:
            self.num_max_res_failures = 0
            self.small_set_size += 100
        return False

    def _transformed_cost(self, model: z3.ModelRef) -> int:
        cost = self.private_offset
        for formula, weight, _ in self._private_soft:
            if self.stop_event.is_set():
                raise InterruptedError("transformed model measurement interrupted")
            if not z3.is_true(model.eval(formula, model_completion=True)):
                cost += weight
        return cost

    def _solve_transformed_once(self) -> None:
        """Optimize private softs, never the original objective directly."""
        assert self.translated is not None
        self._ensure_private_soft()
        opt = self._optimize()
        opt.add(*self.translated.hard)
        for formula, weight, _ in self._private_soft:
            if self.stop_event.is_set():
                raise InterruptedError("private optimization construction interrupted")
            opt.add_soft(formula, weight=str(weight))
        result = opt.check()
        if result == z3.sat:
            model = opt.model()
            self.private_best_cost = self._transformed_cost(model)
            # _publish_model evaluates translated.soft, not private softs, so
            # the coordinator receives a real original correction set/cost.
            self._publish_model(model)
        elif result == z3.unsat:
            # This can only certify infeasible hard constraints.  A transformed
            # soft failure is never converted into an original core.
            self.coordinator.publish_unsat(self.worker_id, self.role)

    def run_worker(self) -> None:
        while not self.interrupted():
            snap = self.snapshot()
            self.maxres(snap)
            self._solve_transformed_once()
            if self.stop_event.wait(0.06):
                break
            # If no new event arrived, the private search still gets another
            # randomized/native Z3 attempt; the stop event bounds the loop.
            time.sleep(0.001)

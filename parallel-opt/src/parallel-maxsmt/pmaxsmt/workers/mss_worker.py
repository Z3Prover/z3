"""Incumbent-seeded weighted local MSS/MCS and model-rotation worker."""
from __future__ import annotations

import time

import z3

from .base import WorkerBase


class MSSWorker(WorkerBase):
    """Explore local MSS neighborhoods using the hs.py rotation scheme.

    Every selector probe is built in this worker's private context.  The probe
    history is intentionally exposed as plain Python data so tests and callers
    can verify that separately seeded workers explore different neighborhoods.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.probe_history: list[tuple[tuple[int, ...], tuple[int, ...], str]] = []
        self.rotation_count = 0
        self._rotation_depth = 0

    def _ordered(self, ids: set[int] | list[int]) -> list[int]:
        """Prefer low-weight moves while retaining seed-dependent diversity."""
        values = list(ids)
        self.rng.shuffle(values)
        values.sort(key=lambda i: (self.objective.weights[i], self.rng.random()))
        return values

    def _pick_release(self, fixed: list[int]) -> set[int]:
        if not fixed:
            return set()
        ordered = self._ordered(fixed)
        count = 1 if len(ordered) < 4 else self.rng.randint(1, min(4, len(ordered)))
        return set(ordered[:count])

    def _assignment_problem(
        self, trues: set[int] | list[int], falses: set[int] | list[int]
    ) -> tuple[z3.Solver, dict[str, int]]:
        """Build hard constraints and assumption selectors for both polarities."""
        assert self.translated is not None and self.ctx is not None
        solver = z3.Solver(ctx=self.ctx)
        solver.set(timeout=self.check_timeout_ms)
        solver.add(*self.translated.hard)
        by_id = self.translated.soft

        selectors: dict[str, int] = {}
        for index in sorted(set(trues)):
            if self.interrupted():
                raise InterruptedError("MSS assumption construction interrupted")
            if index < 0 or index >= len(by_id):
                continue
            selector = z3.Bool(f"{self.role}_{self.worker_id}_mss_true_{index}", ctx=self.ctx)
            solver.add(z3.Implies(selector, by_id[index].formula))
            selectors[str(selector)] = index

        for index in sorted(set(falses)):
            if self.interrupted():
                raise InterruptedError("MSS assumption construction interrupted")
            if index < 0 or index >= len(by_id):
                continue
            selector = z3.Bool(f"{self.role}_{self.worker_id}_mss_false_{index}", ctx=self.ctx)
            solver.add(z3.Implies(selector, z3.Not(by_id[index].formula)))
            selectors[str(selector)] = index

        return solver, selectors

    def _probe_values(
        self, trues: set[int] | list[int], falses: set[int] | list[int]
    ) -> tuple[z3.CheckSatResult, z3.ModelRef | None, frozenset[int]]:
        solver, selectors = self._assignment_problem(trues, falses)
        assumptions: list[z3.BoolRef] = []
        for name in sorted(selectors):
            if self.interrupted():
                raise InterruptedError("MSS probe interrupted")
            assumptions.append(z3.Bool(name, ctx=self.ctx))

        result = solver.check(assumptions)
        truth_tuple = tuple(sorted(set(trues)))
        false_tuple = tuple(sorted(set(falses)))
        self.probe_history.append((truth_tuple, false_tuple, str(result)))
        if result == z3.sat:
            return result, solver.model(), frozenset()
        if result == z3.unsat:
            reverse = {name: index for name, index in selectors.items()}
            core = frozenset(reverse[str(item)] for item in solver.unsat_core() if str(item) in reverse)
            return result, None, core
        return result, None, frozenset()

    def _probe(self, fixed: list[int]) -> z3.ModelRef | None:
        """Compatibility wrapper for a true-assumption neighborhood probe."""
        result, model, core = self._probe_values(fixed, [])
        if result == z3.sat:
            assert model is not None
            self._publish_model(model)
            return model
        if result == z3.unsat:
            if core:
                self.coordinator.publish_core(self.worker_id, self.role, core, original=True)
            else:
                self.coordinator.publish_unsat(self.worker_id, self.role)
        return None

    def reduce_core(
        self,
        core: frozenset[int],
        assignment: dict[int, bool] | None = None,
    ) -> frozenset[int]:
        """Deletion-minimize an original-index probe core with a time bound."""
        assignment = assignment or {index: True for index in core}
        positive = frozenset(
            index for index in core if assignment.get(index, True)
        )
        if not positive:
            return frozenset()
        if positive != core:
            result, _, candidate = self._probe_values(set(positive), set())
            if result != z3.unsat or not candidate:
                return frozenset()
            positive = candidate
        if len(positive) <= 1:
            return positive
        current = set(positive)
        assignment = {index: True for index in current}
        deadline = time.perf_counter() + max(0.02, 4 * self.check_timeout_ms / 1000.0)
        changed = True
        while changed and len(current) > 1 and not self.interrupted() and time.perf_counter() < deadline:
            changed = False
            for index in sorted(current):
                if self.interrupted():
                    break

                if time.perf_counter() >= deadline:
                    break
                trial = current - {index}
                trues = {i for i in trial if assignment.get(i, True)}
                falses = {i for i in trial if not assignment.get(i, True)}
                result, _, candidate = self._probe_values(trues, falses)
                if result == z3.unsat and candidate and len(candidate) <= len(trial):
                    current = set(candidate)
                    assignment = {i: assignment.get(i, True) for i in candidate}
                    changed = True
                    break
        return frozenset(current)

    def _expanded_core(
        self,
        core: frozenset[int],
        backbone2core: dict[int, frozenset[int]],
        assignment: dict[int, bool] | None = None,
    ) -> frozenset[int]:
        """Map only negative assumptions through proved positive supports."""
        expanded: set[int] = set()
        for index in core:
            is_negative = assignment is not None and not assignment.get(index, True)
            if is_negative:
                # A negative soft assumption is not itself an original MaxSMT
                # core member.  It is proof-safe only when local_mss retained
                # the positive original core that supports that assumption.
                expanded.update(backbone2core.get(index, ()))
            else:
                # Positive assumptions remain original soft constraints even
                # when an inherited backbone2core happens to use the same ID.
                expanded.add(index)
        return frozenset(expanded)

    def _publish_probe_core(
        self,
        core: frozenset[int],
        assignment: dict[int, bool],
        backbone2core: dict[int, frozenset[int]] | None = None,
    ) -> frozenset[int]:
        expanded = self._expanded_core(core, backbone2core or {}, assignment)
        if not expanded:
            return frozenset()
        reduced = self.reduce_core(expanded)
        if reduced:
            self.coordinator.publish_core(self.worker_id, self.role, reduced, original=True)
        return reduced

    def local_mss(self, new_model: z3.ModelRef) -> bool:
        """Grow an MSS, collecting cores/backbones as in hs.py's local_mss."""
        assert self.translated is not None
        all_ids = set(range(len(self.translated.soft)))
        mss: set[int] = set()
        for soft in self.translated.soft:
            if self.interrupted():
                return False
            if z3.is_true(new_model.eval(soft.formula, model_completion=True)):
                mss.add(soft.index)
        pending = all_ids - mss
        backbones: set[int] = set()
        backbone2core: dict[int, frozenset[int]] = {}
        unknown: set[int] = set()
        improved = False

        while pending and not self.interrupted():
            p = self._ordered(pending)[0]
            pending.remove(p)
            trues = mss | {p}
            assignment = {i: True for i in trues} | {i: False for i in backbones}
            result, model, raw_core = self._probe_values(trues, backbones)
            if result == z3.sat:
                assert model is not None
                newly_true: set[int] = set()
                for q in unknown:
                    if self.interrupted():
                        return improved
                    if z3.is_true(
                        model.eval(self.translated.soft[q].formula, model_completion=True)
                    ):
                        newly_true.add(q)
                rs = {p} | newly_true
                mss.update(rs)
                pending.difference_update(rs)
                unknown.difference_update(rs)
                if self._publish_model(model):
                    improved = True
            elif result == z3.unsat:
                reduced = self._publish_probe_core(raw_core, assignment, backbone2core)
                if reduced:
                    # The attempted true literal p is a local backbone under
                    # the current MSS; remember the supporting original core.
                    backbone2core[p] = frozenset(set(reduced) - {p})
                    backbones.add(p)
            else:
                unknown.add(p)

        if unknown and not self.interrupted():
            # Give unresolved probes one final deterministic pass before the
            # rotation phase; UNKNOWN never becomes proof information.
            for p in self._ordered(unknown):
                if self.interrupted():
                    break
                result, model, raw_core = self._probe_values(mss | {p}, backbones)
                assignment = {i: True for i in mss | {p}} | {i: False for i in backbones}
                if result == z3.sat and model is not None:
                    mss.add(p)
                    if self._publish_model(model):
                        improved = True
                elif result == z3.unsat and raw_core:
                    reduced = self._publish_probe_core(raw_core, assignment, backbone2core)
                    if reduced:
                        backbone2core[p] = frozenset(set(reduced) - {p})
                        backbones.add(p)

        if improved and not self.interrupted():
            self.mss_rotate(mss, backbone2core)
        return improved

    def try_rotate(self, mss: set[int], backbone2core: dict[int, frozenset[int]]) -> bool:
        """Try adding falsified softs after temporarily dropping MSS members."""
        if self.interrupted():
            return False
        ps = set(range(self.objective.size)) - set(mss)
        backbones: set[int] = set()
        improved = False
        while ps and not self.interrupted():
            p = self._ordered(ps)[0]
            ps.remove(p)
            result, model, raw_core = self._probe_values(set(mss) | {p}, backbones)
            assignment = {i: True for i in set(mss) | {p}} | {i: False for i in backbones}
            if result == z3.sat and model is not None:
                mss.add(p)
                if self.translated is not None:
                    newly_satisfied: set[int] = set()
                    for q in ps:
                        if self.interrupted():
                            return improved
                        if z3.is_true(
                            model.eval(self.translated.soft[q].formula, model_completion=True)
                        ):
                            newly_satisfied.add(q)
                    ps.difference_update(newly_satisfied)
                if self._publish_model(model):
                    improved = True
            elif result == z3.unsat and raw_core:
                reduced = self._publish_probe_core(raw_core, assignment, backbone2core)
                if reduced:
                    backbones.add(p)
                    backbone2core[p] = frozenset(set(reduced) - {p})
        return improved

    def mss_rotate(self, mss: set[int], backbone2core: dict[int, frozenset[int]]) -> bool:
        """Retry rotation after dropping high-frequency MSS members."""
        if self._rotation_depth >= 2 or self.interrupted():
            return False
        counts = {index: 0 for index in mss}
        for core in backbone2core.values():
            for index in core:
                if index in counts:
                    counts[index] += 1
        candidates = sorted(
            (index for index, count in counts.items() if count > 1),
            key=lambda index: (-counts[index], self.objective.weights[index], index),
        )
        for index in candidates:
            self._rotation_depth += 1
            try:
                if self.try_rotate(set(mss) - {index}, dict(backbone2core)):
                    self.rotation_count += 1
                    return True
            finally:
                self._rotation_depth -= 1
        return False

    def run_worker(self) -> None:
        while not self.interrupted():
            snap = self.snapshot()
            if snap.incumbent_falsified is None:
                result, model, core = self._probe_values([], [])
                if result == z3.sat and model is not None:
                    self._publish_model(model)
                    self.local_mss(model)
                elif result == z3.unsat and not core:
                    self.coordinator.publish_unsat(self.worker_id, self.role)
            else:
                falsified = set(snap.incumbent_falsified)
                satisfied = [i for i in range(self.objective.size) if i not in falsified]
                release = self._pick_release(satisfied)
                fixed = [i for i in satisfied if i not in release]
                result, model, core = self._probe_values(fixed, [])
                if result == z3.sat and model is not None:
                    self._publish_model(model)
                    self.local_mss(model)
                elif result == z3.unsat and core:
                    self._publish_probe_core(core, {i: True for i in fixed})
                elif result == z3.unsat:
                    self.coordinator.publish_unsat(self.worker_id, self.role)
            self.stop_event.wait(0.01)

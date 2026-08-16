"""Sampled-backbone probing with mandatory refutation validation."""
from __future__ import annotations

import z3

from .base import WorkerBase, boolean_symbols


class BackboneWorker(WorkerBase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.asserted_backbones: set[tuple[str, bool]] = set()
        self.refuted_candidates: dict[tuple[str, bool], dict[str, bool | str]] = {}
        self.sample_count = 0
        self._common: dict[str, bool] | None = None
        self._symbols: dict[str, z3.BoolRef] | None = None

    def _symbol_table(self) -> dict[str, z3.BoolRef]:
        assert self.translated is not None
        if self._symbols is None:
            self._symbols = boolean_symbols(self.translated, self.interrupted)
        return self._symbols

    def _release_context_objects(self) -> None:
        super()._release_context_objects()
        self._symbols = None

    def _sample(self) -> z3.ModelRef | None:
        assert self.translated is not None and self.ctx is not None
        solver = z3.Solver(ctx=self.ctx)
        solver.set(timeout=self.check_timeout_ms)
        solver.set(random_seed=self.rng.randrange(1, 2**30))
        solver.set(phase_selection=self.rng.randrange(0, 6))
        solver.add(*self.translated.hard)
        # Candidate literals are deliberately not asserted here.  Sampling
        # consensus is evidence only; using it as a permanent fact would be a
        # soundness bug.  A caller may use an unvalidated candidate as a
        # retractable assumption, but this worker does not need to do so.
        if solver.check() != z3.sat:
            return None
        return solver.model()

    def validate_candidate(
        self, literal: tuple[str, bool]
    ) -> tuple[str, dict[str, bool | str] | None]:
        """Refute ``hard ∧ ¬literal`` in this worker's context.

        Returns ``("validated", None)`` only on a real UNSAT result;
        ``("refuted", model)`` records a free counterexample; ``("unknown",
        None)`` is never asserted.
        """
        assert self.translated is not None and self.ctx is not None
        symbols = self._symbol_table()

        var = symbols.get(literal[0])
        if var is None:
            return "unknown", None
        lit = var if literal[1] else z3.Not(var)
        solver = z3.Solver(ctx=self.ctx)
        solver.set(timeout=self.check_timeout_ms)
        solver.add(*self.translated.hard)
        solver.add(z3.Not(lit))
        result = solver.check()
        if result == z3.unsat:
            # This is the only branch where a sampled literal may become a
            # fact in this worker.  Refuted candidates never reach add(lit).
            return "validated", None
        if result == z3.sat:
            return "refuted", self._model_payload(solver.model())
        return "unknown", None

    def _triage(self, model: z3.ModelRef) -> None:
        assert self.translated is not None
        symbols = self._symbol_table()
        values: dict[str, bool] = {}
        for name, symbol in symbols.items():
            if self.interrupted():
                return
            values[name] = z3.is_true(model.eval(symbol, model_completion=True))
        if self._common is None:
            self._common = values
        else:
            common: dict[str, bool] = {}
            for name, value in self._common.items():
                if self.interrupted():
                    return
                if name in values and values[name] == value:
                    common[name] = value
            self._common = common

        for name, value in list(self._common.items()):
            if self.interrupted():
                return

            literal = (name, value)
            if literal in self.asserted_backbones or literal in self.refuted_candidates:
                continue
            self.coordinator.publish_backbone_candidate(
                self.worker_id, self.role, literal
            )

            result, countermodel = self.validate_candidate(literal)
            if result == "validated":
                self.asserted_backbones.add(literal)
                self.coordinator.publish_backbone(self.worker_id, self.role, literal, validated=True)
            elif result == "refuted":
                assert countermodel is not None
                self.refuted_candidates[literal] = countermodel
                self.coordinator.publish_backbone_refuted(
                    self.worker_id,
                    self.role,
                    literal,
                    countermodel,
                )
                self._common.pop(name, None)

    def run_worker(self) -> None:
        self._symbol_table()
        while not self.interrupted():
            model = self._sample()
            if model is not None:
                self.sample_count += 1
                self._publish_model(model)
                self._triage(model)
            self.stop_event.wait(0.02)

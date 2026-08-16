"""Z3 Optimize portfolio worker."""
from __future__ import annotations

from .base import WorkerBase
import z3


class ZOptWorker(WorkerBase):
    def _solve_once(self) -> None:
        assert self.translated is not None
        opt = self._optimize()
        opt.add(*self.translated.hard)
        for sft in self.translated.soft:
            if self.stop_event.is_set():
                raise InterruptedError("Optimize construction interrupted")
            opt.add_soft(sft.formula, weight=str(sft.weight))
        result = opt.check()
        if result == z3.sat:
            self._publish_model(opt.model())

    def run_worker(self) -> None:
        # Optimize is a complete portfolio member for an independent model and
        # bound trajectory.  The certificate still comes only from original
        # cores plus the independently measured incumbent.
        while not self.interrupted():
            self._solve_once()
            if self.stop_event.wait(0.2):
                break

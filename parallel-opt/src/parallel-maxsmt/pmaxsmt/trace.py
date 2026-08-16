"""Thread-safe JSONL anytime telemetry."""
from __future__ import annotations

from dataclasses import dataclass, asdict
import json
from pathlib import Path
import sys
import threading
import time
from typing import TextIO, Any


@dataclass(frozen=True)
class TraceEvent:
    timestamp: float
    worker_id: str
    role: str
    event: str
    lb: int | None
    ub: int | None
    status: str | None
    details: dict[str, Any] | None = None


class TraceWriter:
    def __init__(self, target: str | Path | TextIO | None = None):
        self._lock = threading.Lock()
        self._owned = False
        if target is None:
            self._stream = None
        elif hasattr(target, "write"):
            self._stream = target
        else:
            self._stream = open(target, "w", encoding="utf-8")
            self._owned = True

    def emit(
        self,
        worker_id: str,
        role: str,
        event: str,
        lb: int | None = None,
        ub: int | None = None,
        status: str | None = None,
        **details: Any,
    ) -> TraceEvent:
        item = TraceEvent(time.time(), str(worker_id), str(role), str(event), lb, ub, status, details or None)
        if self._stream is not None:
            payload = asdict(item)
            with self._lock:
                self._stream.write(json.dumps(payload, sort_keys=True) + "\n")
                self._stream.flush()
        return item

    def close(self) -> None:
        if self._owned and self._stream is not None:
            with self._lock:
                self._stream.close()
            self._stream = None

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        self.close()

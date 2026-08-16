"""Static worker-role allocation and CLI parsing."""
from __future__ import annotations

from dataclasses import dataclass


ROLE_NAMES = ("hs", "mss", "backbone", "maxres", "zopt")


@dataclass(frozen=True)
class RoleSpec:
    hs: int = 1
    mss: int = 1
    backbone: int = 1
    maxres: int = 0
    zopt: int = 0

    def __post_init__(self) -> None:
        for name in ROLE_NAMES:
            value = getattr(self, name)
            if not isinstance(value, int) or value < 0:
                raise ValueError(f"role count {name} must be a non-negative integer")
        if self.total <= 0:
            raise ValueError("at least one worker role is required")

    @property
    def total(self) -> int:
        return sum(getattr(self, name) for name in ROLE_NAMES)

    def items(self):
        return tuple((name, getattr(self, name)) for name in ROLE_NAMES)

    def workers(self) -> tuple[tuple[str, int], ...]:
        return tuple((role, i) for role, count in self.items() for i in range(count))

    def as_dict(self) -> dict[str, int]:
        return dict(self.items())


def default_roles(threads: int) -> RoleSpec:
    if not isinstance(threads, int) or threads <= 0:
        raise ValueError("threads must be a positive integer")
    # Always reserve one exact IHS worker.  Diversify the remaining static
    # slots without any run-time role reallocation.
    counts = {name: 0 for name in ROLE_NAMES}
    counts["hs"] = 1
    order = ("mss", "backbone", "zopt", "maxres")
    for i in range(threads - 1):
        counts[order[i % len(order)]] += 1
    return RoleSpec(**counts)


def parse_roles(spec: str | None, threads: int) -> RoleSpec:
    if spec is None or not spec.strip():
        return default_roles(threads)
    counts = {name: 0 for name in ROLE_NAMES}
    seen: set[str] = set()
    for item in spec.split(","):
        item = item.strip()
        if not item:
            continue
        if "=" not in item:
            raise ValueError(f"invalid role entry {item!r}; expected name=count")
        name, raw = (part.strip().lower() for part in item.split("=", 1))
        if name not in ROLE_NAMES:
            raise ValueError(f"unknown role {name!r}; choose from {', '.join(ROLE_NAMES)}")
        if name in seen:
            raise ValueError(f"duplicate role {name!r}")
        seen.add(name)
        try:
            value = int(raw)
        except ValueError as exc:
            raise ValueError(f"role count for {name!r} must be an integer") from exc
        if value < 0:
            raise ValueError(f"role count for {name!r} must be non-negative")
        counts[name] = value
    if sum(counts.values()) != threads:
        raise ValueError(
            f"role counts sum to {sum(counts.values())}, but --threads is {threads}; "
            "static allocation requires an exact match"
        )
    return RoleSpec(**counts)

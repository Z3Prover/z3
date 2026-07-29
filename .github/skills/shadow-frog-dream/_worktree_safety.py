"""Single source of truth for the "is it safe to rm -rf this dream worktree?" gate.

Imported by `dream-reconcile.py` and invoked as a subprocess by
`dream-cleanup.sh` + `dream-gc.sh`. Both bash callers pass the candidate
path + the configured base via argv (NOT via string interpolation), so the
caller can never inject Python source through this module.

A path is considered safe to remove ONLY when ALL of these hold:

1. Path and base are both non-empty strings.
2. Path and base are both absolute (start with "/").
3. Neither contains a ".." component in the literal input.
4. The resolved (symlink-followed) base is not a sensitive filesystem root
   (e.g. /, /tmp, /home, $HOME, /Users, /etc, /usr).
5. After resolving symlinks in the path's parent directory, the resolved
   path is STRICTLY INSIDE the resolved base — not equal to it, and not
   above it.
6. The path matches the exact dream-worktree shape `<base>/<ns>/dream-<slug>`
   where `<ns>` and `<slug>` are each `[A-Za-z0-9._-]+` (the same `SAFE_RE`
   that `dream-setup.sh` already enforces on the inputs).

These rules are deliberately strict: they reject anything that doesn't look
like a dream worktree created by `dream-setup.sh`. That means we will NEVER
`rm -rf` a path the user happens to point us at — only paths that match the
namespace's own creation contract.

CLI invocation (used by the bash scripts):
    python3 _worktree_safety.py <worktree-dir> <base> [<ns>]
    exit codes:
      0 → safe AND the path currently exists (caller should rm)
      2 → safe AND the path does NOT exist  (caller should treat as no-op)
      1 → UNSAFE; do not rm                  (error printed to stderr)
"""
from __future__ import annotations

import os
import re
import sys
from pathlib import Path

# Same regex `dream-setup.sh` validates --slug and --namespace against.
# Keep these in lockstep — if one widens, the other must follow.
_SAFE_RE = re.compile(r"^[A-Za-z0-9._-]+$")

# Defense-in-depth: even if rule 5 (strictly under base) holds, refuse
# outright if the BASE itself lands on one of these. Checked against BOTH
# the literal input AND the symlink-resolved value, with macOS's `/private`
# prefix stripped — otherwise `/tmp` → `/private/tmp` would silently bypass
# the check on macOS (verified empirically: macOS `realpath /tmp` returns
# `/private/tmp` which is not in the list, so the literal `/tmp` check is
# what catches it).
_FORBIDDEN_BASES = frozenset({
    "/",
    "/bin", "/boot", "/dev", "/etc", "/home", "/lib", "/lib32", "/lib64",
    "/Library", "/mnt", "/media", "/opt", "/private", "/proc", "/root",
    "/run", "/sbin", "/srv", "/sys", "/System", "/tmp", "/Users", "/usr",
    "/Users/Shared", "/var", "/var/folders", "/var/tmp",
})

# macOS-specific: `/private` is the real location for `/tmp`, `/etc`,
# `/var`. After `realpath` these all gain the `/private` prefix.
_MACOS_PRIVATE_PREFIX = "/private"


def _strip_macos_private(p: str) -> str:
    """Strip the macOS `/private` prefix so resolved paths can be compared
    against the bare forbidden roots. `/private` itself stays `/private`."""
    if p.startswith(_MACOS_PRIVATE_PREFIX + "/"):
        return p[len(_MACOS_PRIVATE_PREFIX):]
    return p


class UnsafePath(ValueError):
    """Raised when the candidate path fails any of the safety rules."""


def safe_worktree_path(path: str, base: str) -> Path:
    """Validate `path` is a safe-to-remove dream worktree under `base`.

    Returns the symlink-resolved `Path` on success.
    Raises `UnsafePath` on any rule violation.
    Does NOT touch the filesystem beyond `os.path.realpath` resolution.
    """
    # Rule 1: non-empty.
    if not isinstance(path, str) or not path.strip():
        raise UnsafePath(f"empty or non-string worktree path: {path!r}")
    if not isinstance(base, str) or not base.strip():
        raise UnsafePath(f"empty or non-string base: {base!r}")

    # Rule 2: absolute.
    if not path.startswith("/"):
        raise UnsafePath(f"worktree path is not absolute: {path!r}")
    if not base.startswith("/"):
        raise UnsafePath(f"base is not absolute: {base!r}")

    # Rule 3: no ".." traversal in the literal input. Catches things that
    # would otherwise normalize past the base.
    for part in path.split("/"):
        if part == "..":
            raise UnsafePath(f"worktree path contains '..': {path!r}")
    for part in base.split("/"):
        if part == "..":
            raise UnsafePath(f"base contains '..': {base!r}")

    # Resolve the base: this is what we compare against.
    base_res = os.path.realpath(base)

    # Rule 4: refuse sensitive bases. Compare against three normalizations
    # so a symlink shenanigan (`$HOME/my-worktrees → /`) AND macOS's
    # implicit `/tmp → /private/tmp` redirection both fail closed.
    base_norm = os.path.normpath(base)
    candidates = {base_norm, base_res, _strip_macos_private(base_res)}
    forbidden = set(_FORBIDDEN_BASES)
    home = os.path.expanduser("~")
    if home and home != "~":
        forbidden.add(home)
        forbidden.add(_strip_macos_private(os.path.realpath(home)))
    if candidates & forbidden:
        raise UnsafePath(
            f"refusing sweep: base resolves to a sensitive root: "
            f"{base!r} (literal={base_norm!r} resolved={base_res!r})"
        )

    # Resolve the path's PARENT (not the path itself — the leaf may not
    # exist, which is fine for the rm-is-a-no-op case). os.path.realpath
    # walks all symlinks; combining with the literal leaf prevents a
    # symlink AT the leaf from escaping the base after a successful check.
    stripped = path.rstrip("/")
    parent_lit = os.path.dirname(stripped) or "/"
    leaf = os.path.basename(stripped)
    parent_res = os.path.realpath(parent_lit)
    resolved = os.path.join(parent_res, leaf)

    # If the leaf is itself a symlink, follow it AFTER constructing
    # `resolved` so the strict-inside-base check uses the real target.
    if os.path.islink(resolved):
        resolved = os.path.realpath(resolved)

    # Rule 5: strictly under base.
    try:
        rel = os.path.relpath(resolved, base_res)
    except ValueError as exc:
        raise UnsafePath(
            f"worktree path {resolved!r} not relatable to base "
            f"{base_res!r}: {exc}"
        ) from None
    if rel == "." or rel.startswith(".."):
        raise UnsafePath(
            f"worktree path {resolved!r} is not strictly under base "
            f"{base_res!r} (relpath={rel!r})"
        )

    # Rule 6: exact dream-worktree shape: <base>/<ns>/dream-<slug>.
    parts = rel.split(os.sep)
    if len(parts) != 2:
        raise UnsafePath(
            f"worktree path {resolved!r} is not exactly 2 levels under "
            f"base {base_res!r} (got parts={parts!r})"
        )
    ns_part, leaf_part = parts
    if not _SAFE_RE.match(ns_part):
        raise UnsafePath(
            f"namespace component {ns_part!r} does not match {_SAFE_RE.pattern}"
        )
    if not leaf_part.startswith("dream-"):
        raise UnsafePath(
            f"leaf {leaf_part!r} does not start with 'dream-'"
        )
    slug_part = leaf_part[len("dream-"):]
    if not slug_part or not _SAFE_RE.match(slug_part):
        raise UnsafePath(
            f"slug component {slug_part!r} does not match {_SAFE_RE.pattern}"
        )

    return Path(resolved)


def _cli() -> int:
    if len(sys.argv) < 3:
        print(
            "usage: _worktree_safety.py <worktree-dir> <base>",
            file=sys.stderr,
        )
        return 1
    path, base = sys.argv[1], sys.argv[2]
    try:
        resolved = safe_worktree_path(path, base)
    except UnsafePath as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    except (ValueError, OSError) as exc:
        # Defensive: e.g. embedded NUL would raise ValueError from
        # os.path.realpath. Treat any non-UnsafePath gate failure as
        # "refused" rather than crashing with a traceback that the bash
        # caller would interpret as exit-code-1 anyway, but noisily.
        print(f"ERROR: gate failure: {exc}", file=sys.stderr)
        return 1
    # Check existence on the RESOLVED path. islink() catches dangling
    # symlinks (which `exists()` reports as False but which we should
    # still remove).
    if resolved.exists() or resolved.is_symlink():
        return 0
    return 2


if __name__ == "__main__":
    sys.exit(_cli())

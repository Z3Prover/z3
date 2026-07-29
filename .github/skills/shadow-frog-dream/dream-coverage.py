#!/usr/bin/env python3
"""Dream coverage map — compute exploration coverage for task planning.

Usage:
  python3 dream-coverage.py [REPO_ROOT]
  python3 dream-coverage.py [REPO_ROOT] --scope src/auth/ --scope src/db/

Outputs:
  - Coverage summary (total, covered, uncovered)
  - Saturated files (8+ discoveries)
  - High-value uncovered files (sorted by fan-in)
  - Per-directory coverage

Coverage definition: A file is "covered" if its shadow file has at least 1
behavioral discovery (line starting with "- "). Files with only placeholder
text ("_No discoveries yet._") are NOT covered.

Scoped exploration (--scope):
  Restricts the coverage map to files whose path starts with one of the
  given prefixes. Repeatable. Use this to focus a dream session on a
  specific subtree (e.g., a frontier area where bug density is high).
  All counts (totals, %, saturated, fan-in, per-dir) are computed over
  the scoped subset only. Exits nonzero if a non-empty --scope list
  matches zero files so callers notice typos.

Replaces the inline bash coverage map block in SKILL.md, fixing:
  - Space-delimited filename handling (now uses Python lists)
  - O(n²) fan-in computation (now batched with cap)
  - Division by zero on empty repos
  - Hardcoded temp file collisions
  - Coverage = file existence (now = discovery_count > 0)
"""

import argparse
import os
import subprocess
import sys
from collections import defaultdict

# Directory components and suffixes to exclude. Kept in lockstep with
# shadow-init.py's EXCLUDE_DIRS / EXCLUDE_PATTERNS_SUFFIX so coverage's
# denominator is exactly the set of files init shadows (tests INCLUDED —
# init shadows them, so excluding them here would hide shadowed test files
# from the "uncovered" list and inflate the coverage percentage).
EXCLUDE_DIRS = {
    "node_modules", "vendor", "venv", ".venv", "__pycache__",
    "dist", "build", "target", "out", ".shadow",
}
EXCLUDE_SUFFIXES = (".min.js", ".min.css", ".map", ".lock")


def _is_excluded_path(rel_path):
    """Match shadow-init.py: excluded directory component or suffix."""
    parts = rel_path.replace(os.sep, "/").split("/")
    if any(part in EXCLUDE_DIRS for part in parts):
        return True
    return any(rel_path.endswith(suffix) for suffix in EXCLUDE_SUFFIXES)


# Source file selection — must mirror shadow-init.py's _is_source_file so
# coverage's denominator matches the set of files init actually shadows.
# Without this, non-source tracked files (READMEs, images, docs) are counted
# as "uncovered source files" and skew dream planning.
SOURCE_EXTENSIONS = {
    ".py",
    ".js", ".jsx", ".ts", ".tsx", ".mjs", ".cjs",
    ".java", ".kt", ".kts", ".scala",
    ".go",
    ".rs",
    ".rb",
    ".c", ".h", ".cpp", ".hpp", ".cc", ".hh", ".cxx", ".hxx",
    ".cs",
    ".php",
    ".sh", ".bash", ".zsh",
    ".swift",
    ".yaml", ".yml", ".toml", ".json",
}
SOURCE_BASENAMES = {"Makefile", "Dockerfile", "Containerfile", "Rakefile", "Gemfile"}


def _is_source_file(rel_path):
    """Match shadow-init.py: known source extensions or basenames."""
    base = os.path.basename(rel_path)
    if base in SOURCE_BASENAMES:
        return True
    _, ext = os.path.splitext(base)
    return ext.lower() in SOURCE_EXTENSIONS


def get_source_files(repo_root, scopes=None):
    """Get all tracked source files (same selection rules as shadow-init.py).

    If `scopes` is a non-empty list of path prefixes, only files whose
    path starts with at least one prefix are returned. Prefix matching
    is literal (use a trailing '/' to scope a directory cleanly).
    """
    result = subprocess.run(
        ['git', 'ls-files', '-z'],
        capture_output=True, text=True, cwd=repo_root, encoding="utf-8"
    )
    files = []
    for f in result.stdout.split('\0'):
        if not f or _is_excluded_path(f):
            continue
        if not _is_source_file(f):
            continue
        if scopes and not any(f.startswith(p) for p in scopes):
            continue
        files.append(f)
    return files


def _count_discoveries(shadow_path):
    """Count `- ` bullets that are real discoveries.

    Bullets inside a `## Cross-References` section are back-pointer links
    to `_cross/*.md`, NOT discoveries. Skip them.
    """
    count = 0
    in_xref = False
    with open(shadow_path, encoding="utf-8") as sf:
        for line in sf:
            stripped = line.rstrip('\n')
            if stripped.startswith('## ') or stripped.startswith('### '):
                in_xref = stripped.strip().lower().startswith('## cross-references')
                continue
            if not in_xref and line.startswith('- '):
                count += 1
    return count


def check_coverage(repo_root, files):
    """Check shadow coverage. Covered = discovery_count > 0."""
    covered = []
    uncovered = []
    saturated = []

    for f in files:
        shadow = os.path.join(repo_root, '.shadow', f + '.md')
        if os.path.isfile(shadow):
            count = _count_discoveries(shadow)
            if count > 0:
                covered.append((f, count))
                if count >= 8:
                    saturated.append((f, count))
            else:
                # Shadow exists but no real discoveries (placeholder only)
                uncovered.append(f)
        else:
            uncovered.append(f)

    return covered, uncovered, saturated


def compute_fan_in(repo_root, uncovered_files, max_files=200):
    """Compute fan-in for uncovered files. Capped at max_files to avoid timeout."""
    if not uncovered_files:
        return {}

    # Deduplicate basenames and batch
    basenames = {}
    for f in uncovered_files[:max_files]:
        base = os.path.splitext(os.path.basename(f))[0]
        if base not in basenames:
            basenames[base] = []
        basenames[base].append(f)

    fan_in = defaultdict(int)
    for base, files_for_base in basenames.items():
        try:
            result = subprocess.run(
                ['git', 'grep', '-F', '-w', '-l', '--', base],
                capture_output=True, text=True, cwd=repo_root,
                timeout=10, encoding="utf-8"
            )
            count = len([l for l in result.stdout.strip().split('\n') if l]) if result.stdout.strip() else 0
            for f in files_for_base:
                fan_in[f] = count
        except (subprocess.TimeoutExpired, OSError):
            for f in files_for_base:
                fan_in[f] = 0

    return fan_in


def main():
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(
        description="Dream coverage map — compute exploration coverage for task planning.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    parser.add_argument(
        'repo_root', nargs='?', default=os.getcwd(),
        help='Repository root (defaults to current working directory).',
    )
    parser.add_argument(
        '--scope', action='append', default=[], metavar='PREFIX',
        help='Restrict coverage to files whose path starts with PREFIX. '
             'Repeatable (e.g., --scope src/auth/ --scope src/db/). '
             'Trailing slash recommended for directory prefixes.',
    )
    args = parser.parse_args()
    repo_root = args.repo_root
    scopes = args.scope

    print("=== EXPLORATION COVERAGE MAP ===")
    if scopes:
        print(f"Scope filters: {', '.join(scopes)}")

    files = get_source_files(repo_root, scopes=scopes)
    total = len(files)
    print(f"Total source files: {total}")

    if total == 0:
        if scopes:
            print(f"No source files matched scope filters: {scopes}")
            print("Check prefix spelling (trailing slash matters).")
            sys.exit(2)
        print("No source files found after filtering.")
        print("Coverage: N/A")
        return

    covered, uncovered, saturated = check_coverage(repo_root, files)

    for f, count in saturated:
        print(f"SATURATED ({count}): {f}")

    pct = len(covered) * 100 // total
    print(f"Covered: {len(covered)} / {total} ({pct}%)")
    print(f"Uncovered: {len(uncovered)}")

    # High-value uncovered files
    if uncovered:
        print()
        print("=== HIGH-VALUE UNCOVERED FILES ===")
        fan_in = compute_fan_in(repo_root, uncovered)
        ranked = sorted(uncovered, key=lambda f: fan_in.get(f, 0), reverse=True)
        for f in ranked[:30]:
            refs = fan_in.get(f, 0)
            print(f"{refs} {f}")
        print("(sorted by reference count — high fan-in files should be explored first)")

    # Per-directory coverage
    if uncovered:
        print()
        print("=== DIRECTORY COVERAGE ===")
        dir_stats = defaultdict(lambda: {'total': 0, 'covered': 0})
        for f in files:
            d = os.path.dirname(f) or '.'
            dir_stats[d]['total'] += 1
        for f, _ in covered:
            d = os.path.dirname(f) or '.'
            dir_stats[d]['covered'] += 1

        for d in sorted(dir_stats.keys()):
            s = dir_stats[d]
            if s['covered'] < s['total']:
                print(f"{d}: {s['covered']} / {s['total']}")


if __name__ == '__main__':
    main()

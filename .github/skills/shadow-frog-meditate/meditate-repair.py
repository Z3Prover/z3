#!/usr/bin/env python3
"""Repair _dreams/_index.md rows from their own report.md + manifest.json.

Used by shadow-frog-meditate when the index has been corrupted or has
'unknown' category/verdict/title cells. Safe to rerun — only rows with
the targeted defects are touched.

Usage:
    python3 meditate-repair.py [--shadow-dir DIR]

Defaults to ./.shadow/. Writes a .bak backup of the index before
modifying.

Logic:
1. Detect corrupted reports (frontmatter dream_id doesn't match folder
   name). These rows are flagged in stderr and skipped — the user must
   resolve manually.
2. For each non-corrupted row with 'unknown' or empty
   category/verdict/title, look up the canonical value from the report's
   frontmatter, manifest's verdict field, or verdict section signals.
3. Verdict detection order: manifest > VERDICT_SECTION signals >
   whole-body signals. Dead-end signals are checked BEFORE useful
   signals so 'not useful' doesn't match 'useful'.
4. Title repair: replace generic titles (raw slug, "Dream Report: <slug>",
   "Dream t##: <slug>") with the first H1 or first ## Summary line.
5. Parent linkage from manifest: for rows where parent is 'main', check
   manifest.json and report.md frontmatter for a different parent_branch.
   Validate the parent exists in the index (match by slug if timestamps
   differ).
6. Parent linkage from slug heuristics: for rows still parented to 'main'
   with no manifest info, infer from compounding suffixes (-extend, -fix,
   -deeper, -improve, -integration, -cleanup, -metrics, -remaining).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys


DREAM_ID_RE = re.compile(r'^(\d{8}-\d{6}Z)-(.+)$')
COMPOUNDING_SUFFIXES = re.compile(
    r'-(extend|fix|deeper|improve|integration|cleanup|metrics|remaining)$'
)

DEAD_SIGNALS = re.compile(
    r'\bdead.end\b|\bdead_end\b|no improvement|\bnot useful\b'
    r'|\u274c|\bfailed to\b|\binconclusive\b',
    re.I,
)
USEFUL_SIGNALS = re.compile(
    r'\buseful\b|verdict:\s*useful|\btests pass\b|\ball pass\b'
    r'|\bpassed in\b|\b0 failed\b|\u2705|\d+ (tests )?passed'
    r'|\bconfirmed\b|\bverified\b',
    re.I,
)
GENERIC_TITLE = re.compile(
    r'^(Dream Report:\s*|Dream t\d+:\s*)?[a-z0-9-]+$',
    re.I,
)
VERDICT_SECTION = re.compile(r'## Verdict[^\n]*\n(.*?)(?=\n## |\Z)', re.S)


def detect_corrupted(dreams_dir: str) -> set[str]:
    """Find dream folders whose report.md frontmatter ID doesn't match."""
    corrupted: set[str] = set()
    for d in os.listdir(dreams_dir):
        dpath = os.path.join(dreams_dir, d)
        if not os.path.isdir(dpath) or d.startswith('_'):
            continue
        report = os.path.join(dpath, 'report.md')
        if not os.path.exists(report):
            continue
        with open(report, encoding="utf-8") as rf:
            rcontent = rf.read()
        fm_match = re.search(r'dream_id:\s*(\S+)', rcontent)
        body_match = re.search(r'\*\*Dream ID\*\*:\s*(\S+)', rcontent)
        found_id: str | None = None
        if fm_match:
            found_id = fm_match.group(1).strip().strip('"').strip("'")
        elif body_match:
            found_id = body_match.group(1).strip().strip('"').strip("'")
        if found_id and found_id != d:
            corrupted.add(d)
            print(
                f'WARNING CORRUPTED: {d} contains report from {found_id}',
                file=sys.stderr,
            )
    return corrupted


def lookup_verdict(dream_dir: str, content: str) -> str:
    """Resolve verdict via manifest, verdict section, then whole-body scan."""
    manifest = os.path.join(dream_dir, 'manifest.json')
    if os.path.exists(manifest):
        try:
            with open(manifest, encoding="utf-8") as mf:
                mdata = json.load(mf)
            v = (mdata.get('verdict') or '').lower().strip()
            if v and v != 'unknown':
                return v
        except (OSError, json.JSONDecodeError):
            pass
    vsec = VERDICT_SECTION.search(content)
    scan_text = vsec.group(1) if vsec else content
    if DEAD_SIGNALS.search(scan_text):
        return 'dead_end'
    if USEFUL_SIGNALS.search(scan_text):
        return 'useful'
    return ''


def repair_row(parts: list[str], dreams_dir: str) -> tuple[list[str], bool] | None:
    """Repair a single index row in-place. Returns (updated parts, changed) or None."""
    did = parts[1]
    dream_dir = os.path.join(dreams_dir, did)
    report = os.path.join(dream_dir, 'report.md')
    if not os.path.exists(report):
        return None
    with open(report, encoding="utf-8") as rf:
        content = rf.read()

    original = list(parts)

    cat_match = re.search(r'\*\*Category\*\*:\s*(.+)', content)
    if not cat_match:
        # Category is stored in YAML frontmatter (`category: <value>`),
        # not as a `**Category**:` body marker.
        cat_match = re.search(r'^category:\s*(.+)', content, re.M)
    if cat_match and parts[2].strip().lower() in ('unknown', ''):
        parts[2] = cat_match.group(1).strip().strip('"\'').lower()
        parts[2] = re.sub(r'\s*\(.*\)\s*$', '', parts[2])
    parts[2] = parts[2].lower().strip()

    if parts[3].strip().lower() in ('unknown', ''):
        v = lookup_verdict(dream_dir, content)
        if v:
            parts[3] = v

    if GENERIC_TITLE.match(parts[4].strip()):
        heading = re.search(r'^#\s+(.+)', content, re.M)
        if heading and not GENERIC_TITLE.match(heading.group(1).strip()):
            parts[4] = heading.group(1).strip()[:80]
        else:
            summary = re.search(r'## Summary\s*\n+(.+)', content)
            if summary:
                parts[4] = summary.group(1).strip()[:80]

    did_change = parts != original
    return parts, did_change


def parse_dream_id(did: str) -> tuple[str, str] | None:
    """Split dream_id into (timestamp, slug) or None if malformed."""
    m = DREAM_ID_RE.match(did)
    if m:
        return m.group(1), m.group(2)
    return None


def resolve_parent_in_index(
    parent_id: str, all_dream_ids: list[str]
) -> str | None:
    """Resolve a parent dream_id against the index, matching by slug if needed."""
    if parent_id in all_dream_ids:
        return parent_id
    parsed = parse_dream_id(parent_id)
    if not parsed:
        return None
    _, parent_slug = parsed
    for did in all_dream_ids:
        p = parse_dream_id(did)
        if p and p[1] == parent_slug:
            return did
    return None


def repair_parent(
    parts: list[str], dreams_dir: str, all_dream_ids: list[str],
    branch_by_dream_id: dict[str, str],
) -> bool:
    """Repair the parent cell (index 6) if it is 'main' and better info exists.

    The parent column is canonically a BRANCH NAME (matching what the
    reconciler writes from `manifest.parent_branch` and what dream-lineage.py
    keys its graph on), NOT a dream_id. So once we resolve the parent to an
    indexed row, we write that row's branch — not its dream_id.

    Returns True if the parent was changed.
    """
    did = parts[1]
    parent = parts[6].strip()
    if parent != 'main':
        return False

    dream_dir = os.path.join(dreams_dir, did)
    resolved_did: str | None = None

    # Step 10: manifest.json lookup
    manifest_path = os.path.join(dream_dir, 'manifest.json')
    parent_branch_raw: str | None = None
    if os.path.exists(manifest_path):
        try:
            with open(manifest_path, encoding="utf-8") as mf:
                mdata = json.load(mf)
            pb = mdata.get('parent_branch', '').strip()
            if pb and pb != 'main':
                parent_branch_raw = pb
        except (OSError, json.JSONDecodeError):
            pass

    # Fallback: report.md frontmatter
    if parent_branch_raw is None:
        report_path = os.path.join(dream_dir, 'report.md')
        if os.path.exists(report_path):
            with open(report_path, encoding="utf-8") as rf:
                rcontent = rf.read()
            fm_match = re.search(r'parent_branch:\s*["\']?([^"\'\n]+)', rcontent)
            if fm_match:
                pb = fm_match.group(1).strip()
                if pb and pb != 'main':
                    parent_branch_raw = pb

    if parent_branch_raw:
        # Extract dream_id from branch path (last /-separated segment)
        candidate_id = parent_branch_raw.split('/')[-1]
        resolved_did = resolve_parent_in_index(candidate_id, all_dream_ids)

    # Step 11: slug heuristic (only if step 10 didn't resolve anything)
    if resolved_did is None:
        parsed = parse_dream_id(did)
        if not parsed:
            return False
        _, slug = parsed
        suffix_match = COMPOUNDING_SUFFIXES.search(slug)
        if not suffix_match:
            return False
        base_slug = slug[:suffix_match.start()]

        # Find candidates: dream_ids whose slug starts with base_slug
        candidates: list[str] = []
        for other_did in all_dream_ids:
            if other_did == did:
                continue
            other_parsed = parse_dream_id(other_did)
            if not other_parsed:
                continue
            _, other_slug = other_parsed
            # Candidate if other slug starts with base_slug (prefix match)
            if other_slug.startswith(base_slug):
                candidates.append(other_did)

        if not candidates:
            return False

        # Sort by timestamp ascending, take earliest
        candidates.sort()

        if len(candidates) == 1:
            resolved_did = candidates[0]
        else:
            # Multiple candidates — check if they all share the exact base_slug
            # (i.e., only differ by their own suffix). If so, take earliest.
            exact_matches = [
                c for c in candidates
                if parse_dream_id(c) and parse_dream_id(c)[1] == base_slug
            ]
            if len(exact_matches) == 1:
                resolved_did = exact_matches[0]
            else:
                # Ambiguous
                print(
                    f'WARNING AMBIGUOUS: {did} could compound any of: '
                    + ', '.join(candidates),
                    file=sys.stderr,
                )
                return False

    if resolved_did is None:
        return False

    # Translate the resolved parent dream_id to its branch name (the canonical
    # parent-column form). The index row's branch is authoritative — it is
    # what dream-lineage.py looks up — even when the manifest's parent_branch
    # carried a slightly different timestamp.
    parent_branch = branch_by_dream_id.get(resolved_did)
    if not parent_branch:
        return False
    parts[6] = parent_branch
    print(
        f'INFO PARENT: {did} parent main -> {parent_branch}',
        file=sys.stderr,
    )
    return True


def main() -> int:
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--shadow-dir', default='.shadow',
                    help='Shadow root (default: .shadow)')
    args = ap.parse_args()

    dreams_dir = os.path.join(args.shadow_dir, '_dreams')
    index_path = os.path.join(dreams_dir, '_index.md')
    if not os.path.exists(index_path):
        print(f'ERROR: {index_path} not found', file=sys.stderr)
        return 1

    with open(index_path, encoding="utf-8") as f:
        lines = f.readlines()

    backup = index_path + '.bak'
    with open(backup, 'w', encoding="utf-8") as bf:
        bf.writelines(lines)

    corrupted = detect_corrupted(dreams_dir)
    repaired = 0
    parent_repairs = 0

    # Build list of all dream_ids + a dream_id->branch map for parent
    # resolution. The parent column is written as a branch name, so we
    # translate a resolved parent dream_id back to its row's branch.
    all_dream_ids: list[str] = []
    branch_by_dream_id: dict[str, str] = {}
    for line in lines:
        parts = [p.strip() for p in line.split('|')]
        if len(parts) < 8:
            continue
        did = parts[1]
        if not did or did.startswith('-') or did == 'dream_id':
            continue
        all_dream_ids.append(did)
        branch_by_dream_id[did] = parts[5]

    for i, line in enumerate(lines):
        parts = [p.strip() for p in line.split('|')]
        if len(parts) < 8:
            continue
        did = parts[1]
        if not did or did.startswith('-') or did == 'dream_id':
            continue
        if did in corrupted:
            continue
        result = repair_row(parts, dreams_dir)
        if result is None:
            continue
        new_parts, changed = result
        parent_changed = repair_parent(
            new_parts, dreams_dir, all_dream_ids, branch_by_dream_id
        )
        if parent_changed:
            parent_repairs += 1
        if changed or parent_changed:
            lines[i] = '| ' + ' | '.join(new_parts[1:-1]) + ' |\n'
            repaired += 1

    with open(index_path, 'w', encoding="utf-8") as f:
        f.writelines(lines)

    print(
        f'Repaired {repaired} rows ({parent_repairs} parent links); '
        f'backup at {backup}; {len(corrupted)} corrupted dream(s) skipped.'
    )
    return 0


if __name__ == '__main__':
    sys.exit(main())

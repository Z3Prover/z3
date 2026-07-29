#!/usr/bin/env python3
"""Dream reconciliation — merge dream branches into main's shadow.

Usage:
    python3 dream-reconcile.py [REPO_ROOT] [OPTIONS]
    python3 dream-reconcile.py --help

Options:
    --dry-run            Show what would be done without modifying files
    --verify-only        Only run post-reconciliation verification (checks
                         all dreams already in _index.md, not just unreconciled)
    --namespace NS       Override DREAM_NAMESPACE
    --cleanup-branches   Delete reconciled branches after verification.
                         REFUSES to run unless the reconciliation commit is
                         already on origin/<default-branch>. Run AFTER push.
    --help, -h           Show this help message

Steps (idempotent, safe to rerun):
    1. Discover new branches (namespace-filtered, not in _index.md)
    2. Read/validate manifests from remote branches
    3. Merge discoveries into main's per-file shadows (semantic dedup)
    4. Mirror reports, manifests, patches to main's _dreams/
    5. Update _dreams/_index.md
    6. Update _meta/state.json
    7. Rebuild top-level .shadow/_index.md (per-file discovery counts)
    8. Verify all artifacts present
    9. (Optional) Delete reconciled branches — only after push

Exits 0 on success, 1 on any verification failure.
"""

import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

# Shared safety gate for `rm -rf <worktree>`. Lives next to this script so
# bash callers (dream-cleanup.sh, dream-gc.sh) and this module share ONE
# source of truth for the "is this path safe to remove?" rules. Imported
# lazily inside _gc_worktree_after_merge() — top-level `from .` would fail
# when this script is run directly (no package context).

# --- Configuration ---

EXCLUDE_PATTERNS = re.compile(
    r'(^\.|/\.)'
    r'|\btest[s]?/'
    r'|\btest_'
    r'|_test\.'
    r'|\.lock$'
    r'|node_modules/'
    r'|vendor/'
    r'|dist/'
    r'|build/'
    r'|__pycache__'
    r'|\.min\.'
)

# Semantic-dedup thresholds. Word-overlap heuristics over short discoveries
# are notoriously lossy ("returns None on EXPIRED tokens" vs "...REVOKED tokens"
# share 5/6 words → 83% overlap). Use a tight threshold AND require a minimum
# length so 1-word differences in short claims aren't auto-merged.
DEDUP_THRESHOLD = 0.95
DEDUP_MIN_WORDS = 12

# Trust/strength orderings for metadata-merge on EXACT-text duplicates (B15).
# When two dreams independently record the SAME claim with different metadata,
# the stronger metadata must survive instead of being silently dropped. Only
# applied on exact-text matches — fuzzy matches stay skip-only.
SOURCE_TRUST = {'exploration': 1, 'interaction': 2, 'user': 3}

# Language detection for reconciler-created shadows. Mirrors
# shadow-init.py's EXTENSION_TO_LANG / BASENAME_TO_LANG so files bootstrapped
# during reconciliation carry the same canonical `**Language**:` header as
# init-created files.
EXTENSION_TO_LANG = {
    ".py": "Python",
    ".js": "JavaScript", ".jsx": "JavaScript",
    ".mjs": "JavaScript", ".cjs": "JavaScript",
    ".ts": "TypeScript", ".tsx": "TypeScript",
    ".java": "Java",
    ".kt": "Kotlin", ".kts": "Kotlin",
    ".scala": "Scala",
    ".go": "Go",
    ".rs": "Rust",
    ".rb": "Ruby",
    ".c": "C", ".h": "C",
    ".cpp": "C++", ".hpp": "C++", ".cc": "C++",
    ".hh": "C++", ".cxx": "C++", ".hxx": "C++",
    ".cs": "C#",
    ".php": "PHP",
    ".sh": "Shell", ".bash": "Shell", ".zsh": "Shell",
    ".swift": "Swift",
    ".yaml": "YAML", ".yml": "YAML",
    ".toml": "TOML",
    ".json": "JSON",
}
BASENAME_TO_LANG = {
    "Makefile": "Makefile",
    "Dockerfile": "Dockerfile",
    "Containerfile": "Dockerfile",
    "Rakefile": "Ruby",
    "Gemfile": "Ruby",
}


def _detect_language(rel_path):
    """Detect language from a source path, mirroring shadow-init.py."""
    base = os.path.basename(rel_path)
    if base in BASENAME_TO_LANG:
        return BASENAME_TO_LANG[base]
    _, ext = os.path.splitext(base)
    return EXTENSION_TO_LANG.get(ext.lower(), "Unknown")


def _source_rel_from_shadow(shadow_path):
    """Derive the source path (e.g. src/foo.py) from a shadow path."""
    norm = shadow_path.replace(os.sep, '/')
    marker = '/.shadow/'
    idx = norm.rfind(marker)
    rel = norm[idx + len(marker):] if idx >= 0 else os.path.basename(norm)
    if rel.endswith('.md'):
        rel = rel[:-3]
    return rel


def _canonical_header_lines(shadow_path):
    """Return canonical per-file shadow header lines.

    Mirrors shadow-init.py's per-file template (`# Shadow: <path>`,
    `**Language**: <lang>`, `## File-Level`) so reconciler-created shadows
    match init-created ones. Without this, downstream tools read `Unknown`
    for the index Language column and `--check-invariants` flags the file
    as missing its metadata block.
    """
    rel = _source_rel_from_shadow(shadow_path)
    lang = _detect_language(rel)
    return [
        f'# Shadow: {rel}\n', '\n',
        f'**Language**: {lang}\n', '\n',
        '## File-Level\n', '\n', '_No discoveries yet._\n', '\n',
    ]


# --- Git helpers ---

def git(*args, cwd=None, check=True):
    """Run a git command and return stdout."""
    result = subprocess.run(
        ['git'] + list(args),
        capture_output=True, text=True, cwd=cwd, encoding="utf-8"
    )
    if check and result.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout.strip()


def git_show(ref, path, cwd=None):
    """Read a file from a git ref. Returns None if not found."""
    result = subprocess.run(
        ['git', 'show', f'{ref}:{path}'],
        capture_output=True, text=True, cwd=cwd, encoding="utf-8"
    )
    if result.returncode != 0:
        return None
    return result.stdout


# --- Step 1: Discover branches ---

def discover_branches(repo_root, dream_ns):
    """Find dream branches not yet in _index.md."""
    # Get all remote dream branches for this namespace.
    # Use startswith on the short branch name to avoid false positives from
    # any ref that merely contains "dream/<ns>/" as a substring.
    raw = git('branch', '-r', '--format=%(refname:short)', cwd=repo_root)
    prefix = f'dream/{dream_ns}/'
    all_branches = []
    for b in raw.split('\n'):
        b = b.strip()
        if not b:
            continue
        short = b[len('origin/'):] if b.startswith('origin/') else b
        if short.startswith(prefix):
            all_branches.append(short)

    existing_ids = _read_indexed_dream_ids(repo_root)

    # Filter to new branches (dream_id not in index)
    new_branches = []
    for branch in all_branches:
        # Extract dream_id from branch name (everything after the prefix)
        dream_id = branch[len(prefix):]
        if dream_id and dream_id not in existing_ids:
            new_branches.append((branch, dream_id))

    return new_branches


def _read_indexed_dream_ids(repo_root):
    """Return the set of dream_ids already present in _index.md."""
    index_path = os.path.join(repo_root, '.shadow', '_dreams', '_index.md')
    existing = set()
    if not os.path.isfile(index_path):
        return existing
    with open(index_path, encoding="utf-8") as f:
        for line in f:
            if line.startswith('|') and not line.startswith('| dream_id') and not line.startswith('|---'):
                parts = [p.strip() for p in line.split('|')]
                if len(parts) > 1 and parts[1]:
                    existing.add(parts[1])
    return existing


def _read_indexed_branches(repo_root):
    """Return list of (branch, dream_id) tuples from _index.md (column 5)."""
    index_path = os.path.join(repo_root, '.shadow', '_dreams', '_index.md')
    rows = []
    if not os.path.isfile(index_path):
        return rows
    with open(index_path, encoding="utf-8") as f:
        for line in f:
            if line.startswith('|') and not line.startswith('| dream_id') and not line.startswith('|---'):
                parts = [p.strip() for p in line.split('|')]
                # Leading '|' creates an empty parts[0]; columns start at parts[1].
                if len(parts) >= 6 and parts[1]:
                    dream_id = parts[1]
                    branch = parts[5]
                    if branch:
                        rows.append((branch, dream_id))
    return rows


# --- Step 2: Read/validate manifests ---

def load_manifests(repo_root, branches):
    """Read and validate manifests from remote branches."""
    manifests = []
    skipped = []

    for branch, dream_id in branches:
        manifest_path = f'.shadow/_dreams/{dream_id}/manifest.json'
        raw = git_show(f'origin/{branch}', manifest_path, cwd=repo_root)

        if not raw:
            skipped.append((branch, dream_id, "no manifest found"))
            continue

        try:
            manifest = json.loads(raw)
        except json.JSONDecodeError as e:
            skipped.append((branch, dream_id, f"invalid JSON: {e}"))
            continue

        # Validate dream_id consistency
        m_did = manifest.get('dream_id', '')
        if m_did != dream_id:
            skipped.append((branch, dream_id, f"dream_id mismatch: {m_did}"))
            continue

        # Validate required fields
        if not manifest.get('category') or not manifest.get('verdict'):
            skipped.append((branch, dream_id, "missing category or verdict"))
            continue

        manifests.append((branch, dream_id, manifest))

    return manifests, skipped


# --- Step 3: Semantic merge ---

def find_heading(lines, symbol):
    """Find the line index of a heading matching the symbol (bare or backtick-wrapped)."""
    patterns = [
        f'## `{symbol}`',
        f'### `{symbol}`',
        f'## {symbol}',
        f'### {symbol}',
    ]
    for i, line in enumerate(lines):
        stripped = line.rstrip()
        for pat in patterns:
            if stripped == pat:
                return i
    return -1


def find_cross_references_heading(lines):
    """Find the ## Cross-References heading.

    Case-insensitive: meditate/user rewrites that lowercase the heading
    must still be detected, otherwise `_ensure_cross_references_section`
    appends a duplicate section and back-pointer dedup misses entirely.
    """
    for i, line in enumerate(lines):
        if line.strip().lower() == '## cross-references':
            return i
    return -1


def is_duplicate_discovery(existing_lines, new_text):
    """Check if a discovery with similar text already exists.

    Uses word-overlap (Jaccard-ish, scaled by the new text). Tight
    threshold (DEDUP_THRESHOLD) and a minimum length (DEDUP_MIN_WORDS) avoid
    falsely merging short discoveries that differ by a single keyword
    (e.g., "expired" vs "revoked"). Exact-match (after whitespace
    normalization) is always treated as duplicate regardless of length.
    """
    normalized_new = re.sub(r'\s+', ' ', new_text.lower().strip())
    new_words = normalized_new.split()
    if not new_words:
        return False

    for line in existing_lines:
        if not line.startswith('- '):
            continue
        normalized_existing = re.sub(r'\s+', ' ', line[2:].lower().strip())

        # Exact-match short-circuit (independent of word count).
        if normalized_existing == normalized_new:
            return True

        existing_words = normalized_existing.split()
        # Skip the fuzzy heuristic for short discoveries — it has high false
        # positive rate on 1-word differences (5/6 ≈ 83% but distinct meaning).
        if len(new_words) < DEDUP_MIN_WORDS or len(existing_words) < DEDUP_MIN_WORDS:
            continue

        new_set = set(new_words)
        existing_set = set(existing_words)
        overlap = len(new_set & existing_set) / len(new_set)
        if overlap >= DEDUP_THRESHOLD:
            return True
    return False


def _ensure_cross_references_section(lines):
    """Append a ## Cross-References section if missing. Returns updated lines."""
    if find_cross_references_heading(lines) >= 0:
        return lines
    # Ensure trailing newline before adding section
    if lines and not lines[-1].endswith('\n'):
        lines[-1] = lines[-1] + '\n'
    if lines and lines[-1].strip():
        lines.append('\n')
    lines.extend(['## Cross-References\n', '\n', '_No cross-cutting discoveries yet._\n'])
    return lines


def _find_exact_discovery_index(section_lines, new_text):
    """Return the index (within section_lines) of a `- ` discovery line whose
    text EXACTLY matches new_text (whitespace/case normalized), else -1.

    Exact match is the only case eligible for metadata-merge — the fuzzy
    overlap heuristic is too lossy to trust for silently rewriting metadata.
    """
    normalized_new = re.sub(r'\s+', ' ', new_text.lower().strip())
    if not normalized_new:
        return -1
    for i, line in enumerate(section_lines):
        if not line.startswith('- '):
            continue
        if re.sub(r'\s+', ' ', line[2:].lower().strip()) == normalized_new:
            return i
    return -1


def _parse_meta_line(meta_line):
    """Parse a `  _(<status>, source: <src>[, labels: [..]])_` line.

    Returns (status, source, labels) or None if the line isn't a metadata
    line in the canonical shape.
    """
    m = re.match(r'\s*_\((.*)\)_\s*$', meta_line.rstrip('\n'))
    if not m:
        return None
    inner = m.group(1)
    sm = re.search(r'\b(verified|uncertain|refuted)\b', inner)
    status = sm.group(1) if sm else None
    src_m = re.search(r'source:\s*([A-Za-z]+)', inner)
    source = src_m.group(1) if src_m else None
    lbl_m = re.search(r'labels:\s*\[([^\]]*)\]', inner)
    labels = []
    if lbl_m:
        labels = [l.strip() for l in lbl_m.group(1).split(',') if l.strip()]
    if status is None or source is None:
        return None
    return status, source, labels


def _merge_meta(existing, new_status, new_source, new_labels):
    """Compute the upgraded (status, source, labels) for an exact-text dup.

    Rules (B15): union labels; upgrade source to the higher-trust value;
    upgrade `uncertain`->`verified`; NEVER silently change to/from `refuted`
    (status conflicts are meditate's job). Returns (status, source, labels,
    changed).
    """
    e_status, e_source, e_labels = existing

    status = e_status
    if e_status != 'refuted' and new_status != 'refuted':
        if e_status == 'uncertain' and new_status == 'verified':
            status = 'verified'

    source = e_source
    if SOURCE_TRUST.get(new_source, 0) > SOURCE_TRUST.get(e_source, 0):
        source = new_source

    labels = list(e_labels)
    for l in new_labels:
        if l not in labels:
            labels.append(l)

    changed = (status != e_status or source != e_source or labels != e_labels)
    return status, source, labels, changed


def _format_meta_line(status, source, labels):
    parts = [status, f'source: {source}']
    if labels:
        parts.append(f"labels: [{', '.join(labels)}]")
    return f'  _({", ".join(parts)})_\n'


def merge_discovery_into_file(shadow_path, anchor_symbol, discovery, dream_id):
    """Merge a single discovery into a shadow file. Returns True if written."""
    text = discovery.get('text', '').strip()
    if not text:
        return False

    status = discovery.get('status', 'verified')
    source = discovery.get('source', 'exploration')
    labels = discovery.get('labels', [])
    also_involves = discovery.get('also_involves', [])

    # Build the discovery line
    meta_parts = [status, f'source: {source}']
    if labels:
        meta_parts.append(f"labels: [{', '.join(labels)}]")
    meta_line = f'  _({", ".join(meta_parts)})_'

    lines_to_add = [f'- {text}\n', f'{meta_line}\n']
    if also_involves:
        refs = ', '.join(f'`{r}`' for r in also_involves)
        lines_to_add.append(f'  Also involves: {refs}\n')
    lines_to_add.append(f'  Dream report: `_dreams/{dream_id}/`\n')

    # Read or create shadow file
    new_file = not os.path.isfile(shadow_path)
    if new_file:
        # Bootstrap with the canonical layout: file header + File-Level
        # section + symbol heading + Cross-References footer, matching
        # shadow-init.py's per-file template.
        os.makedirs(os.path.dirname(shadow_path), exist_ok=True)
        lines = _canonical_header_lines(shadow_path) + [
            f'## `{anchor_symbol}`\n', '\n',
            '## Cross-References\n', '\n', '_No cross-cutting discoveries yet._\n',
        ]
    else:
        with open(shadow_path, encoding="utf-8") as f:
            lines = f.readlines()
        lines = _ensure_cross_references_section(lines)

    # Check for duplicate
    heading_idx = find_heading(lines, anchor_symbol)
    if heading_idx >= 0:
        # Find the section content (until next heading or end)
        section_end = len(lines)
        for i in range(heading_idx + 1, len(lines)):
            if lines[i].startswith('## ') or lines[i].startswith('### '):
                section_end = i
                break
        section_lines = lines[heading_idx:section_end]

        # Exact-text duplicate: don't drop the new discovery's metadata —
        # merge it into the existing line (union labels, upgrade source trust,
        # upgrade uncertain->verified; never touch refuted). B15.
        exact_rel = _find_exact_discovery_index(section_lines, text)
        if exact_rel >= 0:
            text_idx = heading_idx + exact_rel
            meta_idx = text_idx + 1
            if meta_idx < section_end:
                existing_meta = _parse_meta_line(lines[meta_idx])
            else:
                existing_meta = None
            if existing_meta is None:
                # No canonical metadata line to upgrade — nothing safe to do.
                return False
            merged = _merge_meta(existing_meta, status, source, labels)
            m_status, m_source, m_labels, changed = merged
            if not changed:
                return False
            lines[meta_idx] = _format_meta_line(m_status, m_source, m_labels)
            with open(shadow_path, 'w', encoding="utf-8") as f:
                f.writelines(lines)
            return True

        # Fuzzy near-duplicate: skip (heuristic too lossy to merge metadata).
        if is_duplicate_discovery(section_lines, text):
            return False

        # Remove placeholder if present
        for i in range(heading_idx + 1, section_end):
            if '_No discoveries yet._' in lines[i]:
                lines[i] = ''
                break

        # Insert discovery before next heading or cross-references
        insert_at = section_end
        lines[insert_at:insert_at] = ['\n'] + lines_to_add
    else:
        # Create heading before Cross-References (or at end)
        xref_idx = find_cross_references_heading(lines)
        if xref_idx >= 0:
            insert_at = xref_idx
        else:
            insert_at = len(lines)

        new_section = ['\n', f'## `{anchor_symbol}`\n', '\n'] + lines_to_add
        lines[insert_at:insert_at] = new_section

    with open(shadow_path, 'w', encoding="utf-8") as f:
        f.writelines(lines)

    return True


def add_cross_reference_backpointer(repo_root, file_part, slug, title, dream_id):
    """Add a back-pointer to per-file shadow's ## Cross-References section.

    Required by the bidirectional-reference invariant: every entry in
    `_cross/<slug>.md` must have a matching entry in each referenced file's
    ## Cross-References section. Idempotent (skips if back-pointer exists).
    """
    shadow_path = os.path.join(repo_root, '.shadow', file_part + '.md')
    # Relative link from .shadow/<file_part>.md back up to .shadow/_cross/<slug>.md.
    # For a top-level file (no slashes) the prefix is empty; each directory of
    # depth adds one "../". Otherwise the markdown link is broken and the
    # bidirectional-reference invariant fails on any subdir shadow.
    depth = file_part.count('/')
    prefix = '../' * depth
    backpointer = f'- [{title}]({prefix}_cross/{slug}.md) (dream: {dream_id})'

    if os.path.isfile(shadow_path):
        with open(shadow_path, encoding="utf-8") as f:
            lines = f.readlines()
    else:
        # Create a minimal shadow file with the canonical header + footer if
        # the cross-reference predates per-file analysis. The specific symbols
        # are unknown here, so the `## File-Level` section (which
        # _canonical_header_lines emits) holds file-scope content.
        os.makedirs(os.path.dirname(shadow_path), exist_ok=True)
        lines = _canonical_header_lines(shadow_path) + [
            '## Cross-References\n', '\n', '_No cross-cutting discoveries yet._\n',
        ]

    lines = _ensure_cross_references_section(lines)

    # Idempotency: only treat as "already present" when the line contains
    # the actual markdown link target — `](<prefix>_cross/<slug>.md)`.
    # Substring matching on `_cross/{slug}.md` false-positives on any
    # discovery body that mentions the slug (e.g. an `Also involves:` ref
    # like `\`_cross/db-lifecycle.md::section\``), silently swallowing the
    # legitimate back-pointer add.
    link_marker = f']({prefix}_cross/{slug}.md)'
    if any(link_marker in line for line in lines):
        with open(shadow_path, 'w', encoding="utf-8") as f:
            f.writelines(lines)
        return False

    xref_idx = find_cross_references_heading(lines)
    # Find end of Cross-References section
    section_end = len(lines)
    for i in range(xref_idx + 1, len(lines)):
        if lines[i].startswith('## ') or lines[i].startswith('### '):
            section_end = i
            break

    # Replace the empty placeholder if present, else append.
    placeholder_idx = -1
    for i in range(xref_idx + 1, section_end):
        if '_No cross-cutting discoveries yet._' in lines[i]:
            placeholder_idx = i
            break

    if placeholder_idx >= 0:
        lines[placeholder_idx] = f'{backpointer}\n'
    else:
        # Insert before the next heading (or at section_end)
        insert_at = section_end
        # Trim trailing blank lines inside the section
        while insert_at > xref_idx + 1 and lines[insert_at - 1].strip() == '':
            insert_at -= 1
        lines[insert_at:insert_at] = [f'{backpointer}\n']

    with open(shadow_path, 'w', encoding="utf-8") as f:
        f.writelines(lines)
    return True


def _merge_refs_into_cross_file(cross_path, new_refs):
    """Union new refs into an existing _cross/<slug>.md **Refs**: section.

    When two dreams use the same cross-cutting slug, the later one must not
    silently drop its refs: per-file back-pointers are still added pointing
    at this cross file (below), so its **Refs**: block must list them or the
    bidirectional-reference invariant breaks. Returns True if modified.
    """
    try:
        with open(cross_path, encoding="utf-8") as f:
            content = f.read()
    except OSError:
        return False
    lines = content.split('\n')
    refs_idx = None
    for i, line in enumerate(lines):
        if line.strip().lower().startswith('**refs**:'):
            refs_idx = i
            break
    if refs_idx is None:
        return False
    block_end = refs_idx + 1
    existing = set()
    while block_end < len(lines):
        m = re.match(r'-\s*`([^`]+)`', lines[block_end].strip())
        if m:
            existing.add(m.group(1))
            block_end += 1
        else:
            break
    to_add = [r for r in new_refs if r and r not in existing]
    if not to_add:
        return False
    lines[block_end:block_end] = [f'- `{r}`' for r in to_add]
    with open(cross_path, 'w', encoding="utf-8") as f:
        f.write('\n'.join(lines))
    return True


def merge_discoveries(repo_root, manifests, dry_run=False):
    """Merge all discoveries from manifests into main's shadow files."""
    merged_count = 0
    skipped_count = 0

    for branch, dream_id, manifest in manifests:
        discoveries = manifest.get('discoveries', [])
        for disc in discoveries:
            # Normalize string discoveries to dicts
            if isinstance(disc, str):
                disc = {'anchor': '', 'text': disc}
            anchor = disc.get('anchor', '')
            if '::' not in anchor:
                skipped_count += 1
                continue

            file_part, symbol = anchor.split('::', 1)
            shadow_path = os.path.join(repo_root, '.shadow', file_part + '.md')

            if dry_run:
                print(f"  Would merge: {anchor} <- {disc.get('text', '')[:60]}")
                merged_count += 1
                continue

            # Ensure shadow directory exists
            os.makedirs(os.path.dirname(shadow_path), exist_ok=True)

            if merge_discovery_into_file(shadow_path, symbol, disc, dream_id):
                merged_count += 1
            else:
                skipped_count += 1

        # Handle cross-cutting discoveries
        cross_cutting = manifest.get('cross_cutting', [])
        for cross in cross_cutting:
            # Normalize string entries to dicts
            if isinstance(cross, str):
                cross = {'slug': re.sub(r'[^a-z0-9]+', '-', cross[:60].lower()).strip('-'), 'description': cross}
            slug = cross.get('slug', '')
            if not slug:
                continue

            cross_path = os.path.join(repo_root, '.shadow', '_cross', f'{slug}.md')
            refs = cross.get('refs', []) or []
            title = cross.get('title', slug)

            if dry_run:
                print(f"  Would create cross-cutting: _cross/{slug}.md")
                for ref in refs:
                    if '::' in ref:
                        file_part = ref.split('::', 1)[0]
                        print(f"    + back-pointer in .shadow/{file_part}.md")
                merged_count += 1
                continue

            if not os.path.isfile(cross_path):
                os.makedirs(os.path.dirname(cross_path), exist_ok=True)
                refs_str = '\n'.join(f'- `{r}`' for r in refs)
                content = (
                    f"# {title}\n\n"
                    f"**Category**: {cross.get('category', 'behavior')}\n"
                    f"**Refs**:\n{refs_str}\n\n"
                    f"**Discovery**: {cross.get('text', '')}\n\n"
                    f"_({cross.get('status', 'verified')}, "
                    f"source: {cross.get('source', 'exploration')})_\n"
                )
                with open(cross_path, 'w', encoding="utf-8") as f:
                    f.write(content)
                merged_count += 1
            else:
                # Cross file already exists (e.g. a prior dream used the same
                # slug). Union our refs into its **Refs**: block so it stays
                # consistent with the back-pointers added below.
                if _merge_refs_into_cross_file(cross_path, refs):
                    merged_count += 1
                else:
                    skipped_count += 1

            # Maintain bidirectional invariant: add a back-pointer in each
            # referenced per-file shadow's ## Cross-References section.
            # We do this even when the cross-cutting file already exists, so
            # that re-runs heal any missing back-pointers.
            for ref in refs:
                if '::' not in ref:
                    continue
                file_part = ref.split('::', 1)[0]
                try:
                    add_cross_reference_backpointer(
                        repo_root, file_part, slug, title, dream_id
                    )
                except OSError as e:
                    print(f"  ⚠️  Could not write back-pointer for {file_part}: {e}")

    return merged_count, skipped_count


# --- Step 4: Mirror reports ---

def mirror_reports(repo_root, manifests, dry_run=False):
    """Copy report.md, manifest.json, patch.diff from branches to main."""
    mirrored = 0
    corrupted = []

    for branch, dream_id, manifest in manifests:
        dream_dir = os.path.join(repo_root, '.shadow', '_dreams', dream_id)

        if dry_run:
            print(f"  Would mirror: {dream_id}/")
            mirrored += 1
            continue

        os.makedirs(dream_dir, exist_ok=True)

        # Read report and check for corruption
        report = git_show(f'origin/{branch}', f'.shadow/_dreams/{dream_id}/report.md', cwd=repo_root)
        if report:
            # Verify report dream_id matches
            m = re.match(r'^\ufeff?\s*---\r?\n(.*?)\r?\n---', report, re.S)
            report_corrupt = False
            if m:
                dm = re.search(r'^dream_id:\s*["\']?(.+?)["\']?\s*$', m.group(1), re.M)
                report_did = dm.group(1).strip() if dm else ''
                if report_did and report_did != dream_id:
                    corrupted.append((dream_id, report_did))
                    report_corrupt = True
                    # Write placeholder for the report only — the manifest
                    # and patch below are still mirrored unconditionally so a
                    # single bad frontmatter line never discards valid
                    # artifacts (discoveries are read from the manifest).
                    with open(os.path.join(dream_dir, 'report.md'), 'w', encoding="utf-8") as f:
                        f.write(f"# Corrupted Report\n\nContained content from {report_did}.\n"
                                f"Original on branch: {branch}\n")

            if not report_corrupt:
                with open(os.path.join(dream_dir, 'report.md'), 'w', encoding="utf-8") as f:
                    f.write(report)

        # Mirror manifest
        with open(os.path.join(dream_dir, 'manifest.json'), 'w', encoding="utf-8") as f:
            json.dump(manifest, f, indent=2)

        # Mirror patch
        #
        # Use `is not None` (not a truthy check): git_show returns None when
        # the file is absent on the ref, and "" when the file exists but is
        # 0 bytes. Truthy collapses both into "skip", which loses information
        # — a legitimately empty patch.diff on the dream branch would never
        # be mirrored to main, and verify_artifacts then reports the dream as
        # `missing patch.diff` even though it exists on origin. Always
        # mirror the file when the ref had one (even if empty); skip the
        # write only when truly absent.
        patch = git_show(f'origin/{branch}', f'.shadow/_dreams/{dream_id}/patch.diff', cwd=repo_root)
        if patch is not None:
            with open(os.path.join(dream_dir, 'patch.diff'), 'w', encoding="utf-8") as f:
                f.write(patch)

        mirrored += 1

    return mirrored, corrupted


# --- Step 5: Update index ---

def _resolve_tip_commit(repo_root, branch):
    """Return the short SHA for origin/<branch>, or 'unknown' on failure.

    Avoids writing empty/garbage values into _index.md when the ref is
    pruned, the network is down, or git is otherwise unhappy. Uses git's
    own short-SHA length (git auto-extends past 7 when 7 would be
    ambiguous) instead of truncating, so the stored value always resolves
    uniquely. Validates that the result looks like a hex SHA.
    """
    raw = git('rev-parse', '--short', f'origin/{branch}',
              cwd=repo_root, check=False)
    candidate = raw.strip().split('\n', 1)[0] if raw else ''
    if candidate and re.fullmatch(r'[0-9a-fA-F]{7,40}', candidate):
        return candidate
    return 'unknown'


def update_index(repo_root, manifests, dry_run=False):
    """Add entries to _dreams/_index.md for reconciled branches."""
    index_path = os.path.join(repo_root, '.shadow', '_dreams', '_index.md')

    if dry_run:
        for branch, dream_id, manifest in manifests:
            print(f"  Would index: {dream_id}")
        return

    # Bootstrap if missing (skipped on dry-run so the directory tree
    # stays clean — dry-run must not mutate disk).
    if not os.path.isfile(index_path):
        os.makedirs(os.path.dirname(index_path), exist_ok=True)
        with open(index_path, 'w', encoding="utf-8") as f:
            f.write('# Dream Experiment Archive\n\n'
                    '| dream_id | category | verdict | title | branch | parent | tip_commit |\n'
                    '|----------|----------|---------|-------|--------|--------|------------|\n')

    with open(index_path, 'a', encoding="utf-8") as f:
        for branch, dream_id, manifest in manifests:
            tip = _resolve_tip_commit(repo_root, branch)
            cat = re.sub(r'\s*\(.*\)\s*$', '', manifest.get('category', 'unknown').lower().strip())
            verdict = manifest.get('verdict', 'unknown').lower().strip()
            parent = manifest.get('parent_branch', 'main').strip()

            # Get title from manifest or report heading
            title = manifest.get('title', '')
            if not title:
                report = git_show(f'origin/{branch}',
                                  f'.shadow/_dreams/{dream_id}/report.md', cwd=repo_root)
                if report:
                    fm_end = report.find('---', report.find('---') + 3)
                    body = report[fm_end + 3:] if fm_end > 0 else report
                    m = re.search(r'^#\s+(.+)', body, re.M)
                    title = m.group(1).strip() if m else ''
            if not title:
                title = f'Dream {dream_id}'
            title = title.replace('|', '-').replace('\n', ' ')[:120]

            f.write(f'| {dream_id} | {cat} | {verdict} | {title} | {branch} | {parent} | {tip} |\n')


# --- Shared: discovery counting ---

def _count_discoveries(shadow_path):
    """Count per-file discoveries in a shadow file.

    Bullets inside `## Cross-References` are back-pointer links to
    `_cross/*.md`, not discoveries — exclude them. Heading lookahead is
    case-insensitive so meditate/user-rewritten lowercase headings still
    delimit the section correctly (matches `find_cross_references_heading`).
    """
    if not os.path.isfile(shadow_path):
        return 0
    count = 0
    with open(shadow_path, encoding="utf-8") as sf:
        in_xref = False
        for line in sf:
            stripped = line.rstrip()
            if stripped.lower().startswith('## cross-references'):
                in_xref = True
                continue
            if stripped.startswith('## ') or stripped.startswith('### '):
                in_xref = False
                continue
            if not in_xref and line.startswith('- '):
                count += 1
    return count


# --- Step 6: Update state.json ---

def update_state(repo_root, manifests, dry_run=False):
    """Update _meta/state.json with dream reconciliation metadata."""
    state_path = os.path.join(repo_root, '.shadow', '_meta', 'state.json')

    if not os.path.isfile(state_path):
        if dry_run:
            print("  Would create state.json")
            return
        os.makedirs(os.path.dirname(state_path), exist_ok=True)
        state = {
            'version': 1,
            'initialized_at': datetime.now(timezone.utc).isoformat(),
            'total_files': 0,
            'total_symbols': 0,
            'total_discoveries': 0,
            'dream_cycles_completed': 0,
        }
    else:
        with open(state_path, encoding="utf-8") as f:
            state = json.load(f)

    if dry_run:
        print("  Would update state.json")
        return

    # Recount discoveries
    total_discoveries = 0
    total_files = 0
    total_symbols = 0
    shadow_dir = os.path.join(repo_root, '.shadow')

    for root, dirs, files in os.walk(shadow_dir):
        # Prune `_*` internal directories (_meta, _cross, _dreams) in-place
        # so os.walk never descends into them. Without this, large _dreams/
        # archives are walked on every reconcile for no benefit. Internal dirs
        # only exist at the top level, so prune there only — deeper `_`-prefixed
        # source dirs (e.g. src/_internal/) are real shadows and must be counted.
        if root == shadow_dir:
            dirs[:] = [d for d in dirs if not d.startswith('_')]

        for fname in files:
            if not fname.endswith('.md'):
                continue
            filepath = os.path.join(root, fname)
            rel_path = os.path.relpath(filepath, shadow_dir)
            if rel_path.startswith('_'):
                continue

            total_files += 1
            with open(filepath, encoding="utf-8") as f:
                # `## Cross-References` and `## File-Level` are structural
                # sections, not symbols. Bullets inside `## Cross-References`
                # are back-pointer links to `_cross/*.md`, not discoveries.
                in_xref = False
                for line in f:
                    stripped = line.rstrip()
                    if stripped.startswith('## ') or stripped.startswith('### '):
                        prefix_len = 4 if stripped.startswith('### ') else 3
                        heading_text = stripped[prefix_len:].strip().strip('`').strip()
                        if heading_text.lower() == 'cross-references':
                            in_xref = True
                            continue
                        in_xref = False
                        if heading_text == 'File-Level':
                            continue
                        total_symbols += 1
                        continue
                    if not in_xref and line.startswith('- '):
                        total_discoveries += 1

    state['last_update_at'] = datetime.now(timezone.utc).isoformat()
    state['last_update_type'] = 'dream'
    state['total_files'] = total_files
    state['total_symbols'] = total_symbols
    state['total_discoveries'] = total_discoveries
    state['dream_cycles_completed'] = state.get('dream_cycles_completed', 0) + 1

    # Record last commit
    try:
        state['last_commit'] = git('rev-parse', 'HEAD', cwd=repo_root)
    except RuntimeError:
        pass

    with open(state_path, 'w', encoding="utf-8") as f:
        json.dump(state, f, indent=2)


# --- Step 7: Rebuild top-level _index.md ---

# Container kinds whose heading text gets a `<kind> Name` prefix (per
# shadow-init.py's Symbol.heading_text). We strip the prefix to surface the
# bare class/interface name in the index table.
_HEADING_KIND_PREFIXES = (
    'class ', 'interface ', 'enum ', 'trait ',
    'struct ', 'protocol ', 'module ',
)


def _shadow_symbol_names(shadow_path):
    """Extract top-level symbol names from a shadow file.

    Returns names from `## `name`` headings, skipping the structural
    `## Cross-References` and `## File-Level` sections. Nested `###`
    headings (e.g. methods inside a class) are NOT counted here — the
    top-level index row lists only top-level symbols (matching
    shadow-init.py's `build_index`, which iterates symbols with no parent).
    """
    names = []
    if not os.path.isfile(shadow_path):
        return names
    with open(shadow_path, encoding="utf-8") as sf:
        for line in sf:
            stripped = line.rstrip()
            if not stripped.startswith('## '):
                continue
            heading_text = stripped[3:].strip().strip('`').strip()
            lower = heading_text.lower()
            if lower == 'cross-references' or lower == 'file-level':
                continue
            for kw in _HEADING_KIND_PREFIXES:
                if heading_text.startswith(kw):
                    heading_text = heading_text[len(kw):].strip()
                    break
            if heading_text:
                names.append(heading_text)
    return names


def _shadow_language(shadow_path):
    """Read the `**Language**:` field from a shadow file header.

    Returns 'Unknown' if the header line is missing (e.g. a shadow created
    on-the-fly by `add_cross_reference_backpointer` without metadata).
    Avoids re-implementing shadow-init's extension map here.
    """
    if not os.path.isfile(shadow_path):
        return 'Unknown'
    with open(shadow_path, encoding="utf-8") as sf:
        for i, line in enumerate(sf):
            if i > 10:
                break
            m = re.match(r'\*\*Language\*\*:\s*([^|]+?)\s*(\||$)', line.rstrip())
            if m:
                return m.group(1).strip() or 'Unknown'
    return 'Unknown'


def rebuild_top_index(repo_root, dry_run=False):
    """Regenerate `.shadow/_index.md` from current per-file shadow state.

    `update_state` (Step 6) already refreshes state.json totals, but the
    top-level `_index.md` table — per-file symbol/discovery counts the
    viewer and hooks rely on — is otherwise frozen at init time and goes
    stale after every dream reconcile. This step is the missing companion
    to `update_state`: it walks `.shadow/` (excluding `_*` internal dirs),
    re-counts per-file discoveries via `_count_discoveries`, and rewrites
    the table.

    Bootstraps a fresh `_index.md` if the file doesn't exist. Preserves
    the original `> Generated by shadow-frog-init on <date>` line as
    `> Initially generated by shadow-frog-init on <date>` when found so the
    init provenance survives reconciler rewrites. Honors `dry_run`.
    """
    shadow_dir = os.path.join(repo_root, '.shadow')
    index_path = os.path.join(shadow_dir, '_index.md')

    if dry_run:
        print("  Would regenerate _index.md")
        return

    if not os.path.isdir(shadow_dir):
        print("  No .shadow/ directory — skipping _index.md")
        return

    # Salvage the original init date from any pre-existing index so we don't
    # lose the "first seen" provenance when reconciler rewrites the header.
    original_init_date = None
    if os.path.isfile(index_path):
        try:
            with open(index_path, encoding="utf-8") as f:
                for line in f:
                    m = re.match(
                        r'>\s*(?:Initially g|G)enerated by shadow-frog-init on (\S+)',
                        line,
                    )
                    if m:
                        original_init_date = m.group(1).strip()
                        break
        except OSError:
            pass

    rows = []  # (rel_source_path, language, names, sym_count, disc_count)
    total_symbols = 0
    total_discoveries = 0

    for root, dirs, files in os.walk(shadow_dir):
        # Prune `_*` internal directories so we never descend into `_meta`,
        # `_cross`, `_dreams`, etc. These only exist at the top level, so prune
        # there only — deeper `_`-prefixed source dirs (e.g. src/_internal/) are
        # real mirrored shadows and belong in the index. Mutating `dirs`
        # in-place is the documented `os.walk` way to skip subtrees.
        if root == shadow_dir:
            dirs[:] = sorted(d for d in dirs if not d.startswith('_'))
        else:
            dirs[:] = sorted(dirs)

        for fname in sorted(files):
            if not fname.endswith('.md'):
                continue
            if fname.startswith('_'):
                continue
            shadow_path = os.path.join(root, fname)
            rel_shadow = os.path.relpath(shadow_path, shadow_dir)
            # The shadow path mirrors the source path with `.md` appended.
            source_path = rel_shadow[:-3]

            language = _shadow_language(shadow_path)
            names = _shadow_symbol_names(shadow_path)
            sym_count = len(names)
            disc_count = _count_discoveries(shadow_path)

            total_symbols += sym_count
            total_discoveries += disc_count
            rows.append((source_path, language, names, sym_count, disc_count))

    rows.sort(key=lambda r: r[0])

    cross_dir = os.path.join(shadow_dir, '_cross')
    cross_count = 0
    if os.path.isdir(cross_dir):
        try:
            cross_count = sum(
                1 for f in os.listdir(cross_dir)
                if f.endswith('.md') and not f.startswith('_')
            )
        except OSError:
            pass

    # Pull dream-cycle count from state.json (already updated by Step 6).
    dream_cycles = 0
    state_path = os.path.join(shadow_dir, '_meta', 'state.json')
    if os.path.isfile(state_path):
        try:
            with open(state_path, encoding="utf-8") as f:
                dream_cycles = int(json.load(f).get('dream_cycles_completed', 0) or 0)
        except (json.JSONDecodeError, OSError, ValueError, TypeError):
            dream_cycles = 0

    today = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    total_files = len(rows)

    out = ['# Shadow Index', '']
    if original_init_date:
        out.append(f'> Initially generated by shadow-frog-init on {original_init_date}')
    out.append(f'> Last updated by shadow-frog-dream on {today}')
    totals = (
        f'> Total files: {total_files} | Symbols: {total_symbols} '
        f'| Discoveries: {total_discoveries} | Cross-cutting: {cross_count}'
    )
    if dream_cycles > 0:
        totals += f' | Dream cycles: {dream_cycles}'
    out.append(totals)
    out.append('')
    out.append('| File | Language | Symbols | Discoveries |')
    out.append('|------|----------|---------|-------------|')

    for rel_path, language, names, sym_count, disc_count in rows:
        if sym_count == 0:
            sym_display = '0'
        elif len(names) <= 3:
            sym_display = f"{sym_count} ({', '.join(names)})"
        else:
            sym_display = f"{sym_count} ({', '.join(names[:3])}, ...)"
        out.append(f'| {rel_path} | {language} | {sym_display} | {disc_count} |')

    out.append('')

    try:
        with open(index_path, 'w', encoding="utf-8") as f:
            f.write('\n'.join(out))
    except OSError as e:
        print(f"  ⚠️  Could not write _index.md: {e}")
        return

    print(f"  Index: {total_files} files, {total_discoveries} discoveries")


# --- Step 8: Verify ---

def verify_reconciliation(repo_root, manifests):
    """Verify all artifacts are present on main. Returns list of failures.

    Index-membership uses the parsed `dream_id` column (via
    `_read_indexed_dream_ids`) rather than `dream_id in f.read()`. A naive
    substring check false-positives on shared prefixes (e.g. dream_id
    `20260420-1400-foo` would appear "indexed" merely because the index
    contains `20260420-14001-bar`), silently swallowing missing-index bugs.
    """
    failures = []

    index_path = os.path.join(repo_root, '.shadow', '_dreams', '_index.md')
    index_exists = os.path.isfile(index_path)
    indexed_ids = _read_indexed_dream_ids(repo_root) if index_exists else set()

    for branch, dream_id, manifest in manifests:
        dream_dir = os.path.join(repo_root, '.shadow', '_dreams', dream_id)

        for required in ['report.md', 'manifest.json', 'patch.diff']:
            if not os.path.isfile(os.path.join(dream_dir, required)):
                failures.append(f"{dream_id}: missing {required}")

        if not index_exists:
            failures.append(f"{dream_id}: _index.md does not exist")
        elif dream_id not in indexed_ids:
            failures.append(f"{dream_id}: missing from _index.md")

    return failures


# --- Step 9: Cleanup branches ---

def cleanup_branches(repo_root, manifests, dream_ns, dry_run=False):
    """Delete reconciled dream branches (local and remote).

    Only deletes a branch if:
    - The reconciliation commit is already on origin/<default-branch>
      (so the artifacts the branch carries are durably persisted)
    - All 3 artifacts exist on main (report.md, manifest.json, patch.diff)
    - The dream_id appears in _index.md
    - No un-reconciled branches list this branch as parent

    Returns (deleted, kept) counts.
    """
    index_path = os.path.join(repo_root, '.shadow', '_dreams', '_index.md')
    indexed_ids = _read_indexed_dream_ids(repo_root) if os.path.isfile(index_path) else set()

    # Check if SHADOWFROG_KEEP_BRANCHES is set
    if os.environ.get('SHADOWFROG_KEEP_BRANCHES', '').strip() in ('1', 'true', 'yes'):
        print("  SHADOWFROG_KEEP_BRANCHES is set — skipping cleanup.")
        return 0, len(manifests)

    # Safety check 0: refuse cleanup unless reconciliation commit is on
    # origin/<default-branch>. Otherwise a single failed `git push` would
    # destroy the only copy of the discoveries.
    if not dry_run:
        # Safety check 0a: refuse cleanup while .shadow/ has uncommitted
        # changes. In the combined `reconcile --cleanup-branches` invocation
        # the merge (Steps 3-9) writes discoveries into the WORKING TREE only
        # — HEAD has not moved yet — so the ancestor check below passes
        # trivially against the pre-reconciliation HEAD while the merged
        # discoveries are still unpersisted. Deleting the dream branches here
        # would destroy the only durable copy. A dirty .shadow/ is the
        # signal that reconciliation output has not been committed + pushed.
        shadow_status = subprocess.run(
            ['git', 'status', '--porcelain=v1', '--', '.shadow/'],
            capture_output=True, text=True, cwd=repo_root, encoding="utf-8"
        )
        if shadow_status.stdout.strip():
            print(f"  ❌ Refusing cleanup: .shadow/ has uncommitted changes.", file=sys.stderr)
            print(f"     Commit and push the reconciliation first:", file=sys.stderr)
            print(f"       git add .shadow/ && git commit && git push", file=sys.stderr)
            print(f"     then re-run with --cleanup-branches.", file=sys.stderr)
            return 0, len(manifests)

        try:
            default_branch = git(
                'symbolic-ref', '--short', 'refs/remotes/origin/HEAD',
                cwd=repo_root, check=False
            )
            default_branch = default_branch.replace('origin/', '').strip() or 'main'
        except RuntimeError:
            default_branch = 'main'

        head_sha = git('rev-parse', 'HEAD', cwd=repo_root, check=False)
        ancestor_check = subprocess.run(
            ['git', 'merge-base', '--is-ancestor',
             head_sha, f'origin/{default_branch}'],
            capture_output=True, text=True, cwd=repo_root, encoding="utf-8"
        )
        if ancestor_check.returncode != 0:
            print(f"  ❌ Refusing cleanup: HEAD ({head_sha[:7]}) is NOT an", file=sys.stderr)
            print(f"     ancestor of origin/{default_branch}.", file=sys.stderr)
            print(f"     Run `git push` first so the discoveries are durable,", file=sys.stderr)
            print(f"     then re-run with --cleanup-branches.", file=sys.stderr)
            return 0, len(manifests)

    # Find all remaining dream branches (to check for descendants)
    all_branches_raw = git('branch', '-r', '--format=%(refname:short)',
                           cwd=repo_root, check=False)
    prefix = f'dream/{dream_ns}/'
    all_remote_branches = set()
    for b in all_branches_raw.split('\n'):
        b = b.strip()
        if not b:
            continue
        short = b[len('origin/'):] if b.startswith('origin/') else b
        if short.startswith(prefix):
            all_remote_branches.add(short)

    deleted = 0
    kept = 0

    for branch, dream_id, manifest in manifests:
        dream_dir = os.path.join(repo_root, '.shadow', '_dreams', dream_id)

        # Safety check 1: all artifacts on main
        artifacts_ok = all(
            os.path.isfile(os.path.join(dream_dir, f))
            for f in ('report.md', 'manifest.json', 'patch.diff')
        )
        if not artifacts_ok:
            print(f"  ⚠️  KEEPING {branch} — artifacts not on main")
            kept += 1
            continue

        # Safety check 2: in index. Set-membership (NOT substring) — a raw
        # `dream_id in index_content` falsely passes when our dream_id is a
        # prefix of any indexed ID, which would delete an un-reconciled branch.
        # Same prefix-collision shape as `verify_reconciliation`.
        if dream_id not in indexed_ids:
            print(f"  ⚠️  KEEPING {branch} — not in _index.md")
            kept += 1
            continue

        # Safety check 3: no un-reconciled descendants
        has_descendants = False
        for other_branch in all_remote_branches:
            if other_branch == branch:
                continue
            other_id = other_branch[len(prefix):] if other_branch.startswith(prefix) else other_branch
            # Check if this other branch is NOT in the index (un-reconciled)
            # AND lists our branch as parent. Set-membership for the same
            # prefix-collision reason as Safety check 2 above.
            if other_id not in indexed_ids:
                # Check manifest for parent reference
                other_manifest_raw = git_show(
                    f'origin/{other_branch}',
                    f'.shadow/_dreams/{other_id}/manifest.json',
                    cwd=repo_root
                )
                if other_manifest_raw:
                    try:
                        other_manifest = json.loads(other_manifest_raw)
                        if other_manifest.get('parent_branch', '') == branch:
                            has_descendants = True
                            break
                    except json.JSONDecodeError:
                        pass

        if has_descendants:
            print(f"  ⚠️  KEEPING {branch} — has un-reconciled descendants")
            kept += 1
            continue

        # All checks passed — delete
        if dry_run:
            print(f"  Would delete: {branch}")
            deleted += 1
            continue

        # Delete remote first (network op that can fail)
        result = subprocess.run(
            ['git', 'push', 'origin', '--delete', branch],
            capture_output=True, text=True, cwd=repo_root, encoding="utf-8"
        )
        if result.returncode == 0:
            print(f"  🗑  Deleted remote: {branch}")
        else:
            # Remote might not exist (local-only branch)
            if 'remote ref does not exist' not in result.stderr:
                print(f"  ⚠️  Failed to delete remote {branch}: {result.stderr.strip()}")

        # Delete local
        result = subprocess.run(
            ['git', 'branch', '-D', branch],
            capture_output=True, text=True, cwd=repo_root, encoding="utf-8"
        )
        if result.returncode == 0:
            print(f"  🗑  Deleted local: {branch}")
        # Also delete the remote-tracking ref
        subprocess.run(
            ['git', 'branch', '-dr', f'origin/{branch}'],
            capture_output=True, text=True, cwd=repo_root, encoding="utf-8"
        )

        # Best-effort worktree GC — the directory at
        # `${DREAM_WORKTREE_BASE:-/tmp/shadowfrog-dreams}/<ns>/dream-<slug>`
        # is now orphaned (its branch is gone). Removing it here closes the
        # leak documented in bug-worktree-leak.md.
        #
        # `branch` is the branch we just deleted; passing it lets the GC
        # refuse to remove a path that another dream (sharing the same
        # slug) has reclaimed for its own live worktree.
        _gc_worktree_after_merge(repo_root, dream_ns, dream_id, branch)

        deleted += 1

    return deleted, kept


# Compiled here so the error message is consistent with `dream-setup.sh`.
# DREAM_ID format: YYYYMMDD-HHMMSSZ-<slug>. The leading timestamp is
# fixed-width (8 digits + '-' + 6 digits + 'Z' + '-' = 17 chars), but we
# anchor on the regex to be robust against drift.
_DREAM_ID_SPLIT_RE = re.compile(r'^(\d{8}-\d{6}Z)-(.+)$')


def _slug_from_dream_id(dream_id):
    """Return the slug portion of a dream_id, or None if it doesn't match
    the canonical `YYYYMMDD-HHMMSSZ-<slug>` shape.

    Critical: do NOT use `dream_id.partition('-')[2]` — dream_ids contain
    multiple `-` (the date itself has one), so partition() returns the
    rest of the timestamp, NOT the slug.
    """
    m = _DREAM_ID_SPLIT_RE.match(dream_id or '')
    return m.group(2) if m else None


def _registered_worktree_branch(repo_root, candidate_path):
    """Return the branch name (without `refs/heads/` prefix) that git has
    registered at `candidate_path`, or `None` if no worktree is registered
    at that path (or git can't tell). Detached-HEAD worktrees return `None`.

    Parses `git worktree list --porcelain` output:
        worktree /abs/path
        HEAD <sha>
        branch refs/heads/<name>
    or:
        worktree /abs/path
        HEAD <sha>
        detached

    Paths are compared after `realpath` so macOS `/tmp` ↔ `/private/tmp` and
    other symlinked-base setups don't break the match.
    """
    try:
        result = subprocess.run(
            ['git', 'worktree', 'list', '--porcelain'],
            capture_output=True, text=True, cwd=repo_root, timeout=10,
            encoding="utf-8",
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None

    try:
        target = os.path.realpath(candidate_path)
    except (OSError, ValueError):
        return None

    def _matches(p):
        try:
            return os.path.realpath(p) == target
        except (OSError, ValueError):
            return False

    cur_path = None
    cur_branch = None
    for line in result.stdout.splitlines():
        if line.startswith('worktree '):
            # Flush previous entry if it matched.
            if cur_path is not None and _matches(cur_path):
                return cur_branch
            cur_path = line[len('worktree '):]
            cur_branch = None
        elif line.startswith('branch '):
            ref = line[len('branch '):]
            cur_branch = ref[len('refs/heads/'):] if ref.startswith('refs/heads/') else ref
    if cur_path is not None and _matches(cur_path):
        return cur_branch
    return None


def _gc_worktree_after_merge(repo_root, dream_ns, dream_id, deleted_branch=None):
    """Remove the dream worktree directory after its branch has been
    deleted. Safety-gated by `_worktree_safety.safe_worktree_path` — will
    NEVER `rm -rf` a path outside `$DREAM_WORKTREE_BASE/<ns>/dream-<slug>`.

    Cross-deletion guard: worktree paths are keyed on slug only (see
    `dream-setup.sh`: `WORKTREE_DIR=<base>/<ns>/dream-<slug>`), but
    `dream_id` includes a timestamp. So two dreams that re-use the same
    slug at different times share a worktree path. If the path we're
    about to GC is currently registered to a DIFFERENT branch — i.e. a
    later dream has reclaimed it — we must NOT touch it. Pass
    `deleted_branch` to enable this check.

    All failures are swallowed: the branch delete already succeeded, so a
    leaked worktree (the pre-fix steady state) is strictly less bad than
    an aborted cleanup_branches() loop.
    """
    try:
        slug = _slug_from_dream_id(dream_id)
        if not slug:
            return  # Can't derive worktree path — bail silently.
        base = os.environ.get('DREAM_WORKTREE_BASE', '/tmp/shadowfrog-dreams')
        candidate = os.path.join(base, dream_ns, f'dream-{slug}')

        # Import lazily so this module remains importable for tests that
        # don't exercise the worktree-GC path even if the helper is moved.
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        try:
            from _worktree_safety import safe_worktree_path, UnsafePath
        finally:
            # Only pop our own insertion (defensive against re-import).
            if sys.path and sys.path[0] == os.path.dirname(os.path.abspath(__file__)):
                sys.path.pop(0)

        try:
            resolved = safe_worktree_path(candidate, base)
        except UnsafePath as exc:
            print(f"  ⚠️  Skipping worktree GC for {dream_id}: {exc}")
            return

        # Cross-deletion guard: refuse to touch a path another dream owns.
        # Only consult git when we know which branch we expected (i.e.,
        # `deleted_branch` was passed by `cleanup_branches`). Callers that
        # pre-date this guard (tests, future ad-hoc invocations) default to
        # the original behavior — still gated by the safety check above.
        if deleted_branch:
            registered = _registered_worktree_branch(repo_root, str(resolved))
            if registered is not None and registered != deleted_branch:
                print(
                    f"  ↳ Skipping worktree GC for {dream_id}: "
                    f"path {resolved} now belongs to {registered}"
                )
                return

        # Polite path first: let git update its own bookkeeping.
        worktree_removed = False
        result = subprocess.run(
            ['git', 'worktree', 'remove', str(resolved), '--force'],
            capture_output=True, text=True, cwd=repo_root,
            encoding="utf-8",
        )
        if result.returncode == 0:
            worktree_removed = True
            print(f"  🗑  Removed worktree: {resolved}")
        # Fallback: directory may still be on disk (git failed, dead
        # gitdir pointer, etc.). The safety gate already proved the path
        # is `<base>/<ns>/dream-<slug>` so the rm is bounded.
        if not worktree_removed and (resolved.exists() or resolved.is_symlink()):
            try:
                shutil.rmtree(str(resolved), ignore_errors=False)
                print(f"  🗑  Removed worktree (fallback rm -rf): {resolved}")
            except OSError as exc:
                # Worst case: leak the directory but don't break cleanup.
                print(f"  ⚠️  Worktree rm failed for {resolved}: {exc}")
                return
        # Clean up git's stale-worktree bookkeeping.
        subprocess.run(
            ['git', 'worktree', 'prune'],
            capture_output=True, text=True, cwd=repo_root,
            encoding="utf-8",
        )
    except Exception as exc:  # noqa: BLE001 — GC must never crash cleanup.
        print(f"  ⚠️  Worktree GC raised for {dream_id}: {exc}")


# --- Main orchestration ---

def main():
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8")
    # Parse arguments
    repo_root = None
    dry_run = False
    verify_only = False
    cleanup = False
    namespace_override = None

    args = sys.argv[1:]
    i = 0
    while i < len(args):
        if args[i] in ('--help', '-h'):
            print(__doc__)
            sys.exit(0)
        elif args[i] == '--dry-run':
            dry_run = True
        elif args[i] == '--verify-only':
            verify_only = True
        elif args[i] == '--cleanup-branches':
            cleanup = True
        elif args[i] == '--namespace':
            i += 1
            if i >= len(args):
                print("ERROR: --namespace requires a value", file=sys.stderr)
                sys.exit(1)
            namespace_override = args[i]
        elif not args[i].startswith('-'):
            repo_root = args[i]
        else:
            print(f"Unknown argument: {args[i]}", file=sys.stderr)
            print("Run with --help for usage.", file=sys.stderr)
            sys.exit(1)
        i += 1

    if not repo_root:
        repo_root = subprocess.run(
            ['git', 'rev-parse', '--show-toplevel'],
            capture_output=True, text=True, encoding="utf-8"
        ).stdout.strip()

    if not repo_root or not os.path.isdir(repo_root):
        print("ERROR: Not in a git repository", file=sys.stderr)
        sys.exit(1)

    # Resolve namespace
    dream_ns = namespace_override or os.environ.get('DREAM_NAMESPACE', '')
    if not dream_ns:
        task_info = os.path.join(repo_root, 'TASK_INFO.json')
        if os.path.isfile(task_info):
            try:
                dream_ns = json.load(open(task_info, encoding="utf-8")).get('dream_namespace', '')
            except (json.JSONDecodeError, OSError):
                pass
    if not dream_ns:
        env_file = os.path.join(repo_root, '.env')
        if os.path.isfile(env_file):
            with open(env_file, encoding="utf-8") as f:
                for line in f:
                    if line.startswith('DREAM_NAMESPACE='):
                        dream_ns = line.split('=', 1)[1].strip()
                        break
    if not dream_ns:
        dream_ns = os.path.basename(repo_root)

    print(f"=== Dream Reconciliation ===")
    print(f"Repo: {repo_root}")
    print(f"Namespace: {dream_ns}")
    if dry_run:
        print("Mode: DRY RUN")
    print()

    # Verify-only mode: re-check everything already in _index.md (this is what
    # users actually want — "did my reconciliation produce the right files?").
    # The previous implementation called discover_branches() which by design
    # returns ONLY un-reconciled branches, so verify-only could never see
    # anything to verify.
    if verify_only:
        indexed = _read_indexed_branches(repo_root)
        if not indexed:
            print("No reconciled dreams found in _index.md.")
            sys.exit(0)
        manifests = []
        for branch, dream_id in indexed:
            # Reconstruct minimal manifest from local mirrored copy
            local_manifest = os.path.join(
                repo_root, '.shadow', '_dreams', dream_id, 'manifest.json'
            )
            if os.path.isfile(local_manifest):
                try:
                    with open(local_manifest, encoding="utf-8") as f:
                        m = json.load(f)
                    manifests.append((branch, dream_id, m))
                except (json.JSONDecodeError, OSError):
                    manifests.append((branch, dream_id, {}))
            else:
                manifests.append((branch, dream_id, {}))
        failures = verify_reconciliation(repo_root, manifests)
        if failures:
            print("Verification FAILED:")
            for f in failures:
                print(f"  ❌ {f}")
            sys.exit(1)
        print(f"✓ All {len(manifests)} indexed dreams verified.")
        sys.exit(0)

    # Step 1: Discover branches
    print("Step 1: Discovering branches...")
    branches = discover_branches(repo_root, dream_ns)
    if not branches:
        print("  No new branches to reconcile.")
        # If --cleanup-branches was requested, fall through to cleanup using
        # the branches already in the index. This is the canonical post-push
        # flow: reconcile → push → re-run with --cleanup-branches.
        if cleanup:
            indexed = _read_indexed_branches(repo_root)
            if not indexed:
                print("  Nothing in _index.md to clean up either.")
                sys.exit(0)
            # Synthesize minimal manifests from the local mirrored copies so
            # cleanup_branches can do its safety checks.
            cleanup_manifests = []
            for branch, dream_id in indexed:
                local_manifest = os.path.join(
                    repo_root, '.shadow', '_dreams', dream_id, 'manifest.json'
                )
                m = {}
                if os.path.isfile(local_manifest):
                    try:
                        with open(local_manifest, encoding="utf-8") as f:
                            m = json.load(f)
                    except (json.JSONDecodeError, OSError):
                        pass
                cleanup_manifests.append((branch, dream_id, m))
            print()
            print("Step 9: Cleaning up reconciled branches...")
            deleted, kept = cleanup_branches(
                repo_root, cleanup_manifests, dream_ns, dry_run=dry_run
            )
            print(f"  Deleted: {deleted}, Kept: {kept}")
        sys.exit(0)
    print(f"  Found {len(branches)} new branch(es):")
    for branch, dream_id in branches:
        print(f"    {branch}")
    print()

    # Step 2: Load manifests
    print("Step 2: Loading manifests...")
    manifests, skipped = load_manifests(repo_root, branches)
    print(f"  Valid: {len(manifests)}, Skipped: {len(skipped)}")
    for branch, dream_id, reason in skipped:
        print(f"    SKIP {dream_id}: {reason}")
    print()

    if not manifests:
        print("No valid manifests to reconcile.")
        sys.exit(0)

    # Step 3: Merge discoveries
    print("Step 3: Merging discoveries...")
    merged, dup_skipped = merge_discoveries(repo_root, manifests, dry_run=dry_run)
    print(f"  Merged: {merged}, Duplicates skipped: {dup_skipped}")
    print()

    # Step 4: Mirror reports
    print("Step 4: Mirroring reports...")
    mirrored, corrupted = mirror_reports(repo_root, manifests, dry_run=dry_run)
    print(f"  Mirrored: {mirrored}")
    if corrupted:
        print(f"  Corrupted: {len(corrupted)}")
        for did, wrong_did in corrupted:
            print(f"    ⚠️  {did} contained report from {wrong_did}")
    print()

    # Step 5: Update index
    print("Step 5: Updating index...")
    update_index(repo_root, manifests, dry_run=dry_run)
    print(f"  Added {len(manifests)} entries")
    print()

    # Step 6: Update state
    print("Step 6: Updating state.json...")
    update_state(repo_root, manifests, dry_run=dry_run)
    print()

    # Step 7: Rebuild top-level _index.md (must run AFTER update_state so
    # the dream_cycles_completed count it reads is current).
    print("Step 7: Rebuilding top-level _index.md...")
    rebuild_top_index(repo_root, dry_run=dry_run)
    print()

    # Step 8: Verify
    if not dry_run:
        print("Step 8: Verifying...")
        failures = verify_reconciliation(repo_root, manifests)
        if failures:
            print("  VERIFICATION FAILED:")
            for f in failures:
                print(f"    ❌ {f}")
            print()
            print("Re-run reconciliation for failed dreams.")
            sys.exit(1)
        else:
            print(f"  ✓ All {len(manifests)} dreams verified.")

    print()
    print(f"=== Reconciliation {'would complete' if dry_run else 'complete'} ===")
    print(f"  Dreams reconciled: {len(manifests)}")
    print(f"  Discoveries merged: {merged}")
    if not dry_run:
        print()
        print("Next: git add .shadow/ && git commit && git push")

    # Step 9: Cleanup branches (optional, after user commits and pushes)
    if cleanup and manifests:
        print()
        print("Step 9: Cleaning up reconciled branches...")
        if not dry_run:
            print("  ⚠️  Run this AFTER 'git push' succeeds on main.")
            print("  Checking artifacts on main...")
        deleted, kept = cleanup_branches(
            repo_root, manifests, dream_ns, dry_run=dry_run
        )
        print(f"  Deleted: {deleted}, Kept: {kept}")


if __name__ == '__main__':
    main()

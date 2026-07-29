#!/usr/bin/env python3
"""shadow-viewer: Query and browse a .shadow/ knowledge base.

Usage:
    shadow-viewer.py [options]

Views:
    --summary               Overview + detailed statistics (default)
    --search QUERY          Universal search across files, symbols, and text
    --prefs                 Show project-wide preferences
    --recent [N]            N most recent discoveries with content (default: 10)
    --labels LABEL          Show discoveries by label (bug, security, etc.)
    --top FILE              Top actionable discoveries for FILE (hook-sized)
    --check-invariants      Report structural violations (exit 1 if any)

Options:
    --shadow-dir DIR        Path to .shadow/ directory (default: auto-detect)

Exit codes:
    0  Success (possibly with warnings on stderr)
    1  Fatal error (shadow dir not found, no results possible)
"""

import argparse
import json
import os
import re
import sys
import traceback
from collections import defaultdict
from datetime import datetime
from pathlib import Path


_DISCOVERY_META_RE = re.compile(
    r"_\((\w+),\s*source:\s*(\w+)"
    r"(?:,\s*labels:\s*\[([^\]]*)\])?"
    r"\)_"
)


def warn(msg):
    """Print a warning to stderr. Agents read these to adjust strategy."""
    print(f"[shadow-viewer warning] {msg}", file=sys.stderr)


def error(msg):
    """Print an error to stderr."""
    print(f"[shadow-viewer error] {msg}", file=sys.stderr)


def find_shadow_dir(start="."):
    """Walk up from start to find .shadow/ directory."""
    try:
        p = Path(start).resolve()
        while p != p.parent:
            candidate = p / ".shadow"
            if candidate.is_dir():
                return candidate
            p = p.parent
    except (OSError, PermissionError) as e:
        error(f"Failed to search for .shadow/ directory from '{start}': {e}")
    return None


def parse_discovery(line, continuation_lines=None):
    """Parse a discovery bullet and its metadata line(s)."""
    try:
        text = line[2:].strip() if line.startswith("- ") else line.strip()
    except (TypeError, AttributeError) as e:
        warn(f"parse_discovery: bad line input ({type(line).__name__}): {e}")
        return {"text": str(line) if line else ""}

    meta = {}
    full_text = text

    if continuation_lines:
        for cl in continuation_lines:
            try:
                stripped = cl.strip()
                # _(status, source: type, labels: [l1, l2])_ or _(status, source: type)_
                m = _DISCOVERY_META_RE.match(stripped)
                if m:
                    meta["status"] = m.group(1)
                    meta["source"] = m.group(2)
                    if m.group(3):
                        meta["labels"] = [
                            l.strip()
                            for l in m.group(3).split(",")
                            if l.strip()
                        ]
                else:
                    # _(source: type)_ (preferences format)
                    m2 = re.match(r"_\(source:\s*(\w+)\)_", stripped)
                    if m2:
                        meta["source"] = m2.group(1)
                    elif stripped.startswith("Also involves:"):
                        refs = re.findall(r"`([^`]+)`", stripped)
                        meta["also_involves"] = refs
                    elif stripped.startswith("Dream report:"):
                        m_dr = re.search(r"`([^`]+)`", stripped)
                        if m_dr:
                            meta["dream_report"] = m_dr.group(1)
                    else:
                        full_text += " " + stripped
            except Exception as e:
                warn(f"parse_discovery: failed parsing continuation line "
                     f"'{cl[:80]}': {e}")

    return {"text": full_text, **meta}


def parse_shadow_file(filepath):
    """Parse a per-file shadow into structured data.

    Returns a result dict even on partial failure — whatever was parsed
    before the error is preserved. Warnings go to stderr.
    """
    result = {
        "path": str(filepath),
        "source_file": None,
        "language": None,
        "lines": None,
        "last_modified": None,
        "symbols": [],
        "discoveries": [],
        "cross_references": [],
        "parse_errors": [],
    }

    try:
        content = filepath.read_text(encoding="utf-8")
    except UnicodeDecodeError as e:
        msg = (f"Cannot read {filepath}: encoding error at byte "
               f"{e.start}: {e.reason}. File may not be UTF-8.")
        warn(msg)
        result["parse_errors"].append(msg)
        return result
    except OSError as e:
        msg = f"Cannot read {filepath}: {e}"
        warn(msg)
        result["parse_errors"].append(msg)
        return result

    lines = content.split("\n")
    current_symbol = None
    i = 0

    while i < len(lines):
        line = lines[i]

        try:
            # Header: # Shadow: src/auth.py
            if line.startswith("# Shadow: "):
                result["source_file"] = line[len("# Shadow: "):].strip()

            # Metadata: **Language**: Python | **Lines**: 142 | ...
            elif line.startswith("**Language**"):
                parts = line.split("|")
                for part in parts:
                    part = part.strip()
                    if part.startswith("**Language**"):
                        m = re.search(r"\*\*:\s*(.+)", part)
                        if m:
                            result["language"] = m.group(1).strip()
                    elif "Lines" in part:
                        m = re.search(r"(\d+)", part)
                        if m:
                            try:
                                result["lines"] = int(m.group(1))
                            except ValueError:
                                pass
                    elif "Last modified" in part:
                        m = re.search(r"\*\*:\s*(.+)", part)
                        if m:
                            result["last_modified"] = m.group(1).strip()

            # Symbol heading: ## `symbol_name` or ### `Class.method`
            elif re.match(r"^#{2,3}\s", line):
                sym_match = re.match(r"^(#{2,3})\s+`(.+?)`", line)
                if sym_match:
                    name = sym_match.group(2)
                    current_symbol = name
                    result["symbols"].append(name)
                elif "Cross-References" in line:
                    current_symbol = "__cross_refs__"
                elif "File-Level" in line:
                    current_symbol = "__file_level__"
                else:
                    current_symbol = None

            # Discovery bullet (skip cross-reference links)
            elif (
                line.strip().startswith("- ")
                and current_symbol
                and current_symbol != "__cross_refs__"
            ):
                # Collect continuation lines
                continuation = []
                j = i + 1
                while j < len(lines):
                    next_line = lines[j]
                    if (
                        next_line.strip() == ""
                        or next_line.strip().startswith("- ")
                        or re.match(r"^#{1,3}\s", next_line)
                    ):
                        break
                    continuation.append(next_line)
                    j += 1

                disc = parse_discovery(line.strip(), continuation)
                disc["symbol"] = (
                    "file-level" if current_symbol == "__file_level__"
                    else current_symbol
                )
                disc["file"] = result["source_file"]
                result["discoveries"].append(disc)
                i = j
                continue

            # Cross-reference link
            elif (
                current_symbol == "__cross_refs__"
                and line.strip().startswith("- ")
            ):
                link_match = re.search(r"\[(.+?)\]", line)
                if link_match:
                    result["cross_references"].append(link_match.group(1))

        except Exception as e:
            msg = (f"Error parsing {filepath} at line {i + 1}: "
                   f"{type(e).__name__}: {e}")
            warn(msg)
            result["parse_errors"].append(msg)

        i += 1

    return result


def parse_prefs(shadow_dir):
    """Parse _prefs.md into a list of preferences."""
    prefs_path = shadow_dir / "_prefs.md"
    if not prefs_path.exists():
        return []

    try:
        content = prefs_path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as e:
        warn(f"Cannot read preferences file {prefs_path}: {e}")
        return []

    prefs = []
    lines = content.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        try:
            if line.strip().startswith("- ") and not line.strip().startswith(
                "- ["
            ):
                continuation = []
                j = i + 1
                while j < len(lines):
                    next_line = lines[j]
                    if next_line.strip() == "" or next_line.strip().startswith(
                        "- "
                    ):
                        break
                    continuation.append(next_line)
                    j += 1

                pref = parse_discovery(line.strip(), continuation)
                pref["type"] = "preference"
                prefs.append(pref)
                i = j
                continue
        except Exception as e:
            warn(f"Error parsing preference at line {i + 1} in "
                 f"{prefs_path}: {e}")
        i += 1

    return prefs


def parse_cross_cutting(shadow_dir):
    """Parse all _cross/*.md files."""
    cross_dir = shadow_dir / "_cross"
    if not cross_dir.exists():
        return []

    entries = []
    try:
        md_files = sorted(cross_dir.glob("*.md"))
    except OSError as e:
        warn(f"Cannot list cross-cutting directory {cross_dir}: {e}")
        return []

    for f in md_files:
        try:
            content = f.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as e:
            warn(f"Cannot read cross-cutting file {f}: {e}")
            continue

        entry = {"slug": f.stem, "file": str(f.name)}

        try:
            # Title
            m = re.search(r"^# (.+)", content, re.MULTILINE)
            if m:
                entry["title"] = m.group(1).strip()

            # Category
            m = re.search(r"\*\*Category\*\*:\s*(.+)", content)
            if m:
                entry["category"] = m.group(1).strip()

            # Refs — only within the **Refs**: section, not backticked
            # bullets elsewhere in the file (e.g., inside the Discovery body).
            refs = []
            refs_block = re.search(
                r"\*\*Refs\*\*:\s*\n(.*?)(?=\n[ \t]*\n|\n\*\*|\Z)",
                content,
                re.DOTALL,
            )
            if refs_block:
                refs = re.findall(r"-\s*`([^`]+)`", refs_block.group(1))
            entry["refs"] = refs

            # Discovery text
            m = re.search(
                r"\*\*Discovery\*\*:\s*(.+?)(?=\n\n|\n_\(|\Z)",
                content,
                re.DOTALL,
            )
            if m:
                entry["discovery"] = m.group(1).strip()

            # Status/source (with optional labels)
            m = _DISCOVERY_META_RE.search(content)
            if m:
                entry["status"] = m.group(1)
                entry["source"] = m.group(2)
                if m.group(3):
                    entry["labels"] = [
                        l.strip()
                        for l in m.group(3).split(",")
                        if l.strip()
                    ]
            else:
                # Fallback to simpler pattern
                m2 = re.search(
                    r"_\((\w+),\s*source:\s*(\w+)\)_", content
                )
                if m2:
                    entry["status"] = m2.group(1)
                    entry["source"] = m2.group(2)
        except Exception as e:
            warn(f"Error parsing cross-cutting file {f.name}: "
                 f"{type(e).__name__}: {e}")
            entry.setdefault("title", f.stem)

        entries.append(entry)

    return entries


def load_state(shadow_dir):
    """Load _meta/state.json."""
    state_path = shadow_dir / "_meta" / "state.json"
    if not state_path.exists():
        return {}
    try:
        content = state_path.read_text(encoding="utf-8")
        state = json.loads(content)
        if not isinstance(state, dict):
            warn(f"state.json is not a JSON object (got {type(state).__name__})")
            return {}
        return state
    except json.JSONDecodeError as e:
        warn(f"Invalid JSON in {state_path}: {e}")
        return {}
    except OSError as e:
        warn(f"Cannot read {state_path}: {e}")
        return {}


def get_all_shadow_files(shadow_dir):
    """Get all per-file shadow .md files (excluding special files)."""
    special = {"_index.md", "_prefs.md"}
    special_dirs = {"_cross", "_meta", "_dreams"}

    results = []
    try:
        for f in shadow_dir.rglob("*.md"):
            try:
                rel = f.relative_to(shadow_dir)
                parts = rel.parts
                if parts[0] in special_dirs:
                    continue
                if str(rel) in special:
                    continue
                results.append(f)
            except (ValueError, IndexError) as e:
                warn(f"Skipping file {f}: {e}")
    except OSError as e:
        warn(f"Error walking shadow directory {shadow_dir}: {e}")

    return sorted(results)


def collect_all_discoveries(shadow_dir):
    """Parse all shadow files and collect every discovery.

    Continues past individual file failures — reports errors and moves on.
    """
    all_disc = []
    failed_files = []
    for sf in get_all_shadow_files(shadow_dir):
        try:
            parsed = parse_shadow_file(sf)
            if parsed.get("parse_errors"):
                failed_files.append(
                    (str(sf), parsed["parse_errors"])
                )
            for d in parsed["discoveries"]:
                d.setdefault("file", parsed["source_file"])
                d["shadow_path"] = str(sf.relative_to(shadow_dir))
                try:
                    d["shadow_mtime"] = os.path.getmtime(sf)
                except OSError:
                    d["shadow_mtime"] = 0.0
                all_disc.append(d)
        except Exception as e:
            msg = f"Failed to parse {sf}: {type(e).__name__}: {e}"
            warn(msg)
            failed_files.append((str(sf), [msg]))

    if failed_files:
        warn(f"{len(failed_files)} file(s) had parse errors "
             f"(discoveries from other files still collected)")

    return all_disc


# --- View Functions ---


def view_summary(shadow_dir):
    """Overview + detailed statistics.

    Each section is independently wrapped — if label stats fail, you
    still get counts and the per-file table.
    """
    # Load data (each can fail independently)
    state = {}
    shadow_files = []
    prefs = []
    cross = []

    try:
        state = load_state(shadow_dir)
    except Exception as e:
        warn(f"Failed to load state.json: {e}")

    try:
        shadow_files = get_all_shadow_files(shadow_dir)
    except Exception as e:
        warn(f"Failed to list shadow files: {e}")

    try:
        prefs = parse_prefs(shadow_dir)
    except Exception as e:
        warn(f"Failed to parse preferences: {e}")

    try:
        cross = parse_cross_cutting(shadow_dir)
    except Exception as e:
        warn(f"Failed to parse cross-cutting discoveries: {e}")

    # Parse each file once for both stats and discoveries
    file_stats = []
    all_disc = []
    total_symbols = 0
    for sf in shadow_files:
        try:
            parsed = parse_shadow_file(sf)
            src = parsed["source_file"] or str(sf.relative_to(shadow_dir))
            n_sym = len(parsed["symbols"])
            n_disc = len(parsed["discoveries"])
            total_symbols += n_sym
            file_stats.append((src, n_sym, n_disc))
            for d in parsed["discoveries"]:
                d.setdefault("file", parsed["source_file"])
                d["shadow_path"] = str(sf.relative_to(shadow_dir))
                all_disc.append(d)
        except Exception as e:
            warn(f"Failed to process {sf}: {e}")
    file_stats.sort(key=lambda x: x[2], reverse=True)

    # Header counts (always shown)
    print("Shadow Knowledge Base Summary")
    print("=" * 50)
    print(f"  Files shadowed:    {len(shadow_files)}")
    print(f"  Symbols tracked:   {total_symbols}")
    print(f"  Discoveries:       {len(all_disc)}")
    print(f"  Preferences:       {len(prefs)}")
    print(f"  Cross-cutting:     {len(cross)}")

    # Source breakdown
    try:
        source_counts = defaultdict(int)
        status_counts = defaultdict(int)
        for d in all_disc:
            source_counts[d.get("source", "unknown")] += 1
            status_counts[d.get("status", "unknown")] += 1

        if source_counts:
            print("\nBy source:")
            for src, cnt in sorted(source_counts.items(), key=lambda x: -x[1]):
                pct = cnt / len(all_disc) * 100 if all_disc else 0
                bar = "#" * int(pct / 2)
                print(f"  {src:15s} {cnt:4d} ({pct:5.1f}%) {bar}")

        if status_counts:
            print("\nBy status:")
            for st, cnt in sorted(status_counts.items(), key=lambda x: -x[1]):
                pct = cnt / len(all_disc) * 100 if all_disc else 0
                bar = "#" * int(pct / 2)
                print(f"  {st:15s} {cnt:4d} ({pct:5.1f}%) {bar}")
    except Exception as e:
        warn(f"Failed to compute source/status breakdown: {e}")

    # Label breakdown
    try:
        label_counts = defaultdict(int)
        for d in all_disc:
            for lbl in d.get("labels", []):
                label_counts[lbl] += 1
        if label_counts:
            print("\nBy label:")
            for lbl, cnt in sorted(label_counts.items(), key=lambda x: -x[1]):
                print(f"  {lbl:15s} {cnt:4d}")
    except Exception as e:
        warn(f"Failed to compute label breakdown: {e}")

    # Per-file table
    try:
        if file_stats:
            print(f"\n{'File':<40s} {'Symbols':>8s} {'Disc.':>6s}")
            print(f"{'-'*40} {'-'*8} {'-'*6}")
            for src, n_sym, n_disc in file_stats[:20]:
                print(f"{src:<40s} {n_sym:>8d} {n_disc:>6d}")
            if len(file_stats) > 20:
                print(f"... and {len(file_stats) - 20} more files")
    except Exception as e:
        warn(f"Failed to render per-file table: {e}")

    # Cross-cutting titles
    try:
        if cross:
            print(f"\nCross-cutting discoveries:")
            for e in cross:
                title = e.get("title", e.get("slug", "?"))
                cat = e.get("category", "?")
                print(f"  [{cat}] {title}")
    except Exception as e:
        warn(f"Failed to render cross-cutting list: {e}")

    # State info
    try:
        if state:
            print(f"\nLast update: {state.get('last_update_at', '?')} "
                  f"({state.get('last_update_type', '?')})")
            print(f"Last commit: {state.get('last_commit', '?')}")
    except Exception as e:
        warn(f"Failed to render state info: {e}")


def view_search(shadow_dir, query):
    """Universal search: matches file names, symbol names, and discovery text.

    Also searches cross-cutting discoveries and preferences.
    Results are grouped by match location for readability.
    Each search domain (per-file, cross-cutting, prefs) is independent —
    if one fails, the others still return results.
    """
    query_lower = query.lower()
    disc_matches = []
    cross_matches = []
    pref_matches = []
    section_errors = []

    # Search per-file shadows
    try:
        for sf in get_all_shadow_files(shadow_dir):
            try:
                parsed = parse_shadow_file(sf)
                source_file = parsed["source_file"] or str(
                    sf.relative_to(shadow_dir)
                )
                file_name_hit = query_lower in source_file.lower()

                for d in parsed["discoveries"]:
                    sym = d.get("symbol", "")
                    text = d.get("text", "")
                    sym_hit = query_lower in sym.lower()
                    text_hit = query_lower in text.lower()
                    also_hit = any(
                        query_lower in ref.lower()
                        for ref in d.get("also_involves", [])
                    )

                    if file_name_hit or sym_hit or text_hit or also_hit:
                        disc_matches.append({
                            "file": source_file,
                            "symbol": sym,
                            "text": text,
                            "status": d.get("status", "?"),
                            "source": d.get("source", "?"),
                            "also_involves": d.get("also_involves", []),
                            "match": (
                                "file" if file_name_hit else
                                "symbol" if sym_hit else
                                "also_involves" if also_hit else "text"
                            ),
                        })
            except Exception as e:
                warn(f"Search: error processing {sf}: {e}")
    except Exception as e:
        msg = f"Search: failed to search per-file shadows: {e}"
        warn(msg)
        section_errors.append(msg)

    # Search cross-cutting discoveries
    try:
        for e in parse_cross_cutting(shadow_dir):
            title = e.get("title", "")
            disc_text = e.get("discovery", "")
            refs = e.get("refs", [])
            if (query_lower in title.lower()
                    or query_lower in disc_text.lower()
                    or any(query_lower in r.lower() for r in refs)):
                cross_matches.append(e)
    except Exception as e:
        msg = f"Search: failed to search cross-cutting: {e}"
        warn(msg)
        section_errors.append(msg)

    # Search preferences
    try:
        for p in parse_prefs(shadow_dir):
            if query_lower in p.get("text", "").lower():
                pref_matches.append(p)
    except Exception as e:
        msg = f"Search: failed to search preferences: {e}"
        warn(msg)
        section_errors.append(msg)

    total = len(disc_matches) + len(cross_matches) + len(pref_matches)
    if total == 0:
        print(f"No results for '{query}'.")
        if section_errors:
            print(f"Note: {len(section_errors)} search section(s) had errors "
                  f"— results may be incomplete. Check stderr for details.")
        return

    print(f"Search: '{query}' ({total} results)")
    print("=" * 50)

    # Per-file discoveries, grouped by file
    if disc_matches:
        try:
            by_file = defaultdict(list)
            for d in disc_matches:
                by_file[d["file"]].append(d)

            for file, discs in sorted(by_file.items()):
                print(f"\n{file} ({len(discs)} matches)")
                print("-" * (len(file) + 15))
                for d in discs:
                    sym = d["symbol"]
                    print(f"  {file}::{sym}")
                    print(f"  {d['text'][:120]}")
                    print(f"  ({d['status']}, source: {d['source']})")
                    if d.get("also_involves"):
                        print(
                            f"  Also involves: "
                            f"{', '.join(d['also_involves'])}"
                        )
        except Exception as e:
            warn(f"Search: failed to render per-file results: {e}")

    # Cross-cutting
    if cross_matches:
        try:
            print(f"\nCross-cutting ({len(cross_matches)} matches)")
            print("-" * 30)
            for e in cross_matches:
                title = e.get("title", e.get("slug", "?"))
                cat = e.get("category", "?")
                status = e.get("status", "?")
                source = e.get("source", "?")
                print(f"\n  {title}")
                print(f"  Category: {cat} | {status}, source: {source}")
                print(f"  Refs: {', '.join(e.get('refs', [])[:5])}")
                if e.get("discovery"):
                    print(f"  {e['discovery'][:120]}")
        except Exception as e:
            warn(f"Search: failed to render cross-cutting results: {e}")

    # Preferences
    if pref_matches:
        try:
            print(f"\nPreferences ({len(pref_matches)} matches)")
            print("-" * 30)
            for p in pref_matches:
                print(f"  [{p.get('source', '?')}] {p['text'][:120]}")
        except Exception as e:
            warn(f"Search: failed to render preference results: {e}")


def view_prefs(shadow_dir):
    """Show all preferences."""
    try:
        prefs = parse_prefs(shadow_dir)
    except Exception as e:
        error(f"Failed to parse preferences: {e}")
        return

    if not prefs:
        print("No preferences recorded yet.")
        return

    print(f"Project Preferences ({len(prefs)} total)")
    print("=" * 40)
    for p in prefs:
        try:
            source = p.get("source", "?")
            print(f"\n  [{source}] {p['text']}")
        except Exception as e:
            warn(f"Failed to render preference: {e}")


def view_labels(shadow_dir, label_filter):
    """Show discoveries filtered by label(s).

    label_filter can be a single label or comma-separated list.
    """
    try:
        filters = [l.strip().lower() for l in label_filter.split(",")]
    except Exception as e:
        error(f"Invalid label filter '{label_filter}': {e}")
        return

    try:
        all_disc = collect_all_discoveries(shadow_dir)
    except Exception as e:
        error(f"Failed to collect discoveries for label filtering: {e}")
        return

    # Also include cross-cutting discoveries with labels
    try:
        for entry in parse_cross_cutting(shadow_dir):
            if entry.get("labels"):
                all_disc.append({
                    "file": f"_cross/{entry.get('file', '?')}",
                    "symbol": entry.get("title", entry.get("slug", "?")),
                    "text": entry.get("discovery", entry.get("title", "")),
                    "status": entry.get("status", "?"),
                    "source": entry.get("source", "?"),
                    "labels": entry["labels"],
                })
    except Exception as e:
        warn(f"Failed to include cross-cutting in label search: {e}")

    matching = []
    for d in all_disc:
        try:
            disc_labels = [l.lower() for l in d.get("labels", [])]
            if any(f in disc_labels for f in filters):
                matching.append(d)
        except Exception as e:
            warn(f"Failed to check labels on discovery in "
                 f"{d.get('file', '?')}::{d.get('symbol', '?')}: {e}")

    if not matching:
        print(f"No discoveries with label(s): {', '.join(filters)}")
        return

    print(f"Discoveries with label(s): {', '.join(filters)} "
          f"({len(matching)} results)")
    print("=" * 50)

    by_label = defaultdict(list)
    for d in matching:
        for lbl in d.get("labels", []):
            if lbl.lower() in filters:
                by_label[lbl.lower()].append(d)

    for lbl in filters:
        discs = by_label.get(lbl, [])
        if not discs:
            continue
        print(f"\n[{lbl}] ({len(discs)} discoveries)")
        print("-" * 30)
        for d in discs:
            try:
                sym = d.get("symbol", "?")
                src_file = d.get("file", "?")
                print(f"  {src_file}::{sym}")
                print(f"  {d['text'][:120]}")
                print(f"  ({d.get('status', '?')}, "
                      f"source: {d.get('source', '?')})")
                all_labels = d.get("labels", [])
                other = [l for l in all_labels if l.lower() != lbl]
                if other:
                    print(f"  Also labeled: {', '.join(other)}")
            except Exception as e:
                warn(f"Failed to render labeled discovery: {e}")


def view_recent(shadow_dir, count=10):
    """Show the N most recent discoveries (by shadow file mtime).

    Collects all discoveries across all shadow files, cross-cutting entries,
    and preferences, sorts by the source file's modification time (most recent
    first), and shows the actual discovery content.
    Each data source is independent — if cross-cutting fails, per-file
    discoveries still appear.
    """
    all_items = []

    # Per-file discoveries
    try:
        for sf in get_all_shadow_files(shadow_dir):
            try:
                mtime = os.path.getmtime(sf)
                parsed = parse_shadow_file(sf)
                source_file = parsed["source_file"] or str(
                    sf.relative_to(shadow_dir)
                )
                for d in parsed["discoveries"]:
                    all_items.append({
                        "type": "discovery",
                        "file": source_file,
                        "symbol": d.get("symbol", "?"),
                        "text": d.get("text", ""),
                        "status": d.get("status", "?"),
                        "source": d.get("source", "?"),
                        "mtime": mtime,
                    })
            except Exception as e:
                warn(f"Recent: failed to process {sf}: {e}")
    except Exception as e:
        warn(f"Recent: failed to list shadow files: {e}")

    # Cross-cutting discoveries
    try:
        cross_entries = parse_cross_cutting(shadow_dir)
        cross_by_file = defaultdict(list)
        for e in cross_entries:
            cross_by_file[e["file"]].append(e)

        cross_dir = shadow_dir / "_cross"
        if cross_dir.exists():
            for cf in cross_dir.glob("*.md"):
                try:
                    mtime = os.path.getmtime(cf)
                    for e in cross_by_file.get(cf.name, []):
                        all_items.append({
                            "type": "cross-cutting",
                            "file": f"_cross/{cf.name}",
                            "symbol": e.get("title", e.get("slug", "?")),
                            "text": e.get("discovery", e.get("title", "")),
                            "status": e.get("status", "?"),
                            "source": e.get("source", "?"),
                            "mtime": mtime,
                        })
                except Exception as e:
                    warn(f"Recent: failed to process cross-cutting {cf}: {e}")
    except Exception as e:
        warn(f"Recent: failed to process cross-cutting discoveries: {e}")

    # Preferences
    try:
        prefs_path = shadow_dir / "_prefs.md"
        if prefs_path.exists():
            mtime = os.path.getmtime(prefs_path)
            for p in parse_prefs(shadow_dir):
                all_items.append({
                    "type": "preference",
                    "file": "_prefs.md",
                    "symbol": "-",
                    "text": p.get("text", ""),
                    "status": "-",
                    "source": p.get("source", "?"),
                    "mtime": mtime,
                })
    except Exception as e:
        warn(f"Recent: failed to process preferences: {e}")

    all_items.sort(key=lambda x: x.get("mtime", 0), reverse=True)

    if not all_items:
        print("No discoveries found.")
        return

    shown = all_items[:count]
    print(f"Most Recent Discoveries (top {count})")
    print("=" * 50)
    for item in shown:
        try:
            ts = datetime.fromtimestamp(
                item.get("mtime", 0)
            ).strftime("%Y-%m-%d %H:%M")
            kind = item.get("type", "?")
            sym = item.get("symbol", "?")

            print(f"\n  [{ts}] ({kind})")
            if kind == "preference":
                print(f"  {item.get('text', '')[:120]}")
                print(f"  source: {item.get('source', '?')}")
            else:
                print(f"  {item.get('file', '?')}::{sym}")
                print(f"  {item.get('text', '')[:120]}")
                print(f"  ({item.get('status', '?')}, "
                      f"source: {item.get('source', '?')})")
        except Exception as e:
            warn(f"Recent: failed to render item: {e}")


def view_top(shadow_dir, file_path, labels_filter, limit, max_chars):
    """Show the top N actionable discoveries for a single source file.

    Designed for the preToolUse hook: concise output suitable for
    inlining into additionalContext when the agent is about to mutate a
    file. Pulls from both the per-file shadow and any _cross/ entries
    whose refs touch this file.

    Ranking: verified > uncertain > refuted; within a tier, source
    order is preserved. Output is hard-capped at max_chars (the trailing
    "(...)" marker still fits).
    """
    norm = file_path.strip()
    if norm.startswith("./"):
        norm = norm[2:]
    shadow_path = shadow_dir / f"{norm}.md"
    label_set = {l.strip().lower() for l in labels_filter.split(",") if l.strip()}

    candidates = []

    if shadow_path.is_file():
        try:
            parsed = parse_shadow_file(shadow_path)
            for d in parsed.get("discoveries", []):
                disc_labels = {l.lower() for l in d.get("labels", [])}
                if label_set and not (disc_labels & label_set):
                    continue
                candidates.append({
                    "kind": "file",
                    "anchor": d.get("symbol") or "file-level",
                    "text": d.get("text", "").strip(),
                    "status": d.get("status", "?"),
                    "labels": sorted(disc_labels),
                })
        except Exception as e:
            warn(f"--top: failed parsing {shadow_path}: {e}")

    try:
        for entry in parse_cross_cutting(shadow_dir):
            refs = entry.get("refs", []) or []
            if not any(r.split("::", 1)[0].strip() == norm for r in refs):
                continue
            cross_labels = {l.lower() for l in entry.get("labels", [])}
            if label_set and not (cross_labels & label_set):
                continue
            candidates.append({
                "kind": "cross",
                "anchor": f"_cross/{entry.get('file', entry.get('slug', '?'))}",
                "text": (entry.get("discovery") or entry.get("title") or "").strip(),
                "status": entry.get("status", "?"),
                "labels": sorted(cross_labels),
            })
    except Exception as e:
        warn(f"--top: failed scanning _cross/: {e}")

    if not candidates:
        labels_disp = ",".join(sorted(label_set)) if label_set else "any"
        print(
            f"No actionable discoveries ({labels_disp}) for {norm}."
        )
        return

    tier = {"verified": 0, "uncertain": 1, "refuted": 2}
    candidates.sort(key=lambda d: tier.get(d.get("status", "?"), 3))

    shown = candidates[:limit]
    header = (
        f"Top {len(shown)} of {len(candidates)} actionable discoveries "
        f"for {norm}:"
    )
    lines = [header]
    for d in shown:
        labels = ",".join(d["labels"]) if d["labels"] else "—"
        anchor = d["anchor"]
        text = d["text"].replace("\n", " ").strip()
        lines.append(
            f"- [{labels}] `{anchor}` ({d['status']}): {text}"
        )

    out = "\n".join(lines)
    if max_chars and len(out) > max_chars:
        truncated = out[: max_chars - 6].rstrip()
        out = truncated + "\n(...)"
    print(out)


def view_check_invariants(shadow_dir):
    """Walk the shadow knowledge base and report invariant violations.

    Statically-checkable invariants from shadow-frog/SKILL.md:
      #3 (partial) Per-file 'Also involves:' uses file::symbol notation
      #4 Cross-ref back-pointers match: _cross/<slug>.md refs <->
         per-file ## Cross-References
      #5 Every ## Cross-References entry has a matching _cross/*.md

    Plus syntactic guards that catch the most common drift:
      - Symbol headings use the required backtick form
      - Discovery metadata uses valid status enum
      - Discovery metadata uses valid source enum
      - Discovery labels are from the allowed set
      - _cross/ Category field uses a known value

    Invariants #1, #2, #7 are NOT checked (would require source parsing
    and semantic match); #6 is filesystem-enforced.

    Exit 0 = clean, 1 = at least one violation. Violations print one per
    line in `path:line: kind: message` form so grep/editors can navigate.
    """
    VALID_STATUS = {"verified", "uncertain", "refuted"}
    VALID_SOURCE = {"exploration", "user", "interaction"}
    VALID_LABELS = {"bug", "performance", "security",
                    "feature-gap", "tech-debt"}
    VALID_CATEGORIES = {
        "pattern", "behavior", "edge-case", "contract",
        "performance", "intent", "warning", "history", "convention",
    }

    violations = []
    def v(path, line, kind, msg):
        violations.append(f"{path}:{line}: {kind}: {msg}")

    # Pass 1: walk per-file shadows -> collect cross-reference entries
    # they declare and validate their internal format.
    per_file_xref_targets = {}  # rel_shadow_path -> set(slug declared)
    cross_dir = shadow_dir / "_cross"
    cross_slugs_on_disk = set()
    if cross_dir.is_dir():
        try:
            cross_slugs_on_disk = {f.stem for f in cross_dir.glob("*.md")}
        except OSError as e:
            warn(f"Cannot list {cross_dir}: {e}")

    md_heading_re = re.compile(r"^(#{2,3})\s+(.*)$")
    backtick_heading_re = re.compile(r"^(#{2,3})\s+`[^`]+`\s*$")
    also_involves_re = re.compile(r"^\s*Also involves:\s*(.+)$", re.I)
    file_sym_re = re.compile(r"`([^`]+::[^`]+)`")

    for shadow_path in get_all_shadow_files(shadow_dir):
        try:
            rel = shadow_path.relative_to(shadow_dir)
        except ValueError:
            continue
        try:
            text = shadow_path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as e:
            v(rel, 0, "unreadable", str(e))
            continue

        in_cross_refs = False
        declared = set()
        for ln, raw in enumerate(text.split("\n"), 1):
            line = raw.rstrip()

            heading = md_heading_re.match(line)
            if heading:
                title = heading.group(2).strip()
                if title.lower().startswith("cross-references"):
                    in_cross_refs = True
                    continue
                in_cross_refs = False
                # Skip special headings ("File-Level Notes", "Notes", etc.)
                if (
                    title.lower().startswith("file-level")
                    or title.lower() in {"notes", "metadata"}
                ):
                    continue
                # Symbol heading must use backtick form
                if not backtick_heading_re.match(line):
                    v(rel, ln, "heading",
                      f"symbol heading must be `## `name`` or "
                      f"`### `Class.name``; got: {line[:80]}")
                continue

            if in_cross_refs and line.strip().startswith("- "):
                # Format: - [slug](.shadow/_cross/slug.md) — title
                slug_match = re.search(
                    r"_cross/([^)\s]+?)\.md", line
                )
                if slug_match:
                    declared.add(slug_match.group(1))
                else:
                    # Looser fallback: bare slug in brackets
                    alt = re.search(r"\[([^\]]+)\]", line)
                    if alt:
                        declared.add(alt.group(1).strip())

            # Discovery metadata line
            md = _DISCOVERY_META_RE.search(line)
            if md:
                status, source = md.group(1), md.group(2)
                labels_raw = md.group(3) or ""
                if status not in VALID_STATUS:
                    v(rel, ln, "enum",
                      f"status '{status}' not in {sorted(VALID_STATUS)}")
                if source not in VALID_SOURCE:
                    v(rel, ln, "enum",
                      f"source '{source}' not in {sorted(VALID_SOURCE)}")
                for lbl in (l.strip() for l in labels_raw.split(",") if l.strip()):
                    if lbl not in VALID_LABELS:
                        v(rel, ln, "enum",
                          f"label '{lbl}' not in {sorted(VALID_LABELS)}")

            # `Also involves:` must list file::symbol anchors in backticks
            ai = also_involves_re.match(line)
            if ai:
                rest = ai.group(1)
                anchors = file_sym_re.findall(rest)
                if not anchors:
                    v(rel, ln, "anchor",
                      "Also involves: needs `file::symbol` "
                      "backtick anchors")
                # Light sanity: every anchor has both file and symbol
                for a in anchors:
                    if "::" not in a or not a.split("::", 1)[1].strip():
                        v(rel, ln, "anchor",
                          f"anchor '{a}' missing symbol after ::")

        per_file_xref_targets[str(rel)] = declared

        # Invariant #5: every declared cross slug must exist on disk
        for slug in declared:
            if slug not in cross_slugs_on_disk:
                v(rel, 0, "cross-ref",
                  f"references _cross/{slug}.md but file does not exist")

    # Pass 2: walk _cross/*.md -> validate refs format + back-pointer.
    # Build the reverse map: cross_slug -> set(file::symbol it points at).
    cross_back = {}  # slug -> set(file paths it should be linked from)
    if cross_dir.is_dir():
        for cf in sorted(cross_dir.glob("*.md")):
            slug = cf.stem
            try:
                text = cf.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as e:
                v(cf.relative_to(shadow_dir), 0, "unreadable", str(e))
                continue

            rel_cf = cf.relative_to(shadow_dir)

            # Category enum check
            cat_m = re.search(r"\*\*Category\*\*:\s*(.+)", text)
            if cat_m:
                cat = cat_m.group(1).strip().lower()
                if cat not in VALID_CATEGORIES:
                    v(rel_cf, 0, "enum",
                      f"Category '{cat}' not in {sorted(VALID_CATEGORIES)}")
            else:
                v(rel_cf, 0, "schema",
                  "missing **Category**: field")

            # Discovery metadata
            md = _DISCOVERY_META_RE.search(text)
            if md:
                status, source = md.group(1), md.group(2)
                if status not in VALID_STATUS:
                    v(rel_cf, 0, "enum",
                      f"status '{status}' not in {sorted(VALID_STATUS)}")
                if source not in VALID_SOURCE:
                    v(rel_cf, 0, "enum",
                      f"source '{source}' not in {sorted(VALID_SOURCE)}")
            else:
                v(rel_cf, 0, "schema",
                  "missing trailing _(status, source: ...)_ metadata")

            # Refs must be `file::symbol` anchors
            refs_block = re.search(
                r"\*\*Refs\*\*:\s*\n((?:\s*-\s+`[^`]+`\s*\n?)+)",
                text,
            )
            if not refs_block:
                v(rel_cf, 0, "schema",
                  "missing **Refs**: block (one per line, "
                  "`- `file::symbol``)")
            else:
                anchors = file_sym_re.findall(refs_block.group(1))
                if not anchors:
                    v(rel_cf, 0, "anchor",
                      "Refs block has no `file::symbol` entries")
                for a in anchors:
                    if "::" not in a or not a.split("::", 1)[1].strip():
                        v(rel_cf, 0, "anchor",
                          f"ref '{a}' missing symbol after ::")
                    else:
                        # Convert file part to shadow path:
                        # src/foo.py -> src/foo.py.md (relative to shadow_dir)
                        file_part = a.split("::", 1)[0].strip()
                        shadow_rel = f"{file_part}.md"
                        cross_back.setdefault(slug, set()).add(shadow_rel)

    # Invariant #4 back-pointer: every file referenced by a cross slug
    # must declare that slug in its ## Cross-References.
    for slug, expected_files in cross_back.items():
        for shadow_rel in expected_files:
            declared = per_file_xref_targets.get(shadow_rel)
            if declared is None:
                v(f"_cross/{slug}.md", 0, "cross-ref",
                  f"refs {shadow_rel} but no such shadow file exists")
            elif slug not in declared:
                v(f"_cross/{slug}.md", 0, "cross-ref",
                  f"refs {shadow_rel} but that shadow's ## "
                  f"Cross-References does not link back to "
                  f"_cross/{slug}.md")

    # Output
    if not violations:
        print(f"✓ Invariants OK ({len(per_file_xref_targets)} per-file "
              f"shadows, {len(cross_slugs_on_disk)} cross-cutting "
              f"discoveries)")
        return 0

    for line in violations:
        print(line)
    print(f"\n{len(violations)} invariant violation(s) found.",
          file=sys.stderr)
    return 1


def main():
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8")
    try:
        parser = argparse.ArgumentParser(
            description="Query and browse a .shadow/ knowledge base.",
            formatter_class=argparse.RawDescriptionHelpFormatter,
        )

        # Views (mutually exclusive)
        views = parser.add_mutually_exclusive_group()
        views.add_argument(
            "--summary", action="store_true",
            help="Overview + detailed statistics (default)",
        )
        views.add_argument(
            "--search", metavar="QUERY",
            help="Universal search: files, symbols, and discovery text",
        )
        views.add_argument(
            "--prefs", action="store_true",
            help="Show project-wide preferences",
        )
        views.add_argument(
            "--recent", nargs="?", const=10, type=int, metavar="N",
            help="N most recent discoveries with content (default: 10)",
        )
        views.add_argument(
            "--labels", metavar="LABEL",
            help=(
                "Show discoveries by label "
                "(e.g., bug, security, bug,performance)"
            ),
        )
        views.add_argument(
            "--top", metavar="FILE",
            help=(
                "Top actionable discoveries for FILE (a source path "
                "like src/auth.py). Concise output for the preToolUse "
                "hook: filters to actionable labels (default: "
                "bug,security), includes both per-file and _cross/ "
                "entries that reference FILE, ranks verified first."
            ),
        )
        views.add_argument(
            "--check-invariants", action="store_true",
            help=(
                "Walk the shadow and report structural violations: "
                "missing back-pointers, dangling _cross/ refs, invalid "
                "enums, bad heading format. Exit 1 if any are found."
            ),
        )

        # Options
        parser.add_argument(
            "--shadow-dir", default=None,
            help="Path to .shadow/ directory (default: auto-detect)",
        )
        parser.add_argument(
            "--top-labels", default="bug,security", metavar="LABELS",
            help=(
                "Comma-separated labels to include in --top "
                "(default: bug,security). Pass empty string to include "
                "all labeled discoveries."
            ),
        )
        parser.add_argument(
            "--top-limit", type=int, default=3, metavar="N",
            help="Max discoveries to show in --top (default: 3)",
        )
        parser.add_argument(
            "--top-max-chars", type=int, default=600, metavar="N",
            help=(
                "Hard cap on --top total output length "
                "(default: 600). Use 0 for no cap."
            ),
        )

        args = parser.parse_args()

        # Find shadow dir
        if args.shadow_dir:
            shadow_dir = Path(args.shadow_dir)
        else:
            shadow_dir = find_shadow_dir()

        if not shadow_dir or not shadow_dir.is_dir():
            cwd = os.getcwd()
            error(
                f"No .shadow/ directory found. "
                f"Searched from: {cwd}\n"
                f"[shadow-viewer error] "
                f"Run /shadow-frog-init first to create the shadow, "
                f"or pass --shadow-dir /path/to/.shadow/ explicitly."
            )
            if args.shadow_dir:
                error(
                    f"Provided --shadow-dir '{args.shadow_dir}' does not "
                    f"exist or is not a directory."
                )
            sys.exit(1)

        # Dispatch
        if args.check_invariants:
            sys.exit(view_check_invariants(shadow_dir))
        if args.top:
            view_top(
                shadow_dir,
                args.top,
                args.top_labels,
                args.top_limit,
                args.top_max_chars,
            )
        elif args.search:
            view_search(shadow_dir, args.search)
        elif args.prefs:
            view_prefs(shadow_dir)
        elif args.labels:
            view_labels(shadow_dir, args.labels)
        elif args.recent is not None:
            view_recent(shadow_dir, args.recent)
        else:
            view_summary(shadow_dir)

    except SystemExit:
        raise
    except KeyboardInterrupt:
        error("Interrupted by user.")
        sys.exit(130)
    except Exception as e:
        error(
            f"Unexpected error: {type(e).__name__}: {e}\n"
            f"[shadow-viewer error] Full traceback:\n"
            f"{traceback.format_exc()}"
            f"This is likely a bug in shadow-viewer.py. "
            f"The shadow data may be in an unexpected format. "
            f"Try running with --shadow-dir to confirm the path, "
            f"or inspect the .shadow/ files manually."
        )
        sys.exit(1)


if __name__ == "__main__":
    main()

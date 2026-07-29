#!/usr/bin/env python3
"""Generate an interactive HTML visualization of dream experiment lineage.

Reads .shadow/_dreams/_index.md and experiment reports to produce a
self-contained HTML file with:
  - Stats dashboard (totals, categories, depth)
  - Compounding chains tab (tree cards with expandable reports)
  - Fresh experiments tab (grid grouped by category)
  - Full tree tab (compact overview of entire lineage)

Usage:
    python3 dream-lineage.py                     # writes dream-lineage.html
    python3 dream-lineage.py -o custom-name.html # custom output path
    python3 dream-lineage.py --shadow-dir /path/to/.shadow
"""

import argparse
import html as htmlmod
import json
import os
import re
import sys
from collections import defaultdict


# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

def parse_args():
    p = argparse.ArgumentParser(description="Dream lineage HTML visualizer")
    p.add_argument("-o", "--output", default="dream-lineage.html",
                   help="Output HTML file path (default: dream-lineage.html)")
    p.add_argument("--shadow-dir", default=None,
                   help="Path to .shadow/ directory (default: auto-detect)")
    return p.parse_args()


# ---------------------------------------------------------------------------
# Data loading
# ---------------------------------------------------------------------------

CAT_COLORS = {
    "investigation": "#4CAF50", "bug hunting": "#F44336",
    "feature design": "#2196F3", "refactoring": "#FF9800",
    "optimization": "#9C27B0", "security audit": "#E91E63",
    "unknown": "#607D8B",
}
VERDICT_MAP = {
    "useful": "✅", "confirmed": "✅", "dead_end": "❌", "unknown": "—",
}


def find_shadow_dir(hint=None):
    if hint and os.path.isdir(hint):
        return hint
    for candidate in [".shadow", os.path.join(os.getcwd(), ".shadow")]:
        if os.path.isdir(candidate):
            return candidate
    print("ERROR: .shadow/ directory not found. Use --shadow-dir.", file=sys.stderr)
    sys.exit(1)


def load_index(shadow_dir):
    """Parse _dreams/_index.md into structured data."""
    index_path = os.path.join(shadow_dir, "_dreams", "_index.md")
    if not os.path.exists(index_path):
        print(f"ERROR: {index_path} not found.", file=sys.stderr)
        sys.exit(1)

    children = defaultdict(list)
    meta = {}
    branch_by_slug = {}

    # First pass: collect all branches and build slug index
    with open(index_path, encoding="utf-8") as f:
        for line in f:
            parts = [p.strip() for p in line.split("|")]
            if len(parts) < 8:
                continue
            did, cat, verdict, title, branch, parent, tip = parts[1:8]
            if not did or did.startswith("-") or did == "dream_id":
                continue
            short = did.split("Z-")[-1] if "Z-" in did else did
            meta[branch] = {
                "short": short, "cat": cat, "verdict": verdict,
                "title": title.strip(), "did": did, "tip": tip,
            }
            slug_match = re.search(r"t\d+-", branch)
            if slug_match:
                branch_by_slug[branch[slug_match.start():]] = branch

    # Second pass: resolve parent references (handle timestamp mismatches)
    with open(index_path, encoding="utf-8") as f:
        for line in f:
            parts = [p.strip() for p in line.split("|")]
            if len(parts) < 8:
                continue
            did, cat, verdict, title, branch, parent, tip = parts[1:8]
            if not did or did.startswith("-") or did == "dream_id":
                continue
            resolved = parent
            if parent != "main" and parent not in meta:
                m = re.search(r"t\d+-", parent)
                if m and parent[m.start():] in branch_by_slug:
                    resolved = branch_by_slug[parent[m.start():]]
            if branch not in children[resolved]:
                children[resolved].append(branch)

    # Third pass: check manifest.json and report body for better parent info
    dreams_dir = os.path.join(shadow_dir, "_dreams")
    for branch in list(children.get("main", [])):
        info = meta.get(branch, {})
        did = info.get("did", "")
        if not did:
            continue
        mp = ""
        # Try manifest.json first
        manifest_path = os.path.join(dreams_dir, did, "manifest.json")
        if os.path.exists(manifest_path):
            try:
                with open(manifest_path, encoding="utf-8") as f:
                    mdata = json.load(f)
                mp = mdata.get("parent_branch", "")
            except Exception:
                pass
        # Try report body for parent references
        if not mp or mp == "main":
            report_path = os.path.join(dreams_dir, did, "report.md")
            if os.path.exists(report_path):
                try:
                    with open(report_path, encoding="utf-8") as f:
                        head = f.read(2000)
                    # Check builds_on in frontmatter
                    m = re.search(r"builds_on:\s*\[?\s*[\"']?([^\]\"'\n,]+)", head)
                    if m:
                        mp = m.group(1).strip().strip("\"'")
                except Exception:
                    pass
        if not mp or mp == "main":
            continue
        # Resolve via slug matching
        resolved = mp
        if mp not in meta:
            m = re.search(r"t\d+-", mp)
            if m and mp[m.start():] in branch_by_slug:
                resolved = branch_by_slug[mp[m.start():]]
            else:
                # Try matching just tNN prefix
                m = re.search(r"(t\d+)", mp)
                if m:
                    prefix = m.group(1) + "-"
                    for slug, br in branch_by_slug.items():
                        if slug.startswith(prefix):
                            resolved = br
                            break
                    else:
                        continue
                else:
                    continue
        if resolved == branch:
            continue
        # Re-parent: remove from main, add under resolved parent
        try:
            children["main"].remove(branch)
            if branch not in children[resolved]:
                children[resolved].append(branch)
        except ValueError:
            pass

    return meta, children


def load_reports(shadow_dir, meta):
    """Read report content and manifest metadata for each experiment."""
    for branch, info in meta.items():
        did = info["did"]
        report_path = os.path.join(shadow_dir, "_dreams", did, "report.md")
        info["full_report"] = ""
        info["tests"] = ""
        info["discoveries_count"] = 0

        if os.path.exists(report_path):
            try:
                with open(report_path, encoding="utf-8") as f:
                    content = f.read()
                body = content
                if content.startswith("---"):
                    fm_end = content.find("---", 3)
                    if fm_end > 0:
                        body = content[fm_end + 3:].strip()
                info["full_report"] = body
            except Exception:
                pass

        manifest_path = os.path.join(shadow_dir, "_dreams", did, "manifest.json")
        if os.path.exists(manifest_path):
            try:
                with open(manifest_path, encoding="utf-8") as f:
                    mdata = json.load(f)
                info["tests"] = str(mdata.get("tests_passed", mdata.get("test_count", "")))
                info["discoveries_count"] = len(mdata.get("discoveries", []))
            except Exception:
                pass


# ---------------------------------------------------------------------------
# HTML generation helpers
# ---------------------------------------------------------------------------

def md_to_html(md):
    """Convert markdown to HTML, handling code blocks, lists, tables, etc."""
    # Extract fenced code blocks first (before escaping)
    code_blocks = []
    def stash_code(m):
        lang = m.group(1) or ""
        code = htmlmod.escape(m.group(2))
        code_blocks.append(f'<pre><code>{code}</code></pre>')
        return f"\x00CODE{len(code_blocks) - 1}\x00"
    s = re.sub(r"```(\w*)\n(.*?)```", stash_code, md, flags=re.S)

    s = htmlmod.escape(s)

    # Headings
    s = re.sub(r"^### (.+)$", r"<h4>\1</h4>", s, flags=re.M)
    s = re.sub(r"^## (.+)$", r"<h3>\1</h3>", s, flags=re.M)
    s = re.sub(r"^# (.+)$", r"<h2>\1</h2>", s, flags=re.M)

    # Bold (allow multiline)
    s = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", s, flags=re.S)

    # Inline code
    s = re.sub(r"`([^`\n]+)`", r"<code>\1</code>", s)

    # Blockquotes
    s = re.sub(r"^&gt; (.+)$", r"<blockquote>\1</blockquote>", s, flags=re.M)

    # Tables: detect header + separator + rows
    def render_table(m):
        lines = m.group(0).strip().split("\n")
        headers = [c.strip() for c in lines[0].split("|") if c.strip()]
        rows_html = "<tr>" + "".join(f"<th>{h}</th>" for h in headers) + "</tr>"
        for row_line in lines[2:]:
            cells = [c.strip() for c in row_line.split("|") if c.strip()]
            rows_html += "<tr>" + "".join(f"<td>{c}</td>" for c in cells) + "</tr>"
        return f"<table>{rows_html}</table>"
    s = re.sub(r"^(\|.+\|)\n(\|[-| :]+\|)\n((?:\|.+\|\n?)+)", render_table, s, flags=re.M)

    # Numbered lists: consecutive lines starting with N.
    def render_ol(m):
        items = re.findall(r"^\d+\.\s+(.+)$", m.group(0), re.M)
        return "<ol>" + "".join(f"<li>{it}</li>" for it in items) + "</ol>"
    s = re.sub(r"(?:^\d+\.\s+.+$\n?){2,}", render_ol, s, flags=re.M)
    # Single numbered item
    s = re.sub(r"^(\d+)\.\s+(.+)$", r"<ol start='\1'><li>\2</li></ol>", s, flags=re.M)

    # Unordered lists (including nested via indentation). Consecutive
    # `- item` lines are wrapped in a single <ul>; indented items get
    # class='nested' so the panel-body CSS (li.nested margin-left: 32px)
    # renders the nesting visually. Previous implementation emitted bare
    # <li> tags with no <ul> wrapper, producing structurally invalid HTML.
    def render_ul(m):
        items_html = []
        for line in m.group(0).split('\n'):
            ml = re.match(r"^( *)- (.+)$", line.rstrip())
            if not ml:
                continue
            cls = " class='nested'" if len(ml.group(1)) >= 2 else ""
            items_html.append(f"<li{cls}>{ml.group(2)}</li>")
        return "<ul>" + "".join(items_html) + "</ul>"
    s = re.sub(r"(?:^ *- .+$\n?){1,}", render_ul, s, flags=re.M)

    # Paragraphs
    s = re.sub(r"\n\n+", "</p><p>", s)

    # Restore code blocks
    for i, block in enumerate(code_blocks):
        s = s.replace(f"\x00CODE{i}\x00", block)

    return f"<p>{s}</p>"


def stable_id(branch):
    """Generate a stable template ID from a branch name."""
    return "rpt-" + re.sub(r"[^a-zA-Z0-9]", "-", branch)


def flatten_chain(branch, meta, children, depth=0):
    """Flatten a chain tree into an ordered list of (branch, depth) tuples."""
    result = [(branch, depth)]
    for kid in children.get(branch, []):
        result.extend(flatten_chain(kid, meta, children, depth + 1))
    return result


def node_html(branch, meta, children, with_report=True):
    """Render a single node as a flat timeline row."""
    info = meta.get(branch, {})
    short = info.get("short", branch)
    cat = info.get("cat", "unknown")
    color = CAT_COLORS.get(cat, "#607D8B")
    verdict = VERDICT_MAP.get(info.get("verdict", ""), "—")
    title = htmlmod.escape(info.get("title", ""))
    tests = info.get("tests", "")
    disc = info.get("discoveries_count", 0)
    full_report = info.get("full_report", "")
    depth = info.get("_depth", 0)

    sid = stable_id(branch)

    test_badge = f'<span class="badge test">{tests} tests</span>' if tests else ""
    disc_badge = f'<span class="badge disc">{disc} disc</span>' if disc else ""

    report_btn = ""
    if with_report and full_report:
        report_btn = (
            f' <button class="report-btn" '
            f'onclick="showPanel(\'{sid}\')">📄</button>'
        )

    return (
        f'<div class="tl-row" style="--node-color: {color}">'
        f'<div class="tl-depth" style="background:{color}">{depth}</div>'
        f'<div class="tl-content">'
        f'<div class="node-header">'
        f'<span class="name">{short}</span>'
        f'<span class="verdict">{verdict}</span>'
        f'{test_badge}{disc_badge}'
        f'{report_btn}'
        f'</div>'
        f'<div class="title">{title}</div>'
        f'</div>'
        f'</div>'
    )


def compact_node(branch, meta, children, prefix="", is_last=True):
    """Render a single line in the compact tree view."""
    info = meta.get(branch, {})
    short = info.get("short", branch)
    cat = info.get("cat", "unknown")
    color = CAT_COLORS.get(cat, "#607D8B")
    verdict = VERDICT_MAP.get(info.get("verdict", ""), "—")
    title = htmlmod.escape(info.get("title", ""))
    tests = info.get("tests", "")
    report = info.get("full_report", "")

    connector = "└── " if is_last else "├── "
    test_info = f' <span class="ct-test">{tests}t</span>' if tests else ""

    sid = stable_id(branch)
    report_btn = ""
    if report:
        report_btn = (
            f' <button class="report-btn ct-report-btn" '
            f'onclick="showPanel(\'{sid}\')">📄</button>'
        )

    line = (
        f'<div class="ct-line">'
        f'<span class="ct-tree">{htmlmod.escape(prefix)}{connector}</span>'
        f'<span class="ct-name" style="color:{color}">{short}</span>'
        f'<span class="ct-verdict">{verdict}</span>'
        f'{test_info}'
        f'<span class="ct-title">{title}</span>'
        f'{report_btn}'
        f'</div>'
    )

    kids = children.get(branch, [])
    for i, kid in enumerate(kids):
        ext = "      " if is_last else "│     "
        line += compact_node(kid, meta, children, prefix + ext, i == len(kids) - 1)
    return line


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def tree_depth(node, children, _seen=None):
    """Depth of the subtree rooted at `node`.

    `_seen` guards against cycles in malformed indices (self-parent
    or A↔B loops). On re-visit we treat the node as terminal and
    return 0 — better to underestimate depth than to crash with
    RecursionError on bad input.
    """
    if _seen is None:
        _seen = set()
    if node in _seen:
        return 0
    _seen = _seen | {node}
    kids = children.get(node, [])
    return (1 + max(tree_depth(k, children, _seen) for k in kids)) if kids else 0


def generate_html(shadow_dir, output_path):
    meta, children = load_index(shadow_dir)
    load_reports(shadow_dir, meta)

    total = len(meta)
    compound = sum(1 for p in children if p != "main" for _ in children[p])

    # Separate chains vs fresh
    chain_roots = []
    fresh_leaves = []
    for b in children.get("main", []):
        d = tree_depth(b, children)
        if d >= 1:
            chain_roots.append({"branch": b, "depth": d})
        else:
            fresh_leaves.append(b)
    chain_roots.sort(key=lambda x: -x["depth"])

    max_depth = max((r["depth"] for r in chain_roots), default=0) + 1

    # Category counts
    cat_counts = defaultdict(int)
    for info in meta.values():
        cat_counts[info.get("cat", "unknown")] += 1

    # Session count (unique date-hour groups)
    sessions = set()
    for info in meta.values():
        did = info.get("did", "")
        m = re.match(r"(\d{8}-\d{4})", did)
        if m:
            sessions.add(m.group(1))

    # --- Tab 1: Compounding Chains ---
    chains_html = ""
    for root_info in chain_roots:
        branch = root_info["branch"]
        depth = root_info["depth"]
        flat = flatten_chain(branch, meta, children)
        # Set depth on each node's meta for rendering
        for b, d in flat:
            if b in meta:
                meta[b]["_depth"] = d
        nodes_html = "".join(node_html(b, meta, children, with_report=True)
                             for b, _ in flat)
        chains_html += (
            f'<div class="chain">'
            f'<div class="chain-header">Depth {depth + 1} chain · {len(flat)} experiments</div>'
            f'{nodes_html}'
            f'</div>'
        )

    # --- Tab 2: Fresh Experiments ---
    fresh_by_cat = defaultdict(list)
    for b in fresh_leaves:
        cat = meta.get(b, {}).get("cat", "unknown")
        if b in meta:
            meta[b]["_depth"] = 0
        fresh_by_cat[cat].append(b)

    fresh_html = ""
    for cat in ["investigation", "bug hunting", "feature design", "refactoring",
                 "optimization", "security audit", "unknown"]:
        branches = fresh_by_cat.get(cat, [])
        if not branches:
            continue
        color = CAT_COLORS.get(cat, "#607D8B")
        fresh_html += (
            f'<div class="fresh-group">'
            f'<div class="fresh-header" style="color:{color}">{cat.title()} ({len(branches)})</div>'
            f'<div class="fresh-grid">'
        )
        for b in branches:
            fresh_html += node_html(b, meta, children, with_report=True)
        fresh_html += "</div></div>"

    # --- Tab 3: Full Tree (compact, sorted deepest-first) ---
    tree_html = '<div class="compact-tree"><div class="ct-line"><span class="ct-root">🌳 main</span></div>'
    main_kids = sorted(
        children.get("main", []),
        key=lambda b: tree_depth(b, children),
        reverse=True,
    )
    for i, b in enumerate(main_kids):
        tree_html += compact_node(b, meta, children, "", i == len(main_kids) - 1)
    tree_html += "</div>"

    # --- Category stats bar ---
    cat_bar_html = ""
    for cat in ["investigation", "bug hunting", "feature design", "refactoring",
                 "optimization", "security audit", "unknown"]:
        cnt = cat_counts.get(cat, 0)
        if cnt == 0:
            continue
        color = CAT_COLORS.get(cat, "#607D8B")
        cat_bar_html += (
            f'<div class="cat-stat">'
            f'<span class="legend-dot" style="background:{color}"></span>'
            f'{cat.title()}: <strong>{cnt}</strong>'
            f'</div>'
        )

    # Verdict legend
    verdict_counts = {}
    for info in meta.values():
        v = info.get("verdict", "unknown")
        verdict_counts[v] = verdict_counts.get(v, 0) + 1
    verdict_bar_html = ""
    useful_cnt = verdict_counts.get("useful", 0) + verdict_counts.get("confirmed", 0)
    for symbol, label, cnt in [
        ("✅", "Useful", useful_cnt),
        ("❌", "Dead End", verdict_counts.get("dead_end", 0)),
        ("—", "Unknown", verdict_counts.get("unknown", 0) + verdict_counts.get("---", 0)),
    ]:
        if cnt == 0:
            continue
        verdict_bar_html += (
            f'<div class="cat-stat">'
            f'{symbol} {label}: <strong>{cnt}</strong>'
            f'</div>'
        )

    # --- Global report templates (one per experiment, shared by all tabs) ---
    templates_html = ""
    for branch, info in meta.items():
        report = info.get("full_report", "")
        if not report:
            continue
        sid = stable_id(branch)
        short = htmlmod.escape(info.get("short", branch))
        verdict = VERDICT_MAP.get(info.get("verdict", ""), "—")
        title = htmlmod.escape(info.get("title", ""))
        templates_html += (
            f'<template id="{sid}">'
            f'<h2>{short}</h2>'
            f'<div class="panel-meta">{verdict} {title}</div>'
            f'{md_to_html(report)}'
            f'</template>\n'
        )

    page = TEMPLATE.format(
        total=total, compound=compound, fresh=total - compound,
        sessions=len(sessions), chains=len(chain_roots), max_depth=max_depth,
        cat_bar=cat_bar_html, verdict_bar=verdict_bar_html,
        chains_html=chains_html, chain_count=len(chain_roots),
        fresh_html=fresh_html, fresh_count=len(fresh_leaves),
        tree_html=tree_html, tree_count=total,
        templates=templates_html,
    )

    with open(output_path, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"Wrote {output_path} ({os.path.getsize(output_path):,} bytes)")
    print(f"  {total} experiments, {len(chain_roots)} chains (max depth {max_depth}), "
          f"{compound} compounding, {total - compound} fresh")


# ---------------------------------------------------------------------------
# HTML template
# ---------------------------------------------------------------------------

TEMPLATE = '''<!DOCTYPE html>
<html><head>
<meta charset="utf-8">
<title>🐸 Dream Lineage</title>
<style>
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
         background: #0d1117; color: #c9d1d9; padding: 24px; line-height: 1.5; }}
  h1 {{ color: #58a6ff; font-size: 22px; margin-bottom: 8px; }}
  .stats {{ display: flex; gap: 12px; margin: 12px 0 16px; flex-wrap: wrap; }}
  .stat {{ background: #161b22; border: 1px solid #30363d; border-radius: 6px; padding: 8px 16px; }}
  .stat .num {{ font-size: 20px; font-weight: 700; color: #58a6ff; }}
  .stat .label {{ font-size: 11px; color: #8b949e; text-transform: uppercase; letter-spacing: .5px; }}
  .cat-bar {{ display: flex; gap: 14px; margin: 0 0 16px; flex-wrap: wrap; }}
  .cat-stat {{ display: flex; align-items: center; gap: 4px; font-size: 12px; color: #8b949e; }}
  .cat-stat strong {{ color: #c9d1d9; }}
  .legend-dot {{ width: 10px; height: 10px; border-radius: 50%; display: inline-block; }}

  /* Tabs */
  .tab-bar {{ display: flex; gap: 2px; margin: 16px 0 0; }}
  .tab {{ padding: 8px 16px; background: #161b22; border: 1px solid #30363d; border-bottom: none;
          border-radius: 6px 6px 0 0; cursor: pointer; font-size: 13px; color: #8b949e; }}
  .tab.active {{ background: #0d1117; color: #e6edf3; border-color: #58a6ff; }}
  .tab-content {{ display: none; padding-top: 16px; }}
  .tab-content.active {{ display: block; }}

  /* Chain cards */
  .chains {{ display: grid; grid-template-columns: repeat(3, 1fr); gap: 16px; }}
  .chain {{ background: #161b22; border: 1px solid #30363d; border-radius: 8px; padding: 14px; }}
  .chain-header {{ font-size: 11px; color: #8b949e; text-transform: uppercase;
                    letter-spacing: .5px; margin-bottom: 8px; }}

  /* Timeline rows (chain + fresh tabs) */
  .tl-row {{ display: flex; gap: 8px; align-items: flex-start; padding: 5px 0;
              border-bottom: 1px solid #21262d; }}
  .tl-row:last-child {{ border-bottom: none; }}
  .tl-depth {{ flex-shrink: 0; width: 22px; height: 22px; border-radius: 50%;
                display: flex; align-items: center; justify-content: center;
                font-size: 10px; font-weight: 700; color: #0d1117; margin-top: 2px; }}
  .tl-content {{ flex: 1; min-width: 0; }}
  .node-header {{ display: flex; align-items: center; gap: 5px; flex-wrap: wrap; }}
  .icon {{ font-size: 14px; }}
  .name {{ font-weight: 600; font-size: 13px; color: #e6edf3;
            font-family: "SF Mono", "Fira Code", monospace; }}
  .verdict {{ font-size: 13px; }}
  .badge {{ font-size: 10px; padding: 1px 6px; border-radius: 10px; font-weight: 500; }}
  .badge.test {{ background: #1f3d2a; color: #3fb950; }}
  .badge.disc {{ background: #2a1f3d; color: #a371f7; }}
  .title {{ font-size: 12px; color: #8b949e; margin-top: 1px; }}

  /* Report button (📄 icon on each node) */
  .report-btn {{ background: none; border: 1px solid #30363d; color: #58a6ff; font-size: 11px;
                  padding: 1px 6px; border-radius: 4px; cursor: pointer; font-family: inherit;
                  line-height: 1; }}
  .report-btn:hover {{ background: #161b22; border-color: #58a6ff; }}
  .ct-report-btn {{ font-size: 10px; padding: 0 4px; margin-left: 4px; vertical-align: middle; }}

  /* Slide-out detail panel */
  .panel-overlay {{ display: none; position: fixed; top: 0; right: 0; bottom: 0;
                     width: 50vw; min-width: 420px; max-width: 700px; background: #161b22;
                     border-left: 2px solid #58a6ff; z-index: 100; overflow-y: auto;
                     padding: 20px 24px; box-shadow: -4px 0 24px rgba(0,0,0,0.5); }}
  .panel-overlay.open {{ display: block; }}
  .panel-close {{ position: sticky; top: 0; float: right; background: #21262d; border: 1px solid #30363d;
                   color: #c9d1d9; font-size: 16px; width: 32px; height: 32px; border-radius: 6px;
                   cursor: pointer; display: flex; align-items: center; justify-content: center;
                   z-index: 101; }}
  .panel-close:hover {{ background: #30363d; color: #f0f6fc; }}
  .panel-meta {{ font-size: 13px; color: #8b949e; margin: 4px 0 12px; }}
  .panel-body h2 {{ font-size: 16px; color: #e6edf3; margin: 10px 0 6px; border: none; padding: 0; }}
  .panel-body h3 {{ font-size: 14px; color: #c9d1d9; margin: 8px 0 4px; }}
  .panel-body h4 {{ font-size: 13px; color: #8b949e; margin: 6px 0 2px; }}
  .panel-body code {{ background: #0d1117; padding: 1px 4px; border-radius: 3px;
                       font-size: 12px; color: #e6edf3; }}
  .panel-body pre {{ background: #0d1117; padding: 10px; border-radius: 6px; font-size: 12px;
                      overflow-x: auto; margin: 6px 0; color: #c9d1d9; white-space: pre-wrap; }}
  .panel-body pre code {{ background: none; padding: 0; }}
  .panel-body strong {{ color: #c9d1d9; }}
  .panel-body li {{ margin-left: 16px; margin-bottom: 3px; color: #8b949e; font-size: 13px; }}
  .panel-body ol {{ margin: 6px 0; padding-left: 24px; color: #8b949e; }}
  .panel-body li.nested {{ margin-left: 32px; }}
  .panel-body table {{ border-collapse: collapse; margin: 8px 0; font-size: 12px; width: 100%; }}
  .panel-body th {{ background: #161b22; border: 1px solid #30363d; padding: 4px 8px;
                     text-align: left; color: #c9d1d9; font-weight: 600; }}
  .panel-body td {{ border: 1px solid #30363d; padding: 4px 8px; color: #8b949e; }}
  .panel-body blockquote {{ border-left: 3px solid #30363d; padding-left: 12px;
                             margin: 6px 0; color: #8b949e; font-style: italic; }}
  .panel-body p {{ margin-bottom: 8px; font-size: 13px; color: #8b949e; line-height: 1.6; }}

  /* Fresh experiments grid */
  .fresh-group {{ margin-bottom: 16px; }}
  .fresh-header {{ font-size: 14px; font-weight: 600; margin-bottom: 8px; }}
  .fresh-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(320px, 1fr)); gap: 8px; }}

  /* Compact full tree */
  .compact-tree {{ background: #161b22; border: 1px solid #30363d; border-radius: 8px;
                     padding: 16px; font-family: "SF Mono", "Fira Code", monospace;
                     font-size: 12px; line-height: 1.6; overflow-x: auto; }}
  .ct-line {{ white-space: nowrap; }}
  .ct-root {{ font-weight: 700; font-size: 14px; color: #e6edf3; }}
  .ct-tree {{ color: #484f58; white-space: pre; }}
  .ct-name {{ font-weight: 600; }}
  .ct-verdict {{ margin: 0 2px; }}
  .ct-test {{ font-size: 10px; color: #3fb950; margin: 0 4px; }}
  .ct-title {{ color: #6e7681; font-family: -apple-system, sans-serif; font-size: 11px;
                margin-left: 6px; }}
</style>
</head><body>
<h1>🐸 Dream Lineage</h1>
<div class="stats">
  <div class="stat"><div class="num">{total}</div><div class="label">Experiments</div></div>
  <div class="stat"><div class="num">{compound}</div><div class="label">Compounding</div></div>
  <div class="stat"><div class="num">{fresh}</div><div class="label">Fresh</div></div>
  <div class="stat"><div class="num">{sessions}</div><div class="label">Sessions</div></div>
  <div class="stat"><div class="num">{chains}</div><div class="label">Chains</div></div>
  <div class="stat"><div class="num">{max_depth}</div><div class="label">Max Depth</div></div>
</div>
<div class="cat-bar">{cat_bar}</div>
<div class="cat-bar">{verdict_bar}</div>
<p style="font-size:12px;color:#6e7681;margin-bottom:4px">
  Click 📄 on any node to view its full experiment report in the side panel.
</p>

<div class="tab-bar">
  <div class="tab active" onclick="switchTab('chains')">🌳 Chains ({chain_count})</div>
  <div class="tab" onclick="switchTab('fresh')">📋 Fresh ({fresh_count})</div>
  <div class="tab" onclick="switchTab('tree')">🗂️ Full Tree ({tree_count})</div>
</div>

<div id="chains" class="tab-content active">
  <div class="chains">{chains_html}</div>
</div>

<div id="fresh" class="tab-content">
  {fresh_html}
</div>

<div id="tree" class="tab-content">
  {tree_html}
</div>

<!-- Global report templates -->
{templates}

<!-- Slide-out report panel -->
<div id="report-panel" class="panel-overlay">
  <button class="panel-close" onclick="closePanel()">✕</button>
  <div id="panel-body" class="panel-body"></div>
</div>

<script>
function switchTab(id) {{
  document.querySelectorAll('.tab-content').forEach(e => e.classList.remove('active'));
  document.querySelectorAll('.tab').forEach(e => e.classList.remove('active'));
  document.getElementById(id).classList.add('active');
  event.target.classList.add('active');
}}
function showPanel(templateId) {{
  const tmpl = document.getElementById(templateId);
  if (!tmpl) return;
  const panel = document.getElementById('report-panel');
  const body = document.getElementById('panel-body');
  body.innerHTML = tmpl.innerHTML;
  panel.classList.add('open');
}}
function closePanel() {{
  document.getElementById('report-panel').classList.remove('open');
}}
document.addEventListener('keydown', function(e) {{
  if (e.key === 'Escape') closePanel();
}});
</script>
</body></html>'''


if __name__ == "__main__":
    args = parse_args()
    shadow_dir = find_shadow_dir(args.shadow_dir)
    generate_html(shadow_dir, args.output)

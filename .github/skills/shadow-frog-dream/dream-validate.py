#!/usr/bin/env python3
"""Validate dream artifacts before commit.

Usage: python3 dream-validate.py DREAM_ID [WORKTREE_DIR]
       python3 dream-validate.py --help

Checks:
  1. No flat files (subdirectory format required)
  2. Dream subdirectory exists
  3. Required files exist (report.md, manifest.json, patch.diff)
  4. patch.diff is non-empty (completion criterion #1)
  5. Report frontmatter dream_id matches
  6. Manifest dream_id matches
  7. Required manifest fields present
  8. Category and verdict validation
  9. Discovery `op` is `add` (update/refute not yet supported by reconciler)
 10. Discoveries in manifest are mirrored into per-file shadows on the
     dream branch (the reconciler ports manifest entries into main, but
     the documented workflow also requires updating branch shadows so
     human PR reviewers can read the discoveries in context)
 11. Non-blocking label-triage warnings (bug/security/performance signal
     phrases in discovery text without matching labels)

Exits 0 on success, 1 on ANY validation failure.
This is the hard gate — agents MUST NOT commit/push if this fails.
"""

import json
import os
import re
import subprocess
import sys


def main():
    for _stream in (sys.stdout, sys.stderr):
        if hasattr(_stream, "reconfigure"):
            _stream.reconfigure(encoding="utf-8")
    args = sys.argv[1:]

    if not args or args[0] in ('--help', '-h'):
        print(__doc__)
        sys.exit(0 if args else 1)

    dream_id = args[0]
    worktree = args[1] if len(args) > 1 else os.getcwd()

    errors = []
    warnings = []
    dream_dir = os.path.join(worktree, '.shadow', '_dreams', dream_id)

    # 1. Check for flat files (wrong format)
    for ext in ['.md', '.manifest.json', '.patch.diff', '.diff']:
        flat = os.path.join(worktree, '.shadow', '_dreams', dream_id + ext)
        if os.path.isfile(flat):
            errors.append(f"Flat file found: .shadow/_dreams/{dream_id}{ext}")
            errors.append(f"MUST use subdirectory: .shadow/_dreams/{dream_id}/")

    # 2. Check subdirectory exists
    if not os.path.isdir(dream_dir):
        errors.append(f"Missing dream subdirectory .shadow/_dreams/{dream_id}/")
        errors.append(f"Create with: mkdir -p .shadow/_dreams/{dream_id}")
        for e in errors:
            print(f"ERROR: {e}")
        sys.exit(1)

    # 3. Check required files
    for required in ['report.md', 'manifest.json', 'patch.diff']:
        path = os.path.join(dream_dir, required)
        if not os.path.isfile(path):
            errors.append(f"Missing .shadow/_dreams/{dream_id}/{required}")

    if errors:
        for e in errors:
            print(f"ERROR: {e}")
        sys.exit(1)

    # 4. Enforce non-empty patch.diff (completion criterion #1)
    patch_path = os.path.join(dream_dir, 'patch.diff')
    patch_bytes = os.path.getsize(patch_path)
    if patch_bytes == 0:
        errors.append(
            f"patch.diff is empty — completion criterion #1 requires "
            f"code was written or modified. Either implement something, "
            f"or delete this dream and choose a different task."
        )
    else:
        # Non-empty is not enough: whitespace-only or a stray newline must
        # not count as "code was written". Require a real unified-diff marker.
        with open(patch_path, encoding='utf-8', errors='replace') as pf:
            patch_text = pf.read()
        if not re.search(r'(?m)^(diff --git |--- |\+\+\+ |@@ )', patch_text):
            errors.append(
                "patch.diff has content but no unified-diff markers "
                "(`diff --git`, `---`, `+++`, or `@@` hunk headers). It does "
                "not look like a real code diff — regenerate it with "
                "`git diff <base_commit>..HEAD -- . ':!.shadow'` or delete "
                "this dream."
            )

    # 5. Validate report dream_id
    report_path = os.path.join(dream_dir, 'report.md')
    with open(report_path, encoding="utf-8") as f:
        content = f.read()
    m = re.match(r'^\ufeff?\s*---\r?\n(.*?)\r?\n---', content, re.S)
    if m:
        dm = re.search(r'^dream_id:\s*["\']?(.+?)["\']?\s*$', m.group(1), re.M)
        report_did = dm.group(1) if dm else ''
    else:
        report_did = ''

    if report_did != dream_id:
        errors.append(
            f"report.md dream_id mismatch: '{report_did}' (expected '{dream_id}')"
        )
        errors.append("REWRITE the report with the correct dream_id.")

    # 6. Validate manifest
    manifest_path = os.path.join(dream_dir, 'manifest.json')
    try:
        with open(manifest_path, encoding="utf-8") as f:
            manifest = json.load(f)
    except json.JSONDecodeError as e:
        errors.append(f"manifest.json is invalid JSON: {e}")
        for e in errors:
            print(f"ERROR: {e}")
        sys.exit(1)

    manifest_did = manifest.get('dream_id', '')
    if manifest_did != dream_id:
        errors.append(
            f"manifest.json dream_id mismatch: '{manifest_did}' (expected '{dream_id}')"
        )
        errors.append("REWRITE the manifest with the correct dream_id.")

    # 7. Check required fields
    required_fields = [
        'dream_id', 'branch', 'parent_branch', 'category', 'verdict', 'title'
    ]
    missing = [f for f in required_fields if not manifest.get(f)]
    if missing:
        errors.append(f"manifest.json missing required fields: {missing}")

    # 8. Validate category and verdict values
    valid_cats = {
        'investigation', 'bug hunting', 'feature design',
        'refactoring', 'optimization', 'security audit'
    }
    cat = manifest.get('category', '').lower()
    if cat and cat not in valid_cats:
        errors.append(f'Invalid category "{manifest.get("category")}". Must be one of: {valid_cats}')

    valid_verdicts = {'useful', 'dead_end'}
    verdict = manifest.get('verdict', '').lower()
    if verdict and verdict not in valid_verdicts:
        errors.append(f'Invalid verdict "{manifest.get("verdict")}". Must be one of: {valid_verdicts}')

    # 9. Validate discovery `op` values — reconciler currently only
    # implements `add`. update/refute are reserved for future use; allowing
    # them through silently corrupts main's shadow because the reconciler
    # appends them as new discoveries instead of mutating the original.
    discoveries = manifest.get('discoveries', []) or []
    # Normalize bare-string discoveries to dicts, mirroring the reconciler
    # (dream-reconcile.py merge_discoveries) so validate accepts exactly the
    # manifests the reconciler does instead of crashing on str entries.
    discoveries = [
        {'text': d} if isinstance(d, str) else d
        for d in discoveries
    ]
    for i, disc in enumerate(discoveries):
        if not isinstance(disc, dict):
            errors.append(
                f'discoveries[{i}] must be a string or object, got '
                f'{type(disc).__name__}.'
            )
            continue
        op = (disc.get('op') or 'add').lower()
        if op != 'add':
            errors.append(
                f'discoveries[{i}].op = "{op}" — only "add" is supported '
                f'by the reconciler today. Drop the op field (defaults to '
                f'"add"), or split this into a meditate session.'
            )

    # 10. Discoveries must be mirrored into per-file shadows on the dream
    # branch. The reconciler reads manifest entries directly when merging
    # into main, so the discoveries themselves are NOT lost — but the
    # documented dream workflow also requires updating per-file shadows
    # so human PR reviewers can read discoveries in context alongside the
    # branch's code changes. A manifest with discoveries but zero
    # modified .shadow/*.md files outside _dreams/ means the branch is
    # out of sync with its own manifest. This is a hard error: it
    # signals the agent skipped the mirroring step.
    if discoveries:
        bm_match = re.search(
            r'^base_commit:\s*["\']?([0-9a-fA-F]{7,40})["\']?\s*$',
            m.group(1), re.M,
        ) if m else None
        if not bm_match:
            errors.append(
                "manifest declares discoveries but report.md frontmatter "
                "is missing `base_commit` — cannot verify shadow files were "
                "updated. Add base_commit (full SHA emitted by dream-setup.sh)."
            )
        else:
            base = bm_match.group(1)
            modified = set()
            git_failed = False
            try:
                # --relative forces output paths relative to CWD, so
                # `.shadow/foo.md` checks work whether the worktree is
                # the repo root (normal dream case) or a subdirectory
                # (testing this validator on an example).
                d = subprocess.run(
                    ['git', '-C', worktree, 'diff', '--name-only',
                     '--relative', f'{base}..HEAD', '--', '.shadow/'],
                    capture_output=True, text=True, encoding="utf-8", timeout=10,
                )
                if d.returncode == 0:
                    if d.stdout:
                        modified.update(d.stdout.strip().splitlines())
                else:
                    # Non-zero almost always means base_commit is not a
                    # resolvable ref in this worktree — we cannot compute the
                    # mirror diff, so don't emit the misleading "no shadows
                    # modified" hard error below.
                    git_failed = True
                # Include uncommitted (staged + unstaged) — the final
                # commit may not have happened at validate time.
                # `--untracked-files=all` forces git to enumerate every
                # untracked file individually; without it, a fresh
                # `.shadow/src/` subtree is rolled up into a single
                # `?? .shadow/` line and the mirror check false-fails.
                s = subprocess.run(
                    ['git', '-C', worktree, 'status', '--porcelain=v1',
                     '--untracked-files=all', '--', '.shadow/'],
                    capture_output=True, text=True, encoding="utf-8", timeout=10,
                )
                if s.returncode == 0:
                    for line in s.stdout.strip().splitlines():
                        if len(line) > 3:
                            # "XY path" or "R  old -> new" — take the
                            # final path segment.
                            modified.add(line[3:].split(' -> ')[-1])
                else:
                    git_failed = True
            except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
                warnings.append(
                    "could not run `git diff` against base_commit — "
                    "skipping the discovery-mirror check. Verify "
                    "manually that .shadow/*.md files were updated."
                )
            else:
                non_dream = [
                    f for f in modified
                    if f.startswith('.shadow/')
                    and not f.startswith('.shadow/_dreams/')
                    and f.endswith('.md')
                ]
                if not non_dream and git_failed:
                    warnings.append(
                        f"could not resolve base_commit {base[:8]} in this "
                        f"worktree (git diff/status returned an error), so the "
                        f"discovery-mirror check was skipped. Verify manually "
                        f"that .shadow/*.md files were updated, or confirm "
                        f"base_commit is correct."
                    )
                elif not non_dream:
                    errors.append(
                        f"manifest declares {len(discoveries)} discoveries "
                        f"but NO .shadow/*.md files outside _dreams/ were "
                        f"modified vs base_commit {base[:8]}. The reconciler "
                        f"merges manifest entries into main directly (so "
                        f"discoveries are not lost at merge time), but the "
                        f"branch shadows must also be updated so PR reviewers "
                        f"can read the discoveries in context. Mirror each "
                        f"discovery into the corresponding per-file shadow "
                        f"(e.g. .shadow/src/foo.py.md) or into .shadow/_cross/ "
                        f"before validating."
                    )

    # 11. Label triage (non-blocking) — nudge the agent to re-check label
    # assignment when discovery text contains common signal phrases but no
    # label is set. Keywords are intentionally narrow to limit false positives
    # (e.g. "slow path" alone is too noisy). The agent makes the final call.
    LABEL_SIGNALS = {
        'bug': [
            r'\bsilent(?:ly)? (?:fail|return|ignore|drop|truncate|swallow)',
            r'\boff[- ]by[- ]one\b',
            r'\bincorrect(?:ly)? (?:return|compute|round|order)',
            r'\brace condition\b',
            r'\bnot thread[- ]safe\b',
            r'\bvalidate[- ]then[- ](?:use|calculate|apply)',
            r'\bmasks? (?:errors?|exceptions?|failures?)\b',
            r'\bcrash(?:es)? on\b',
            r'\bnever (?:fires?|runs?|reaches?)\b',
        ],
        'security': [
            r'\binjection\b',
            r'\bpath traversal\b',
            r'\b\.\./\b',
            r'\bunsanitized\b',
            r'\bunescape(?:d)?\b',
            r'\bauth(?:n|z)? bypass\b',
            r'\bmissing auth(?:n|z| check)\b',
            r'\b(?:logs?|leaks?) (?:secret|password|token|api[- ]?key)',
            r'\beval\(',
            r'\bos\.system\(',
            r'\bshell=True\b',
        ],
        'performance': [
            r'\bO\(N(?:\^|\*\*)?2\)',
            r'\bquadratic\b',
            r'\b(?:slow|takes?) \d+(?:\.\d+)? *(?:ms|s|seconds?|minutes?)',
            r'\bre[- ]?reads?\b.*\b(?:every|each) (?:call|request|iteration)',
            r'\bbottleneck\b',
            r'\bN\+1\b',
        ],
    }
    sig_patterns = {
        lbl: [re.compile(p, re.I) for p in pats]
        for lbl, pats in LABEL_SIGNALS.items()
    }
    for i, disc in enumerate(discoveries):
        if not isinstance(disc, dict):
            continue
        text = (disc.get('text') or '')
        if not text:
            continue
        existing = {l.lower() for l in (disc.get('labels') or [])}
        for lbl, patterns in sig_patterns.items():
            if lbl in existing:
                continue
            for pat in patterns:
                if pat.search(text):
                    warnings.append(
                        f"discoveries[{i}] text contains '{lbl}' signal "
                        f"(/{pat.pattern}/) but no '{lbl}' label is set. "
                        f"Re-check whether this discovery is actionable; "
                        f"if so, add it to manifest labels and the in-file "
                        f"discovery metadata."
                    )
                    break

    # Output
    for w in warnings:
        print(f"WARNING: {w}")

    if errors:
        for e in errors:
            print(f"ERROR: {e}")
        sys.exit(1)

    print(f"✓ Validation passed for {dream_id}")


if __name__ == '__main__':
    main()

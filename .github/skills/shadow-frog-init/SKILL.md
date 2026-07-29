---
name: shadow-frog-init
description: >-
  Initialize a shadow knowledge base for any codebase. Creates a .shadow/
  directory that mirrors the source tree with markdown files for AI-discovered
  insights. Run this once per repo before using other shadow-frog skills.
  Refuses to overwrite an existing .shadow/ unless --reset is passed.
scripts:
  - shadow-init.py
---

# ShadowFrog Init

Creates `.shadow/` directory with symbol-organized shadow files for every
source file. Run once per repo. If `.shadow/` exists, ask user to reset or skip.

## Primary: Python Helper Script

The companion script `shadow-init.py` lives in the same directory as
this SKILL.md file. To find and run it:

```bash
# Project install (Copilot CLI):
python3 .github/skills/shadow-frog-init/shadow-init.py [options]
# Or for Claude Code:
python3 .claude/skills/shadow-frog-init/shadow-init.py [options]
```

**IMPORTANT: Run from the repo/worktree root directory.** The script
auto-detects the root via `git rev-parse --show-toplevel`, which returns
the correct root for regular repos AND worktrees. If auto-detection fails
(common when python is routed through Docker or the `.git` file points to
an inaccessible path), pass `--root` explicitly:

```bash
# If auto-detect fails, pass the root explicitly:
python3 .github/skills/shadow-frog-init/shadow-init.py --root "$(pwd)"

# In Docker wrapper scenarios (eval harness), git may not work inside
# the container. Use --root to bypass git detection:
python3 .github/skills/shadow-frog-init/shadow-init.py --root /testbed
```

### Options

| Flag | Effect |
|------|--------|
| `--root DIR` | Repository root (default: auto-detect via git) |
| `--reset` | Delete existing .shadow/ and recreate |
| `--dry-run` | Show what would be created without writing |

### What it does

1. Discovers source files via `git ls-files`
2. Filters through `.shadow/.shadowignore` (gitignore syntax)
3. Extracts symbols from each file (classes, functions, methods)
4. Creates per-file shadow `.md` files with symbol headings
5. Creates `_index.md`, `_prefs.md`, `_meta/state.json`, `.shadowignore`
6. Reports: files, symbols, languages detected

### After running

Tell the user:
- "Edit `.shadow/.shadowignore` to exclude files that shouldn't be shadowed"
- "Run `/shadow-frog-dream` for autonomous exploration, or `/shadow-frog-update` after your next changes"

Then decide the version-control mode (do not skip this — it is not handled
by the script). Ask the user: "Should `.shadow/` be **committed** (shared
with your team via git) or **gitignored** (local to your machine only)?"
Make the trade-off explicit before they choose — see
[Step 9: Handle .gitignore](#9-handle-gitignore) for the full committed vs
gitignored comparison. Key caveat: a gitignored `.shadow/` disables
`shadow-frog-dream` (dreams move `.shadow/` through git). If gitignored, add
`.shadow/` to `.gitignore`.

## Fallback: Manual Init

If the Python script fails (wrong Python version, missing file, etc.),
follow these steps manually:

### 1. Check preconditions

```bash
git rev-parse --is-inside-work-tree  # must be a git repo
test -d .shadow && echo "exists"     # if exists, ask user: reset or skip
```

### 2. Discover source files

```bash
git ls-files --cached --others --exclude-standard
```

Include patterns (auto-detect from repo contents):
`*.py`, `*.js`, `*.ts`, `*.tsx`, `*.jsx`, `*.java`, `*.go`, `*.rs`, `*.rb`,
`*.cpp`, `*.c`, `*.h`, `*.cs`, `*.swift`, `*.kt`, `*.scala`, `*.php`,
`*.sh`, `*.bash`, `*.zsh`, `*.yaml`, `*.yml`, `*.toml`, `*.json`,
`Makefile`, `Dockerfile`, `docker-compose*.yml`

Default excludes (always applied): `node_modules/`, `vendor/`, `venv/`,
`.venv/`, `__pycache__/`, `*.min.js`, `*.min.css`, `*.map`, `*.lock`,
`dist/`, `build/`, `target/`, `out/`, `.shadow/`, binary files

After discovering files, filter them through `.shadow/.shadowignore`
(if it exists). The ignore file uses `.gitignore` syntax.

### 3. Create directories

```bash
mkdir -p .shadow/_cross .shadow/_meta .shadow/_dreams
# For each source file, create parent dirs: mkdir -p .shadow/<dir>/
```

### 4. Create `.shadow/.shadowignore`

Uses `.gitignore` syntax. Seed with sensible defaults:

```gitignore
# Directories
node_modules/
vendor/
venv/
.venv/
__pycache__/
dist/
build/
target/
out/

# Generated / minified
*.min.js
*.min.css
*.map
*.lock

# Binary
*.png
*.jpg
*.gif
*.ico
*.woff
*.woff2
*.ttf
*.eot
*.pdf
*.zip
*.tar.gz

# The shadow itself
.shadow/

# ShadowFrog's own install artifacts (project install copies these here)
.github/skills/shadow-frog*/
.github/hooks/scripts/shadow-frog-*
.claude/skills/shadow-frog*/
.claude/hooks/scripts/shadow-frog-*
```

Tell the user: "Edit `.shadow/.shadowignore` to exclude files or
folders that shouldn't be shadowed (e.g., vendored code, generated
files, tool configs)."

### 5. Create `_prefs.md`

```markdown
# Preferences

_No preferences recorded yet._
```

This file stores project-wide user preferences and conventions that are
not tied to any specific file or symbol. It is populated by
`/shadow-frog-update` when the user shares general directives.

### 6. Create `_meta/state.json`

```json
{
  "version": 1,
  "initialized_at": "<ISO timestamp>",
  "last_update_at": "<ISO timestamp>",
  "last_commit": "<full 40-char HEAD SHA>",
  "last_update_type": "init|auto|manual|dream|meditate",
  "total_files": 0,
  "total_symbols": 0,
  "total_discoveries": 0,
  "dream_cycles_completed": 0
}
```

### 7. Generate per-file shadows

For each source file, extract symbols and create a shadow with this structure:

```markdown
# Shadow: <path/to/file.py>

**Language**: <lang> | **Lines**: <N> | **Last modified**: <date>

## File-Level

_No discoveries yet._

## `class <ClassName>`

### `<ClassName.method>`

_No discoveries yet._

## `<function_name>`

_No discoveries yet._

## Cross-References

_No cross-cutting discoveries yet._
```

Rules:
- Every class, function, method gets a `##`/`###` heading
- Symbol name is the stable anchor — no line numbers in headings
- `## Cross-References` section is always last
- Extract symbols using language-appropriate static analysis (AST, tree-sitter, regex)
- If static analysis is not feasible, create `## File-Level` only; other skills fill in symbols later

### 8. Generate `_index.md`

```markdown
# Shadow Index

> Generated by shadow-frog-init on <date>
> Total files: N | Symbols: M | Discoveries: 0 | Cross-cutting: 0

| File | Language | Symbols | Discoveries |
|------|----------|---------|-------------|
| src/auth.py | Python | 5 (UserAuth, authenticate_user, ...) | 0 |
```

### 9. Handle .gitignore

Ask the user: "Should `.shadow/` be **committed** (shared with your team via
git) or **gitignored** (local to your machine only)?"

Before they decide, make the trade-off explicit:

**Committed (shared) — full functionality:**
- The whole team shares one knowledge base; discoveries compound across people.
- `shadow-frog-dream` works — autonomous experiments commit `.shadow/`
  artifacts onto dream branches, push them, and reconcile merges them back.
- `shadow-frog-meditate` and the viewer work normally.

**Gitignored (local only) — reduced functionality:**
- Your shadow stays private to your machine and never leaves the repo.
- `shadow-frog-init`, `shadow-frog-update`, `shadow-frog-meditate`, and the
  viewer all still work (they operate on the local filesystem).
- **`shadow-frog-dream` will NOT work.** Dreams move `.shadow/` through git
  (commit → push → reconcile from the remote); a gitignored `.shadow/` is
  silently skipped by `git add`, so discoveries never reach the remote and
  are lost. `dream-setup.sh` detects this and refuses to start with a clear
  error rather than failing silently.

- If gitignored: add `.shadow/` to `.gitignore`.

### 10. Report

Print: files discovered, languages detected, total symbols.
Suggest: `/shadow-frog-update` for deeper analysis, `/shadow-frog-dream` for autonomous exploration.

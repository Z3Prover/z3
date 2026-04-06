#!/usr/bin/env bash
# extract.sh
#
# Run the Meta-F* reflection-based extraction to generate C++ rewrite rules
# from the F* lemmas in this directory.
#
# Usage (from the fstar/ directory):
#   ./extract.sh
#
# Usage (from the repo root):
#   fstar/extract.sh
#
# Output:
#   Prints the generated C++ rules to stdout.
#   Exits non-zero if F* typechecking or tactic execution fails.
#
# Requirements:
#   fstar.exe on PATH (F* 2024.09.05 or later recommended).
#   The three source files must be present:
#     IEEE754.fst, FPARewriterRules.fst, RewriteCodeGen.fst

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

if ! command -v fstar.exe &>/dev/null; then
    echo "ERROR: fstar.exe not found on PATH." >&2
    echo "Install F* 2026.03.24+ from https://github.com/FStarLang/FStar/releases" >&2
    exit 1
fi

echo "=== F* version ===" >&2
fstar.exe --version >&2

echo "" >&2
echo "=== Running Meta-F* extraction ===" >&2

# F* writes tactic print() output to stdout.
# Verification progress and errors go to stderr.
fstar.exe --include . \
    IEEE754.fst \
    FPARewriterRules.fst \
    RewriteCodeGen.fst

echo "" >&2
echo "=== Extraction complete ===" >&2

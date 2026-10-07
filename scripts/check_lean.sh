#!/usr/bin/env bash
set -euo pipefail

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    printf 'Usage: %s [FILE ...]\n' "$0"
    printf 'Build the pinned Lean project, then check any supplied Lean source files.\n'
    printf 'Both .lean and .txt files are accepted. With no files, check the project only.\n'
    exit 0
fi
if [[ "${1:-}" == "--" ]]; then
    shift
fi

repo_dir="$(CDPATH= cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
project_dir="$repo_dir/lean"
toolchain="$(< "$project_dir/lean-toolchain")"

if command -v elan >/dev/null 2>&1; then
    elan_command="$(command -v elan)"
elif [[ -x "${HOME:-}/.elan/bin/elan" ]]; then
    elan_command="${HOME}/.elan/bin/elan"
else
    printf 'check_lean.sh: elan was not found. Install elan; see lean/README.md.\n' >&2
    exit 127
fi

for file in "$@"; do
    if [[ ! -f "$file" || ! -r "$file" ]]; then
        printf 'check_lean.sh: cannot read file: %s\n' "$file" >&2
        exit 2
    fi
done

caller_dir="$PWD"
cd -- "$project_dir"
"$elan_command" run "$toolchain" lake build
for file in "$@"; do
    case "$file" in
        /*) ;;
        *) file="$caller_dir/$file" ;;
    esac
    printf 'Checking %s\n' "$file"
    "$elan_command" run "$toolchain" lake env lean --trust=0 -DwarningAsError=true "$file"
done
printf 'Lean checks passed.\n'

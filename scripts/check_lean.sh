#!/usr/bin/env bash
set -euo pipefail

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    printf 'Usage: %s [--chain] [FILE ...]\n' "$0"
    printf 'Build the pinned Lean project, then check any supplied Lean source files.\n'
    printf 'Both .lean and .txt files are accepted. With no files, check the project only.\n'
    printf 'With --chain the files are one chain of modules, checked in order by one Lean process\n'
    printf 'each: a file may import the files before it by name (NAME.lean as NAME). Each but the\n'
    printf 'last is compiled, under the same flags, to an .olean in a fresh temporary directory that\n'
    printf 'only the later files of this run read and that is removed when the run ends (5 to 9 MB\n'
    printf 'of .olean per MB of Lean text while it runs). That directory is made by mktemp -d, or in\n'
    printf 'the directory Z3_LEAN_CHAIN_DIR names: a run that is killed cannot remove it, so a caller\n'
    printf 'that runs chains under a deadline names a directory it removes itself.\n'
    exit 0
fi
chain=0
if [[ "${1:-}" == "--chain" ]]; then
    chain=1
    shift
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
if (( chain )); then
    # An imported file's module name is its file name: an identifier, so that `import NAME` finds it.
    for file in "${@:1:$(( $# > 0 ? $# - 1 : 0 ))}"; do
        if [[ ! "$(basename -- "$file")" =~ ^[A-Za-z_][A-Za-z0-9_]*\.lean$ ]]; then
            printf 'check_lean.sh: a chained file that later files import must be named IDENTIFIER.lean: %s\n' "$file" >&2
            exit 2
        fi
    done
    if [[ -n "${Z3_LEAN_CHAIN_DIR:-}" && ! -d "$Z3_LEAN_CHAIN_DIR" ]]; then
        printf 'check_lean.sh: Z3_LEAN_CHAIN_DIR is not a directory: %s\n' "$Z3_LEAN_CHAIN_DIR" >&2
        exit 2
    fi
fi

caller_dir="$PWD"
cd -- "$project_dir"
# Z3_LEAN_SKIP_BUILD=1: the caller has already built the project in this checkout (the Python
# tests set it after their first check).
if [[ "${Z3_LEAN_SKIP_BUILD:-}" != "1" ]]; then
    "$elan_command" run "$toolchain" lake build
fi
if (( chain )); then
    # The .olean files of the chain: written by this run's Lean processes, read by its later ones,
    # and removed with the run. `lake env` keeps LEAN_PATH after the project's own search path.
    # The directory is always a fresh one, so no .olean of another run is ever read. A run that is
    # killed (SIGKILL: no trap) leaves it behind, 5 to 9 MB per MB of Lean text: a caller with a
    # deadline names in Z3_LEAN_CHAIN_DIR a directory of its own to make it in, and removes that.
    if [[ -n "${Z3_LEAN_CHAIN_DIR:-}" ]]; then
        case "$Z3_LEAN_CHAIN_DIR" in
            /*) modules="$(mktemp -d "$Z3_LEAN_CHAIN_DIR/olean.XXXXXX")" ;;
            *) modules="$(mktemp -d "$caller_dir/$Z3_LEAN_CHAIN_DIR/olean.XXXXXX")" ;;
        esac
    else
        modules="$(mktemp -d)"
    fi
    trap 'rm -rf -- "$modules"' EXIT
    export LEAN_PATH="$modules${LEAN_PATH:+:$LEAN_PATH}"
fi
remaining=$#
for file in "$@"; do
    case "$file" in
        /*) ;;
        *) file="$caller_dir/$file" ;;
    esac
    remaining=$(( remaining - 1 ))
    printf 'Checking %s\n' "$file"
    if (( chain && remaining )); then
        name="$(basename -- "$file")"
        "$elan_command" run "$toolchain" lake env lean --trust=0 -DwarningAsError=true --memory=8192 \
            --root="$(dirname -- "$file")" -o "$modules/${name%.lean}.olean" "$file"
    else
        "$elan_command" run "$toolchain" lake env lean --trust=0 -DwarningAsError=true --memory=8192 "$file"
    fi
done
printf 'Lean checks passed.\n'

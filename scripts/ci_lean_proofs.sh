#!/usr/bin/env bash
# Check Z3's native proofs in Lean: the Lean reconstruction tests, the z3test proof script tests,
# and the Lean-certified Boolean and QF_LRA proof matrices.
# Used by .github/workflows/ci.yml (releaseClang job) and .github/workflows/lean-proofs.yml.
set -uo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/ci_lean_proofs.sh [options]

Check Z3's native proofs in Lean against an existing build. Every check runs even if an
earlier one fails. The script exits nonzero if any check failed.

Options:
  --z3 PATH        z3 executable (default: build/z3). Its directory's python/ subdirectory
                   is put on PYTHONPATH.
  --z3test DIR     z3test checkout (default: z3test)
  --out DIR        directory for lean-proof-artifacts/ and lean-proof-matrix.jsonl
                   (default: $RUNNER_TEMP if set, otherwise lean-proof-out)
  --timeout SEC    per-benchmark timeout passed to proof_matrix.py (default: 30)
  --install-lean   install elan and the toolchain pinned in lean/lean-toolchain first
  -h, --help       show this help

Environment: PYTHON selects the Python interpreter (default: python3).
EOF
}

repo_dir="$(CDPATH='' cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
z3="build/z3" z3test="z3test" out="${RUNNER_TEMP:-lean-proof-out}" timeout=30 install_lean=0
while (( $# )); do
    case "$1" in
        --z3) z3="$2"; shift 2 ;;
        --z3test) z3test="$2"; shift 2 ;;
        --out) out="$2"; shift 2 ;;
        --timeout) timeout="$2"; shift 2 ;;
        --install-lean) install_lean=1; shift ;;
        -h|--help) usage; exit 0 ;;
        *) printf 'ci_lean_proofs.sh: unknown argument: %s\n' "$1" >&2; usage >&2; exit 2 ;;
    esac
done

abspath() { (CDPATH='' cd -- "$(dirname -- "$1")" && printf '%s/%s\n' "$(pwd -P)" "$(basename -- "$1")"); }
[[ -x "$z3" ]] || { printf 'ci_lean_proofs.sh: z3 executable not found: %s\n' "$z3" >&2; exit 2; }
[[ -d "$z3test/scripts/proofs" ]] || { printf 'ci_lean_proofs.sh: not a z3test checkout: %s\n' "$z3test" >&2; exit 2; }
mkdir -p "$out"
z3="$(abspath "$z3")" z3test="$(abspath "$z3test")" out="$(abspath "$out")"

if (( install_lean )); then
    curl --proto '=https' --tlsv1.2 -sSf https://elan.lean-lang.org/elan-init.sh -o "$out/elan-init.sh"
    sh "$out/elan-init.sh" -y --no-modify-path --default-toolchain none
    "$HOME/.elan/bin/elan" toolchain install "$(< "$repo_dir/lean/lean-toolchain")"
    [[ -n "${GITHUB_PATH:-}" ]] && echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
    export PATH="$HOME/.elan/bin:$PATH"
fi

python_dir="$(dirname "$z3")/python"
export Z3_EXE="$z3" Z3_SOURCE="$repo_dir" PYTHONPATH="$python_dir${PYTHONPATH:+:$PYTHONPATH}"
artifacts="$out/lean-proof-artifacts" matrix="$out/lean-proof-matrix.jsonl" lean="$z3test/regressions/proofs/lean"
rm -rf "$artifacts" "$matrix"

py="${PYTHON:-python3}" rows="" failed=0
check() {
    local name="$1" start=$SECONDS rc; shift
    [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::group::$name"
    printf '\n===== %s\n$ %s\n' "$name" "$*"
    (cd "$repo_dir" && "$@"); rc=$?
    [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::endgroup::"
    if (( rc == 0 )); then
        rows+="| $name | pass | $(( SECONDS - start ))s |"$'\n'
    else
        rows+="| $name | **FAIL** (exit $rc) | $(( SECONDS - start ))s |"$'\n'; failed=1
        [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::error::$name failed (exit $rc)"
    fi
}

check "Lean reconstruction tests" \
    "$py" -m unittest discover -s examples/python -p 'test_proof_to_lean*.py' -v
check "z3test proof script tests" \
    "$py" -m unittest discover -s "$z3test/scripts/proofs" -p 'test_proof*.py' -v
check "Lean-certified Boolean matrix (legacy proof object)" \
    "$py" "$z3test/scripts/proofs/proof_matrix.py" --z3 "$Z3_EXE" --z3-source "$Z3_SOURCE" \
        --lean --cells legacy-proof-object --timeout "$timeout" \
        --lean-artifacts "$artifacts" --out "$matrix" \
        "$lean"/boolean_*.smt2 "$lean/unit_resolution.smt2"
check "Lean-certified QF_LRA matrix (clause log)" \
    "$py" "$z3test/scripts/proofs/proof_matrix.py" --z3 "$Z3_EXE" --z3-source "$Z3_SOURCE" \
        --lean --cells smt-clause-log-nopp --timeout "$timeout" \
        --lean-artifacts "$artifacts" --out "$matrix" \
        "$lean"/lra_*.smt2

summary="$(printf '## Lean proof checks\n\n| check | result | time |\n| --- | --- | --- |\n%s' "$rows")"
printf '\n%s\n' "$summary"
[[ -n "${GITHUB_STEP_SUMMARY:-}" ]] && printf '%s\n' "$summary" >> "$GITHUB_STEP_SUMMARY"
exit $failed

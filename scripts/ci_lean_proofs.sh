#!/usr/bin/env bash
# Check Z3's native proofs in Lean: the Lean reconstruction tests, the z3test proof script tests,
# and the Lean-certified Boolean and QF_LRA proof matrices; optionally probe how far certification
# reaches on further benchmarks. Writes a Markdown summary (scripts/lean_proof_summary.py) of what
# was checked, what is trusted, and where certification stops.
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
  --out DIR        output directory (default: $RUNNER_TEMP if set, otherwise lean-proof-out)
  --timeout SEC    per-benchmark timeout passed to proof_matrix.py (default: 30)
  --install-lean   install elan and the toolchain pinned in lean/lean-toolchain first
  --probe DIR      also run the boundary probe over the .smt2 files below DIR (repeatable):
                   both Lean cells, informational only. Inputs that are not certified do
                   not fail the run; a harness or configuration error does.
  --probe-timeout SEC       solver limit per probed benchmark (default: 10)
  --probe-lean-timeout SEC  reconstruction and Lean limit per probed benchmark (default: 120)
  --probe-jobs N   probe processes run in parallel (default: 2; each Lean check may use 8 GB)
  --probe-only     skip the gated checks and run only the probe (one CI job per corpus)
  -h, --help       show this help

Writes to the output directory: lean-proof-summary.md (also appended to $GITHUB_STEP_SUMMARY),
lean-proof-matrix.jsonl, lean-proof-artifacts/, lean-proof-logs/, and with --probe also
lean-probe.jsonl and lean-probe/.

Environment: PYTHON selects the Python interpreter (default: python3).
EOF
}

repo_dir="$(CDPATH='' cd -- "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
z3="build/z3" z3test="z3test" out="${RUNNER_TEMP:-lean-proof-out}" timeout=30 install_lean=0
probe_dirs=() probe_timeout=10 probe_lean_timeout=120 probe_jobs=2 probe_only=0
while (( $# )); do
    case "$1" in
        --z3) z3="$2"; shift 2 ;;
        --z3test) z3test="$2"; shift 2 ;;
        --out) out="$2"; shift 2 ;;
        --timeout) timeout="$2"; shift 2 ;;
        --install-lean) install_lean=1; shift ;;
        --probe) probe_dirs+=("$2"); shift 2 ;;
        --probe-timeout) probe_timeout="$2"; shift 2 ;;
        --probe-lean-timeout) probe_lean_timeout="$2"; shift 2 ;;
        --probe-jobs) probe_jobs="$2"; shift 2 ;;
        --probe-only) probe_only=1; shift ;;
        -h|--help) usage; exit 0 ;;
        *) printf 'ci_lean_proofs.sh: unknown argument: %s\n' "$1" >&2; usage >&2; exit 2 ;;
    esac
done

abspath() { (CDPATH='' cd -- "$(dirname -- "$1")" && printf '%s/%s\n' "$(pwd -P)" "$(basename -- "$1")"); }
[[ -x "$z3" ]] || { printf 'ci_lean_proofs.sh: z3 executable not found: %s\n' "$z3" >&2; exit 2; }
[[ -d "$z3test/scripts/proofs" ]] || { printf 'ci_lean_proofs.sh: not a z3test checkout: %s\n' "$z3test" >&2; exit 2; }
(( probe_only && ! ${#probe_dirs[@]} )) && { echo 'ci_lean_proofs.sh: --probe-only requires --probe' >&2; exit 2; }
for dir in ${probe_dirs[@]+"${probe_dirs[@]}"}; do
    [[ -d "$dir" ]] || { printf 'ci_lean_proofs.sh: probe directory not found: %s\n' "$dir" >&2; exit 2; }
done
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
probe_out="$out/lean-probe" probe_matrix="$out/lean-probe.jsonl" logs="$out/lean-proof-logs"
checks="$logs/checks.tsv" summary_file="$out/lean-proof-summary.md"
rm -rf "${out:?}/lean-proof-artifacts" "${out:?}/lean-probe" "${out:?}/lean-proof-logs"
rm -f "${out:?}/lean-proof-matrix.jsonl" "${out:?}/lean-probe.jsonl" "${out:?}/lean-proof-summary.md"
mkdir -p "$logs"

py="${PYTHON:-python3}" rows="" failed=0 count=0
# check NAME KIND gate|probe COMMAND...: run one check, keep its output in a log for the summary,
# and record it in the check list. A gating check fails the run on any nonzero exit status. The
# probe exits 1 whenever an input is not certified, its normal outcome; a higher status is an error.
check() {
    local name="$1" kind="$2" role="$3" start=$SECONDS rc log; shift 3
    count=$(( count + 1 )); log="$logs/check-$count-$kind.log"
    [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::group::$name"
    printf '\n===== %s\n$ %s\n' "$name" "$*"
    (cd "$repo_dir" && "$@") 2>&1 | tee "$log"; rc=${PIPESTATUS[0]}
    [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::endgroup::"
    printf '%s\t%s\t%s\t%d\t%d\t%s\n' "$name" "$kind" "$role" "$rc" "$(( SECONDS - start ))" "$log" >> "$checks"
    if (( rc == 0 )) || [[ "$role" == probe && $rc == 1 ]]; then
        rows+="| $name | pass | $(( SECONDS - start ))s |"$'\n'
    else
        rows+="| $name | **FAIL** (exit $rc) | $(( SECONDS - start ))s |"$'\n'; failed=1
        [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::error::$name failed (exit $rc)"
    fi
}

# probe_part LIST: run both Lean cells over one benchmark list of the probe; print its log when done.
probe_part() {
    local list="$1" base="${1%.txt}" rc
    "$py" "$z3test/scripts/proofs/proof_matrix.py" --z3 "$Z3_EXE" --z3-source "$Z3_SOURCE" \
        --lean --cells legacy-proof-object,smt-clause-log-nopp --timeout "$probe_timeout" \
        --lean-timeout "$probe_lean_timeout" --lean-artifacts "$base.artifacts" --out "$base.jsonl" \
        "$list" > "$base.log" 2>&1
    rc=$?
    echo "$rc" > "$base.rc"
    printf -- '--- %s (exit %d)\n' "$(< "$base.label")" "$rc"
    cat "$base.log"
}

# probe: split the probe directories into one benchmark list per immediate subdirectory (a logic,
# in the SMT-LIB layouts) plus one for the files directly inside, and run the lists in parallel.
probe() {
    local dir sub list n=0 status=0 rc
    mkdir -p "$probe_out"
    for dir in "${probe_dirs[@]}"; do
        dir="$(abspath "$dir")"
        for sub in "$dir" "$dir"/*/; do
            sub="${sub%/}" list="$probe_out/part-$n.txt"
            if [[ "$sub" == "$dir" ]]; then
                find "$dir" -maxdepth 1 -name '*.smt2' -type f | LC_ALL=C sort > "$list"
            elif [[ -d "$sub" ]]; then
                find "$sub" -name '*.smt2' -type f | LC_ALL=C sort > "$list"
            else
                continue
            fi
            if [[ -s "$list" ]]; then
                printf '%s\n' "${sub#"$(dirname "$dir")/"}" > "${list%.txt}.label"
                n=$(( n + 1 ))
            fi
        done
    done
    (( n )) || { echo "no .smt2 files below the probe directories" >&2; return 2; }
    export -f probe_part
    export py z3test probe_timeout probe_lean_timeout
    for (( i = 0; i < n; i++ )); do printf '%s\n' "$probe_out/part-$i.txt"; done \
        | xargs -P "$probe_jobs" -n 1 bash -c 'probe_part "$1"' _
    for (( i = 0; i < n; i++ )); do
        rc="$(cat "$probe_out/part-$i.rc" 2>/dev/null || echo 2)"
        (( rc > status )) && status=$rc
        cat "$probe_out/part-$i.jsonl" >> "$probe_matrix" 2>/dev/null
    done
    return "$status"
}

if (( ! probe_only )); then
    check "Lean reconstruction tests" unittest gate \
        "$py" -m unittest discover -s examples/python -p 'test_proof_to_lean*.py' -v
    check "z3test proof script tests" unittest gate \
        "$py" -m unittest discover -s "$z3test/scripts/proofs" -p 'test_proof*.py' -v
    check "Lean-certified Boolean matrix (legacy proof object)" matrix gate \
        "$py" "$z3test/scripts/proofs/proof_matrix.py" --z3 "$Z3_EXE" --z3-source "$Z3_SOURCE" \
            --lean --cells legacy-proof-object --timeout "$timeout" \
            --lean-artifacts "$artifacts" --out "$matrix" \
            "$lean"/boolean_*.smt2 "$lean/unit_resolution.smt2"
    check "Lean-certified QF_LRA matrix (clause log)" matrix gate \
        "$py" "$z3test/scripts/proofs/proof_matrix.py" --z3 "$Z3_EXE" --z3-source "$Z3_SOURCE" \
            --lean --cells smt-clause-log-nopp --timeout "$timeout" \
            --lean-artifacts "$artifacts" --out "$matrix" \
            "$lean"/lra_*.smt2
fi
if (( ${#probe_dirs[@]} )); then
    check "Boundary probe" probe probe probe
fi

summary_args=(--checks "$checks" --source "$repo_dir" --z3test "$z3test" --gate "$matrix")
summary_args+=(--context "z3 $(git -C "$repo_dir" rev-parse --short=12 HEAD 2>/dev/null || echo '(unknown commit)'), $("$z3" --version 2>/dev/null | head -1)")
summary_args+=(--context "z3test $(git -C "$z3test" rev-parse --short=12 HEAD 2>/dev/null || echo '(unknown commit)'), Lean $(< "$repo_dir/lean/lean-toolchain")$( (( probe_only )) || echo ", gate solver limit ${timeout}s")")
if (( ${#probe_dirs[@]} )); then
    summary_args+=(--probe "$probe_matrix" --probe-timeout "$probe_timeout" --probe-lean-timeout "$probe_lean_timeout")
    for dir in "${probe_dirs[@]}"; do
        dir="$(abspath "$dir")"
        case "$dir/" in
            "$z3test"/*) label="z3test ${dir#"$z3test"/}" ;;
            "$repo_dir"/*) label="z3 ${dir#"$repo_dir"/}" ;;
            *) label="$dir" ;;
        esac
        summary_args+=(--corpus "$label=$dir")
    done
fi
if [[ -n "${GITHUB_RUN_ID:-}" ]]; then
    summary_args+=(--artifacts-url "${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-}/actions/runs/${GITHUB_RUN_ID}#artifacts")
fi
if ! "$py" "$repo_dir/scripts/lean_proof_summary.py" "${summary_args[@]}" > "$summary_file"; then
    [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::warning::the detailed Lean proof summary failed; reporting the check table only"
    printf '## Lean proof checks\n\n| check | result | time |\n| --- | --- | --- |\n%s' "$rows" > "$summary_file"
fi
printf '\n'; cat "$summary_file"
[[ -n "${GITHUB_STEP_SUMMARY:-}" ]] && cat "$summary_file" >> "$GITHUB_STEP_SUMMARY"
exit $failed

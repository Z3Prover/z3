---
description: Build Z3 and FStar, then publish a GitHub Discussion summary
on:
  schedule: daily
  workflow_dispatch:
    inputs:
      z3_ref:
        description: Z3 ref to checkout and build
        required: false
        default: master
      z3_cmake_args:
        description: Extra CMake arguments for the Z3 build
        required: false
        default: ""
      z3_runtime_args:
        description: Extra runtime args for Z3 sanity checks
        required: false
        default: "smt.ho_matching=true"
      fstar_ref:
        description: FStar ref to checkout and build
        required: false
        default: master
      fstar_opam_switch:
        description: OCaml switch version for FStar
        required: false
        default: "4.14.2"
      fstar_otherflags:
        description: Extra OTHERFLAGS for FStar build
        required: false
        default: "--smt.ho_matching true"
permissions:
  contents: read
  discussions: read
network: defaults
tools:
  bash: true
  github:
    toolsets: [discussions]
safe-outputs:
  mentions: false
  create-discussion:
    title-prefix: "[F* build] "
    category: "Agentic Workflows"
    close-older-discussions: false
  missing-tool:
    create-issue: true
timeout-minutes: 180
steps:
  - name: Checkout Z3
    uses: actions/checkout@v6.0.2
    with:
      ref: ${{ github.event.inputs.z3_ref || 'master' }}
      fetch-depth: 1
      persist-credentials: false
---

# Build FStar with a configurable Z3 build and publish results

You are an AI build agent. Build Z3 and then build FStar with that Z3. Post a GitHub Discussion summarizing the run.

## Input parameters

Read all values from workflow-dispatch inputs and apply defaults when not set:

- `z3_ref` (default `master`)
- `z3_cmake_args` (default empty)
- `z3_runtime_args` (default `smt.ho_matching=true`)
- `fstar_ref` (default `master`)
- `fstar_opam_switch` (default `4.14.2`)
- `fstar_otherflags` (default `--smt.ho_matching true`)

## Constraints

- Use `${{ github.workspace }}` as the workspace root.
- Put temporary files under `/tmp/gh-aw/agent`.
- Use only the Z3 built in this workflow when building FStar.
- Keep a compact build summary in `/tmp/gh-aw/agent/summary.md`.
- Fail fast with clear error messages.

## Phase 1: Build Z3

```bash
set -euo pipefail

mkdir -p /tmp/gh-aw/agent
cd "${{ github.workspace }}"

Z3_REF="${{ github.event.inputs.z3_ref || 'master' }}"
Z3_CMAKE_ARGS="${{ github.event.inputs.z3_cmake_args || '' }}"
Z3_RUNTIME_ARGS="${{ github.event.inputs.z3_runtime_args || 'smt.ho_matching=true' }}"

echo "z3_ref=$Z3_REF"
echo "z3_cmake_args=$Z3_CMAKE_ARGS"
echo "z3_runtime_args=$Z3_RUNTIME_ARGS"

sudo apt-get update -y
sudo apt-get install -y cmake ninja-build python3 git curl unzip opam m4 pkg-config libgmp-dev jq

cmake -S . -B build/release -G Ninja -DCMAKE_BUILD_TYPE=Release $Z3_CMAKE_ARGS
ninja -C build/release z3

"${{ github.workspace }}/build/release/z3" --version | tee /tmp/gh-aw/agent/z3-version.txt
"${{ github.workspace }}/build/release/z3" $Z3_RUNTIME_ARGS -version | tee /tmp/gh-aw/agent/z3-runtime-check.txt
```

Extract the numeric version string from `/tmp/gh-aw/agent/z3-version.txt` into `Z3_VERSION`.

## Phase 2: Prepare Z3 aliases for FStar

```bash
set -euo pipefail

mkdir -p /tmp/gh-aw/agent/z3-bin
ln -sf "${{ github.workspace }}/build/release/z3" /tmp/gh-aw/agent/z3-bin/z3
ln -sf "${{ github.workspace }}/build/release/z3" /tmp/gh-aw/agent/z3-bin/z3-4.8.5
ln -sf "${{ github.workspace }}/build/release/z3" /tmp/gh-aw/agent/z3-bin/z3-4.13.3
export PATH="/tmp/gh-aw/agent/z3-bin:$PATH"

z3 --version
z3-4.8.5 --version
z3-4.13.3 --version
```

## Phase 3: Clone and build FStar

```bash
set -euo pipefail

FSTAR_REF="${{ github.event.inputs.fstar_ref || 'master' }}"
FSTAR_OPAM_SWITCH="${{ github.event.inputs.fstar_opam_switch || '4.14.2' }}"
FSTAR_OTHERFLAGS="${{ github.event.inputs.fstar_otherflags || '--smt.ho_matching true' }}"

rm -rf /tmp/gh-aw/agent/FStar
git clone --depth=1 --branch "$FSTAR_REF" https://github.com/FStarLang/FStar.git /tmp/gh-aw/agent/FStar
cd /tmp/gh-aw/agent/FStar

echo "FStar commit: $(git rev-parse HEAD)" | tee /tmp/gh-aw/agent/fstar-commit.txt

opam init --disable-sandboxing --yes
opam switch create "$FSTAR_OPAM_SWITCH" --yes || opam switch "$FSTAR_OPAM_SWITCH"
eval "$(opam env --switch=$FSTAR_OPAM_SWITCH)"

opam install --deps-only . --yes

Z3_VERSION="$(sed -E -n 's/^Z3 version ([0-9]+\.[0-9]+\.[0-9]+).*/\1/p' /tmp/gh-aw/agent/z3-version.txt | head -1)"
if [ -z "$Z3_VERSION" ]; then
  echo "ERROR: could not parse Z3 version from /tmp/gh-aw/agent/z3-version.txt"
  exit 1
fi

PATH="/tmp/gh-aw/agent/z3-bin:$PATH" OTHERFLAGS="--z3version $Z3_VERSION $FSTAR_OTHERFLAGS" make -j"$(nproc)"
```

## Phase 4: Collect summary

```bash
set -euo pipefail

test -x /tmp/gh-aw/agent/FStar/out/bin/fstar.exe
/tmp/gh-aw/agent/FStar/out/bin/fstar.exe --version | tee /tmp/gh-aw/agent/fstar-version.txt

Z3_VERSION="$(sed -E -n 's/^Z3 version ([0-9]+\.[0-9]+\.[0-9]+).*/\1/p' /tmp/gh-aw/agent/z3-version.txt | head -1)"
FSTAR_VERSION="$(cat /tmp/gh-aw/agent/fstar-version.txt | tr -d '\r' | head -1)"
FSTAR_COMMIT="$(sed -E -n 's/^FStar commit: (.*)$/\1/p' /tmp/gh-aw/agent/fstar-commit.txt | head -1)"

cat > /tmp/gh-aw/agent/summary.md <<EOF
### Build status
- ✅ Z3 build completed
- ✅ FStar build completed

### Inputs used
- z3_ref: \`${{ github.event.inputs.z3_ref || 'master' }}\`
- z3_cmake_args: \`${{ github.event.inputs.z3_cmake_args || '' }}\`
- z3_runtime_args: \`${{ github.event.inputs.z3_runtime_args || 'smt.ho_matching=true' }}\`
- fstar_ref: \`${{ github.event.inputs.fstar_ref || 'master' }}\`
- fstar_opam_switch: \`${{ github.event.inputs.fstar_opam_switch || '4.14.2' }}\`
- fstar_otherflags: \`${{ github.event.inputs.fstar_otherflags || '--smt.ho_matching true' }}\`

### Produced versions
- Z3 version: \`${Z3_VERSION:-unknown}\`
- FStar version: \`${FSTAR_VERSION:-unknown}\`
- FStar commit: \`${FSTAR_COMMIT:-unknown}\`

### Experimental configuration
- ho_matching requested via Z3 args and FStar OTHERFLAGS.
EOF
```

## Phase 5: Publish discussion

Read `/tmp/gh-aw/agent/summary.md` and call `create_discussion` with:

- Title: `FStar build with configurable Z3 inputs — YYYY-MM-DD`
- Body: include the summary file contents and a link to `${{ github.server_url }}/${{ github.repository }}/actions/runs/${{ github.run_id }}`

You **MUST** call either `create_discussion` or `report_incomplete` before finishing.

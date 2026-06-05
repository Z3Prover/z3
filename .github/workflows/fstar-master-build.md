---
description: Build Z3 master and then build FStar master using that Z3 build
on:
  schedule: daily
  workflow_dispatch:
permissions: read-all
network: defaults
tools:
  bash: true
timeout-minutes: 180
steps:
  - name: Checkout Z3 master
    uses: actions/checkout@v6.0.2
    with:
      ref: master
      fetch-depth: 1
      persist-credentials: false
---

# Build FStar master with Z3 master

You are an AI build agent. Build the latest `master` branch of Z3, then build the latest `master` branch of FStar using the Z3 you just built.

## Constraints

- Use `${{ github.workspace }}` as the workspace root.
- Put temporary files under `/tmp/gh-aw/agent`.
- Use only the Z3 built in this workflow when building FStar.
- Fail fast with clear error messages if any phase fails.

## Phase 1: Build Z3 master

```bash
set -euo pipefail

cd "${{ github.workspace }}"

echo "Building Z3 from branch: $(git rev-parse --abbrev-ref HEAD)"
git rev-parse HEAD

sudo apt-get update -y
sudo apt-get install -y cmake ninja-build python3 git curl unzip

cmake -S . -B build/release -G Ninja -DCMAKE_BUILD_TYPE=Release
ninja -C build/release z3

"${{ github.workspace }}/build/release/z3" --version | tee /tmp/gh-aw/agent/z3-version.txt
```

Extract the numeric version string from the `z3 --version` output and store it in `Z3_VERSION` (for example, `4.15.4`).

## Phase 2: Prepare PATH aliases for FStar

FStar expects versioned Z3 command names on PATH. Create local aliases pointing to the Z3 binary from Phase 1.

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

## Phase 3: Clone and build FStar master

```bash
set -euo pipefail

mkdir -p /tmp/gh-aw/agent
rm -rf /tmp/gh-aw/agent/FStar

git clone --depth=1 --branch master https://github.com/FStarLang/FStar.git /tmp/gh-aw/agent/FStar
cd /tmp/gh-aw/agent/FStar

echo "FStar commit: $(git rev-parse HEAD)"

sudo apt-get update -y
sudo apt-get install -y opam m4 pkg-config libgmp-dev

opam init --disable-sandboxing --yes
OPAM_SWITCH=4.14.2
opam switch create "$OPAM_SWITCH" --yes || opam switch "$OPAM_SWITCH"
eval "$(opam env --switch=$OPAM_SWITCH)"

opam install --deps-only . --yes

Z3_VERSION="$(sed -E -n 's/^Z3 version ([0-9]+\.[0-9]+\.[0-9]+).*/\1/p' /tmp/gh-aw/agent/z3-version.txt | head -1)"
if [ -z "$Z3_VERSION" ]; then
  echo "ERROR: could not parse Z3 version from /tmp/gh-aw/agent/z3-version.txt"
  exit 1
fi

echo "Using Z3 version override: $Z3_VERSION"
PATH="/tmp/gh-aw/agent/z3-bin:$PATH" OTHERFLAGS="--z3version $Z3_VERSION" make -j"$(nproc)"
```

## Phase 4: Verify artifacts and report

```bash
set -euo pipefail

test -x /tmp/gh-aw/agent/FStar/out/bin/fstar.exe
/tmp/gh-aw/agent/FStar/out/bin/fstar.exe --version | tee /tmp/gh-aw/agent/fstar-version.txt

echo "SUCCESS: built Z3 master and FStar master with that Z3"
```

## Usage

- This workflow is scheduled daily and can also be started manually.
- It checks out Z3 `master`, builds `build/release/z3`, then clones FStar `master` and builds it using that Z3.

---
description: Build latest FStar master using Z3 built from latest Z3 master

on:
  schedule: daily
  workflow_dispatch:

permissions: read-all

network: defaults

tools:
  bash: true
  github:
    toolsets: [default]

safe-outputs:
  create-discussion:
    title-prefix: "[F* Build] "
    category: "Agentic Workflows"
    close-older-discussions: true
    expires: 14d
  create-issue:
    title-prefix: "[F* Build Failure] "
    labels: ["build", "fstar"]
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

timeout-minutes: 120

steps:
  - name: Checkout Z3 master
    uses: actions/checkout@v6.0.2
    with:
      ref: master
      fetch-depth: 1
      persist-credentials: false

---

# Build Latest F* with Latest Z3

You are an automation engineer validating interoperability between Z3 and F*.

Your goal is to build **latest Z3 master** from this repository, then build **latest FStarLang/FStar master** using the Z3 you built.

## Requirements

1. Use `${{ github.workspace }}` as the Z3 source (already checked out at `master`).
2. Build Z3 from source with CMake + Ninja in Release mode.
3. Install Z3 into `/tmp/gh-aw/agent/z3-install`.
4. Verify the installed Z3 binary and capture its full version string.
5. Fetch latest `master` from `FStarLang/FStar` and capture the exact commit SHA used.
6. Build F* from that latest master using the locally built Z3 (not a system Z3).
7. If F* requires setup steps, follow the current instructions from the checked-out FStar repository (for example `INSTALL.md`, `README.md`, `flake.nix`, or build scripts).
8. Keep all temporary files under `/tmp/gh-aw/agent`.

## Execution Plan

### Phase 1: Environment Setup

- Install required build dependencies for Z3 and F* (for example: `cmake`, `ninja-build`, `opam`, `m4`, `pkg-config`, `libgmp-dev`, `curl`, `git`, `python3`).
- Print tool versions (`cmake`, `ninja`, `opam`, `ocaml` if available).

### Phase 2: Build and Install Z3 (master)

- Build in `/tmp/gh-aw/agent/z3-build`.
- Use:
  - `cmake -G Ninja -DCMAKE_BUILD_TYPE=Release`
  - `ninja`
  - `ninja install` with prefix `/tmp/gh-aw/agent/z3-install`
- Verify:
  - `/tmp/gh-aw/agent/z3-install/bin/z3 --version`
- Record:
  - Z3 commit from `git -C "${{ github.workspace }}" rev-parse HEAD`
  - Z3 version output

### Phase 3: Fetch Latest F* Master

- Clone `https://github.com/FStarLang/FStar.git` into `/tmp/gh-aw/agent/fstar` with branch `master`.
- Record exact commit SHA:
  - `git -C /tmp/gh-aw/agent/fstar rev-parse HEAD`

### Phase 4: Build F* with Local Z3

- Ensure the local Z3 is used by exporting:
  - `PATH=/tmp/gh-aw/agent/z3-install/bin:$PATH`
  - `Z3_EXE=/tmp/gh-aw/agent/z3-install/bin/z3`
- Discover and follow the repository’s current build path from checked-in docs/scripts.
- Execute the build commands needed for F* master.
- Capture concise logs into files under `/tmp/gh-aw/agent/logs/`.

### Phase 5: Report Results

- On success, call `create-discussion` with:
  - Z3 commit + version
  - FStar commit
  - Key build commands executed
  - Build outcome summary
- On failure, call `create-issue` with:
  - Failing phase
  - Error summary
  - Relevant log excerpt
  - Z3 commit/version and FStar commit (if available)

## Safety and Quality

- Fail fast on command errors.
- Do not modify repository files.
- Keep the report concise and actionable.

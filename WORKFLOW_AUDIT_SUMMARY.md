# Workflow Audit Summary

## Audit of Run 20827545546

**Run URL:** https://github.com/Z3Prover/z3/actions/runs/20827545546/job/59832789762

### Issues Identified

#### 1. Missing OCaml Build Instructions
The pr-fix agentic workflow lacked specific instructions for building Z3 with OCaml bindings. When the AI agent needed to work on OCaml-related code changes, it didn't have clear guidance on:
- How to set up the OCaml environment (opam, OCaml compiler)
- Required system dependencies (gmp, pkg-config, ninja, ccache)
- CMake configuration for OCaml bindings
- Build commands for OCaml bindings
- How to test the OCaml bindings

#### 2. Incorrect Safe-Output Configuration
**File:** `.github/workflows/pr-fix.md`
**Issue:** Used deprecated/incorrect safe-output name `push-to-pr-branch`
**Fix:** Changed to correct name `push-to-pull-request-branch`

This prevented the workflow from properly pushing changes to pull request branches.

#### 3. Deprecated Field Names
**Files:** Multiple agentic workflow files
**Issue:** Used deprecated field name `timeout_minutes` instead of `timeout-minutes`
**Affected Files:**
- ask.md
- ci-doctor.md
- daily-backlog-burner.md
- daily-perf-improver.md
- daily-test-improver.md
- pr-fix.md

This caused compilation failures in strict mode.

### Changes Made

#### 1. Created `.github/workflows/agentics/build-tools.md`

This new file provides comprehensive OCaml build instructions that are now available to all agentic workflows that include it (via `@include? agentics/build-tools.md`).

**Content includes:**
- System dependencies for Ubuntu/Linux and macOS
- OCaml setup with opam
- Required OCaml packages (ocamlfind, zarith)
- CMake configuration for Z3 with OCaml bindings
- Build commands using ninja
- Testing instructions for both bytecode and native OCaml examples
- Environment variable setup
- Caching recommendations
- Troubleshooting guide

**Workflows that now have access to these instructions:**
- ask.md
- pr-fix.md
- daily-backlog-burner.md
- daily-perf-improver.md
- daily-test-improver.md

#### 2. Fixed pr-fix.md Configuration

```diff
 safe-outputs:
-  push-to-pr-branch:
+  push-to-pull-request-branch:
   create-issue:
     title-prefix: "${{ github.workflow }}"
```

```diff
-timeout_minutes: 20
+timeout-minutes: 20
```

#### 3. Fixed Deprecated Field Names

Updated all agentic workflows to use the correct `timeout-minutes` field name instead of the deprecated `timeout_minutes`.

### Source of Build Instructions

The OCaml build instructions were extracted from `.github/workflows/ocaml.yaml`, which is the existing CI workflow for OCaml binding builds. This ensures consistency between:
- Manual CI builds (ocaml.yaml)
- AI-driven builds (agentic workflows)

Key steps extracted:
1. System dependency installation (bubblewrap, m4, libgmp-dev, pkg-config, ninja-build, ccache)
2. OCaml setup using ocaml/setup-ocaml@v3 action
3. opam package installation (ocamlfind, zarith)
4. CMake configuration with OCaml-specific flags:
   - `-DZ3_BUILD_OCAML_BINDINGS=ON`
   - `-G Ninja` for faster builds
5. Ninja build target: `build_z3_ocaml_bindings`
6. Testing with both bytecode and native OCaml examples

### Benefits

1. **Consistency:** Agentic workflows now use the same build process as the standard CI
2. **Reliability:** AI agents have clear, tested instructions for OCaml builds
3. **Reusability:** Build instructions are shared across multiple workflows via includes
4. **Maintainability:** Single source of truth for OCaml build steps in agentics/build-tools.md
5. **Compliance:** All workflows now use correct, non-deprecated field names
6. **Functionality:** pr-fix workflow can now properly push changes to PR branches

### Testing Recommendations

1. **Trigger pr-fix workflow** on a PR that involves OCaml code changes
2. **Monitor the workflow run** to ensure the agent can:
   - Install OCaml dependencies
   - Configure Z3 with OCaml bindings
   - Build the OCaml bindings
   - Run tests
   - Push changes if needed
3. **Verify other workflows** (ask, daily-*) can compile and run successfully

### Next Steps

1. Monitor the next workflow runs to ensure compilation succeeds in CI
2. Watch for any issues with the OCaml build instructions in practice
3. Consider adding similar build instruction sections for other language bindings (Java, .NET, Python) if needed
4. Update documentation to reference the new build-tools.md file for contributors

## Files Modified

1. `.github/workflows/agentics/build-tools.md` (created)
   - Comprehensive OCaml build instructions
   - 150+ lines of detailed guidance

2. `.github/workflows/pr-fix.md`
   - Fixed safe-output configuration
   - Fixed timeout field name

3. `.github/workflows/ask.md`
   - Fixed timeout field name

4. `.github/workflows/ci-doctor.md`
   - Fixed timeout field name

5. `.github/workflows/daily-backlog-burner.md`
   - Fixed timeout field name

6. `.github/workflows/daily-perf-improver.md`
   - Fixed timeout field name

7. `.github/workflows/daily-test-improver.md`
   - Fixed timeout field name

## Compilation Status

The workflows should now compile successfully in CI with proper GitHub authentication. Local compilation requires GitHub CLI authentication to resolve the `@include` directives.

To compile in CI (with authentication):
```bash
gh aw compile
```

The compilation will:
1. Resolve all `@include` and `@include?` directives
2. Generate `.lock.yml` files for each `.md` workflow
3. Validate the workflow configuration
4. Check for deprecated fields and security issues in strict mode

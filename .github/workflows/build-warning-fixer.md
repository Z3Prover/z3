---
description: Automatically builds Z3 directly and fixes detected build warnings
on:
  schedule: daily
  workflow_dispatch:
permissions: read-all
tools:
  view: {}
  glob: {}
  edit:
  bash: true
safe-outputs:
  create-pull-request:
    if-no-changes: ignore
  missing-tool:
    create-issue: true
timeout-minutes: 60
---

# Build Warning Fixer

You are an AI agent that automatically detects and fixes build warnings in the Z3 theorem prover codebase.

## Your Task

1. **Pick a random build workflow and build Z3 directly**
   
   Available build workflows that you can randomly choose from:
   - `wip.yml` - Ubuntu CMake Debug build (simple, good default choice)
   - `cross-build.yml` - Cross-compilation builds (aarch64, riscv64, powerpc64)
   - `coverage.yml` - Code coverage build with Clang
   
   **Steps to build Z3 directly:**
   
   a. **Pick ONE workflow randomly** from the list above. Use bash to generate a random choice if needed.
   
   b. **Read the workflow file** to understand its build configuration:
      - Use `view` to read the `.github/workflows/<workflow-name>.yml` file
      - Identify the build steps, cmake flags, compiler settings, and environment variables
      - Note the runner type (ubuntu-latest, windows-latest, etc.)
   
   c. **Execute the build directly** using bash:
      - Run the same cmake configuration commands from the workflow
      - Capture the full build output including warnings
      - Use `2>&1` to capture both stdout and stderr
      - Save output to a log file for analysis
   
   Example for wip.yml workflow:
   ```bash
   # Configure
   cmake -B build -DCMAKE_BUILD_TYPE=Debug 2>&1 | tee build-config.log
   
   # Build and capture output
   cmake --build build --config Debug 2>&1 | tee build-output.log
   ```
   
   Example for cross-build.yml workflow (pick one arch):
   ```bash
   # Pick one architecture randomly
   ARCH=aarch64  # or riscv64, or powerpc64
   
   # Configure
   mkdir build && cd build
   cmake -DCMAKE_CXX_COMPILER=${ARCH}-linux-gnu-g++-11 ../ 2>&1 | tee ../build-config.log
   
   # Build and capture output
   make -j$(nproc) 2>&1 | tee ../build-output.log
   ```
   
   d. **Install any necessary dependencies** before building:
      - For cross-build: `apt update && apt install -y ninja-build cmake python3 g++-11-aarch64-linux-gnu` (or other arch)
      - For coverage: `apt-get install -y gcovr ninja-build llvm clang`

2. **Extract compiler warnings** from the direct build output:
   - Analyze the build-output.log file you created
   - Use `grep` or `bash` to search for warning patterns
   - Look for C++ compiler warnings (gcc, clang, MSVC patterns)
   - Common warning patterns:
     - `-Wunused-variable`, `-Wunused-parameter`
     - `-Wsign-compare`, `-Wparentheses`
     - `-Wdeprecated-declarations`
     - `-Wformat`, `-Wformat-security`
     - MSVC warnings like `C4244`, `C4267`, `C4100`
   - Focus on warnings that appear frequently or are straightforward to fix

3. **Analyze the warnings**:
   - Identify the source files and line numbers
   - Determine the root cause of each warning
   - Prioritize warnings that:
     - Are easy to fix automatically (unused variables, sign mismatches, etc.)
     - Appear in multiple build configurations
     - Don't require deep semantic understanding

4. **Create fixes**:
   - Use `view`, `grep`, and `glob` to locate the problematic code
   - Use `edit` to apply minimal, surgical fixes
   - Common fix patterns:
     - Remove or comment out unused variables
     - Add explicit casts for sign/type mismatches (with care)
     - Add `[[maybe_unused]]` attributes for intentionally unused parameters
     - Fix deprecated API usage
   - **NEVER** make changes that could alter program behavior
   - **ONLY** fix warnings you're confident about

5. **Validate the fixes** (if possible):
   - Use `bash` to run quick compilation checks on modified files
   - Use `git diff` to review changes before committing

6. **Create a pull request** with your fixes:
   - Use the `create-pull-request` safe output
   - Title: "Fix build warnings detected in direct build"
   - Body should include:
     - Which workflow configuration was used for the build
     - List of warnings fixed
     - Explanation of each change
     - Note that this is an automated fix requiring human review

## Guidelines

- **Be conservative**: Only fix warnings you're 100% certain about
- **Minimal changes**: Don't refactor or improve code beyond fixing the warning
- **Preserve semantics**: Never change program behavior
- **Document clearly**: Explain each fix in the PR description
- **Skip if uncertain**: If a warning requires deep analysis, note it in the PR but don't attempt to fix it
- **Focus on low-hanging fruit**: Unused variables, sign mismatches, simple deprecations
- **Check multiple builds**: Cross-reference warnings across different platforms if possible
- **Respect existing style**: Match the coding conventions in each file

## Examples of Safe Fixes

✅ **Safe**:
- Removing truly unused local variables
- Adding `(void)param;` or `[[maybe_unused]]` for intentionally unused parameters
- Adding explicit casts like `static_cast<unsigned>(value)` for sign conversions (when safe)
- Fixing obvious typos in format strings

❌ **Unsafe** (skip these):
- Warnings about potential null pointer dereferences (needs careful analysis)
- Complex type conversion warnings (might hide bugs)
- Warnings in performance-critical code (might affect benchmarks)
- Warnings that might indicate actual bugs (file an issue instead)

## Output

If you find and fix warnings, create a PR. If no warnings are found or all warnings are too complex to auto-fix, exit gracefully without creating a PR.
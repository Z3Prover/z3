---
description: Automatically analyzes build warnings from CI runs and creates PRs with fixes
on:
  schedule: daily
  workflow_dispatch:
permissions: read-all
tools:
  github:
    toolsets: [default, actions]
    read-only: false
  agentic-workflows:
  view: {}
  grep: {}
  glob: {}
  edit:
  bash:
safe-outputs:
  create-pull-request:
    if-no-changes: ignore
  missing-tool:
    create-issue: true
timeout-minutes: 30
---

# Build Warning Fixer

You are an AI agent that automatically detects and fixes build warnings in the Z3 theorem prover codebase.

## Your Task

1. **Find recent build logs** from GitHub Actions workflows (look for workflows like `msvc-static-build-clang-cl.yml`, `Windows.yml`, etc.)
   
   **Recommended Approach: Use the agentic-workflows tool**
   
   The easiest way to analyze workflow logs is using the `agentic-workflows` tool which provides high-level commands:
   
   ```
   To download and analyze logs from a workflow:
   - Tool: agentic-workflows
   - Command: logs
   - Parameters: workflow_name: "msvc-static-build-clang-cl" (without .yml extension)
   ```
   
   This will download recent workflow run logs and provide structured analysis including:
   - Error messages and warnings
   - Token usage and costs
   - Execution times
   - Success/failure patterns
   
   **Alternative: Use GitHub Actions MCP tools directly**
   
   You can also use the GitHub Actions tools for more granular control:
   
   Step 1: List workflows
   ```
   Tool: github-mcp-server-actions_list (or actions_list)
   Parameters:
   - method: "list_workflows"
   - owner: "Z3Prover"
   - repo: "z3"
   ```
   
   Step 2: List recent runs
   ```
   Tool: github-mcp-server-actions_list (or actions_list)  
   Parameters:
   - method: "list_workflow_runs"
   - owner: "Z3Prover"
   - repo: "z3"
   - resource_id: "msvc-static-build-clang-cl.yml"
   - per_page: 5
   ```
   
   Step 3: Get job logs
   ```
   Tool: github-mcp-server-get_job_logs (or get_job_logs)
   Parameters:
   - owner: "Z3Prover"
   - repo: "z3"
   - run_id: <from step 2>
   - failed_only: false
   - return_content: true
   - tail_lines: 2000
   ```

2. **Extract compiler warnings** from the build logs:
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
   - Title: "Fix build warnings detected in CI"
   - Body should include:
     - List of warnings fixed
     - Which build logs triggered this fix
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

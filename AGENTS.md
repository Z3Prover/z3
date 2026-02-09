# Agent Instructions

## Building Z3

Use **CMake** and **Ninja** for builds:

```bash
# Debug build
mkdir -p build/debug && cd build/debug
cmake -G Ninja -DCMAKE_BUILD_TYPE=Debug ../..
ninja                 # Build Z3
ninja test-z3         # Build unit tests
./test-z3 /a          # Run all unit tests

# Release build
mkdir -p build/release && cd build/release
cmake -G Ninja -DCMAKE_BUILD_TYPE=Release ../..
ninja

# Release build with tracing enabled
mkdir -p build/release && cd build/release
cmake -G Ninja -DCMAKE_BUILD_TYPE=Release -DZ3_ENABLE_TRACING_FOR_NON_DEBUG=ON ../..
ninja
```

## Debugging Guidelines

- **Tracing limit**: No tracing should run for more than 5 seconds. If a trace takes longer, narrow down the scope or use conditional tracing.
- **Tracing syntax**: Use `-tr:tag` to enable specific trace tags, e.g.:
  ```bash
  ./z3 -tr:nlsat_explain input.smt2
  ```
- **Trace output**: Tracing output goes to `.z3-trace` in the current directory.
- **Useful trace tags**: `nlsat_explain`, `nlsat`, `nlsat_solver`

## Issue Tracking

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds


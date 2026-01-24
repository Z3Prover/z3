---
description: Analyzes code pushed to lws branch for duplicate code, inefficient patterns, and opportunities to use modern C++ features
on:
  push:
    branches:
      - lws
permissions: read-all
tools:
  github:
    toolsets: [default]
  view: {}
  glob: {}
  grep: {}
  bash:
    - "git log*"
    - "git diff*"
    - "git show*"
    - "clang-format --version"
safe-outputs:
  add-comment:
    max: 1
  create-issue:
    title-prefix: "[Code Quality] "
    labels: [code-quality, lws-branch, automated]
  missing-tool:
    create-issue: true
network: defaults
timeout-minutes: 20
---

<!-- Edit the file linked below to modify the agent without recompilation. Feel free to move the entire markdown body to that file. -->
{{#runtime-import agentics/lws-code-quality-analyzer.md}}

# Quick Reference

You are analyzing code quality for the Z3 theorem prover's `lws` branch.

## Three Focus Areas

1. **Duplicate Code**: Repeated patterns that should be abstracted
2. **Inefficient Code**: Performance bottlenecks and suboptimal implementations  
3. **Contemporary Features**: Opportunities for modern C++ (C++17/C++20)

## Key Commands

```bash
# See what changed in the latest commit
git show HEAD --stat
git diff HEAD~1 HEAD

# Find duplicate patterns
grep -r "pattern" src/

# View file context
view path/to/file.cpp
```

## Output Format

Create a detailed analysis with:
- Summary statistics
- Specific findings with file locations
- Code examples (before/after)
- Actionable recommendations
- Progressive disclosure with `<details>` tags

Focus on the most impactful issues first!

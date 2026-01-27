---
description: Automatically annotate code with assertions capturing class invariants, pre-conditions, and post-conditions using LLM-based specification mining

on:
  schedule: weekly
  workflow_dispatch:
    inputs:
      target_path:
        description: 'Target directory or file to analyze (e.g., src/ast/, src/smt/smt_context.cpp)'
        required: false
        default: ''
      target_class:
        description: 'Specific class name to analyze (optional)'
        required: false
        default: ''

roles: [write, maintain, admin]

permissions:
  contents: read
  issues: read
  pull-requests: read

network:
  allowed:
    - cpp

tools:
  github:
    toolsets: [default]
  view: {}
  glob: {}
  grep: {}
  edit: {}
  bash:
    - ":*"

safe-outputs:
  create-pull-request:
    if-no-changes: ignore
  missing-tool:
    create-issue: true

timeout-minutes: 45

steps:
  - name: Checkout repository
    uses: actions/checkout@v5

---

<!-- Edit the file linked below to modify the agent without recompilation. Feel free to move the entire markdown body to that file. -->
@./agentics/specbot.md

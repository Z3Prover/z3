---
description: Automatically validate and reproduce reported soundness bugs

on:
  issues:
    types: [opened, labeled]
  schedule: daily

roles: all

permissions: read-all

network: defaults

tools:
  cache-memory: true
  github:
    toolsets: [default]
  bash: [":*"]
  web-fetch: {}

safe-outputs:
  add-comment:
    max: 2
  create-discussion:
    title-prefix: "[Soundness] "
    category: "Agentic Workflows"
    close-older-discussions: true
  missing-tool:
    create-issue: true

timeout-minutes: 30

steps:
  - name: Checkout repository
    uses: actions/checkout@v5

---

<!-- Edit the file linked below to modify the agent without recompilation. Feel free to move the entire markdown body to that file. -->
@./agentics/soundness-bug-detector.md

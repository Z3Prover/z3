---
description: Monitor arXiv and GitHub weekly for new 'levelwise' references and create an issue summarizing the findings

on:
  schedule: weekly
  workflow_dispatch:

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
  create-issue:
    max: 1
    title-prefix: "[Levelwise Monitor] "
    labels: ["research", "automated"]
  missing-tool:
    create-issue: true

timeout-minutes: 15

steps:
  - name: Checkout repository
    uses: actions/checkout@v5

---

<!-- Edit the file linked below to modify the agent without recompilation. Feel free to move the entire markdown body to that file. -->
@./agentics/levelwise-monitor.md

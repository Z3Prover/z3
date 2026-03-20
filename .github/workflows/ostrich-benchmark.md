---
description: Run Z3 string solver benchmarks (seq vs nseq) and ZIPT on all Ostrich benchmarks from tests/ostrich.zip on the c3 branch and post results as a GitHub discussion

on:
  schedule:
    - cron: "0 6 * * *"
  workflow_dispatch:

permissions: read-all

network: defaults

tools:
  bash: true
  github:
    toolsets: [default]

safe-outputs:
  create-discussion:
    title-prefix: "[Ostrich Benchmark] "
    category: "Agentic Workflows"
    close-older-discussions: true
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false

timeout-minutes: 180

steps:
  - name: Checkout c3 branch
    uses: actions/checkout@v5
    with:
      ref: c3
      fetch-depth: 1
      persist-credentials: false

---

<!-- Edit the file linked below to modify the agent without recompilation. Feel free to move the entire markdown body to that file. -->
@./agentics/ostrich-benchmark.md

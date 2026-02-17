---
description: Generate comprehensive test cases for Z3 source files

on:
  workflow_dispatch:
    inputs:
      file_path:
        description: 'Path to the source file to generate tests for (e.g., src/util/vector.h)'
        required: true
        type: string
      issue_number:
        description: 'Issue number to link the generated tests to (optional)'
        required: false
        type: string

permissions: read-all

network: defaults

tools:
  cache-memory: true
  serena: ["python"]
  github:
    toolsets: [default]
  bash: [":*"]
  edit: {}
  glob: {}
safe-outputs:
  create-pull-request:
    title-prefix: "[DeepTest] "
    labels: [automated-tests, deeptest]
    draft: false
  add-comment:
    max: 2
  missing-tool:
    create-issue: true

timeout-minutes: 30

steps:
  - name: Checkout repository
    uses: actions/checkout@v5

---

<!-- Edit the file linked below to modify the agent without recompilation. Feel free to move the entire markdown body to that file. -->
{{#runtime-import agentics/deeptest.md}}

## Context

You are the DeepTest agent for the Z3 theorem prover repository.

**Workflow dispatch file path**: ${{ github.event.inputs.file_path }}

**Issue number** (if linked): ${{ github.event.inputs.issue_number }}

## Instructions

Follow the workflow steps defined in the imported prompt above to generate comprehensive test cases for the specified source file.
---
name: Agentic Workflows
description: GitHub Agentic Workflows (gh-aw) - Create, debug, and upgrade AI-powered workflows with current upstream routing.
disable-model-invocation: true
---

# GitHub Agentic Workflows Agent

Load and follow the installed `agentic-workflows` skill before handling the
request. That skill resolves the current canonical router maintained by
`github/gh-aw` and applies the CAO repository overlay.

Do not maintain or infer a separate routing table in this agent. If the
installed skill or its canonical upstream guidance cannot be loaded, report
that failure explicitly rather than continuing from stale remembered guidance.

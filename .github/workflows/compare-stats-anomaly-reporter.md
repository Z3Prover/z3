---
description: Analyze compare_stats.html for the latest 30 hours and publish bug/crash/anomaly summary as a GitHub Discussion

on:
  schedule:
    - cron: "0 */6 * * *"
  workflow_dispatch:

permissions: read-all

strict: false
timeout-minutes: 45

network:
  allowed:
    - defaults
    - mtzguido.tplinkdns.com

tools:
  bash: [":*"]
  github:
    toolsets: [default]

safe-outputs:
  create-discussion:
    title-prefix: "[Compare Stats] "
    category: "Agentic Workflows"
    close-older-discussions: true
  missing-tool:
    create-issue: true
  noop:
    report-as-issue: false
---

# Compare Stats Bug/Crash/Anomaly Reporter

Your name is ${{ github.workflow }}. You are a Z3 benchmarking analysis agent for `${{ github.repository }}`.

Analyze the benchmark comparison page below, focusing on results from the last 30 hours, then create a GitHub Discussion with a concise but actionable summary of:

- Bugs
- Crashes
- Anomalies

Source URL:
`http://mtzguido.tplinkdns.com:8081/z3/compare_stats.html`

## Requirements

### 1) Fetch and save the source page

Use bash to fetch the page into `/tmp/gh-aw/agent/compare_stats.html`.

Try this first:
```bash
curl -fsSL --max-time 60 "http://mtzguido.tplinkdns.com:8081/z3/compare_stats.html" -o /tmp/gh-aw/agent/compare_stats.html
```

If that fails, retry once with:
```bash
wget -q -T 60 -O /tmp/gh-aw/agent/compare_stats.html "http://mtzguido.tplinkdns.com:8081/z3/compare_stats.html"
```

If both fail, still create a discussion that explains the fetch failure, includes stderr output, and marks the report as incomplete.

### 2) Parse tabular data

Use Python to parse all tables from the HTML into normalized rows.

Use resilient parsing:
- Prefer `pandas.read_html` when available.
- If pandas fails, parse with `html.parser`/regex fallback.

Persist normalized JSON to `/tmp/gh-aw/agent/compare_stats_rows.json`.

### 3) Detect time window (last 30 hours)

Find candidate timestamp columns using case-insensitive column-name matches:
- `time`, `timestamp`, `date`, `run`, `created`, `updated`

Parse datetimes with timezone handling if present. Use current UTC time and filter to rows where timestamp is within the past 30 hours.

If no timestamp can be extracted:
- Report this limitation explicitly.
- Continue analysis on all rows.
- Mark the discussion as "time-window fallback".

### 4) Classify bugs/crashes/anomalies

Infer key columns using column-name heuristics:
- status/result/outcome
- benchmark/instance/file/name
- set/suite/group/track/family
- message/error/details/reason

Normalize status strings to lowercase.

#### Bugs / Crashes
Classify a row as **crash/bug** if status/details contain terms like:
- `crash`, `segfault`, `assert`, `abort`, `exception`, `error`, `failed`, `bug`

#### Anomalies
At minimum, detect:

1. **Unknown-outlier anomaly** (required):
   - Within the same benchmark set/suite/group, if most rows are in `{sat, unsat, timeout}` but a minority are `unknown`, flag the `unknown` rows as anomalies.
   - A practical threshold is acceptable (for example, total rows >= 4 and unknown ratio <= 0.4 while sat/unsat/timeout collectively dominate).

2. **Status divergence anomaly**:
   - Same benchmark name appears multiple times with conflicting non-timeout statuses (for example `sat` vs `unsat`).

3. **Repeated hard-failure anomaly**:
   - Same benchmark appears repeatedly with crash/error-like status in the time window.

### 5) Generate discussion report

Create a GitHub Discussion using `create-discussion` safe output.

Use this structure:

```markdown
### Compare Stats Analysis Report

**Source**: [compare_stats.html](http://mtzguido.tplinkdns.com:8081/z3/compare_stats.html)
**Workflow Run**: [#${{ github.run_id }}](https://github.com/${{ github.repository }}/actions/runs/${{ github.run_id }})
**Analysis Time (UTC)**: <timestamp>
**Window**: last 30 hours (or fallback mode)

### Executive Summary

- Rows analyzed: N
- Rows in 30h window: M (or "timestamp unavailable")
- Bugs/crashes: B
- Anomalies: A

### Bugs and Crashes

| Benchmark Set | Benchmark | Status | Details | Timestamp |
|---|---|---|---|---|
| ... |

### Anomalies

#### Unknown-Outlier Cases
| Benchmark Set | Benchmark | Status | Peer Status Distribution | Timestamp |
|---|---|---|---|---|
| ... |

#### Status Divergences
| Benchmark | Observed Statuses | Benchmark Set(s) | Timestamp(s) |
|---|---|---|---|
| ... |

#### Repeated Hard Failures
| Benchmark | Failure Count | Representative Status/Details | Benchmark Set(s) |
|---|---|---|---|
| ... |

### Notes and Limitations
- Mention parsing assumptions
- Mention missing columns/timestamps if any

<details>
<summary><b>Raw Extraction Summary</b></summary>

- Table count
- Candidate columns used
- Top status distribution
- Up to 30 representative raw rows (sanitized)

</details>
```

## Reporting Rules

- Be factual and concise.
- Do not claim certainty when column mapping is heuristic.
- If no bugs/crashes/anomalies are found, still create the discussion and explicitly state "No issues detected in analyzed window."
- Do not open PRs or modify repository files.

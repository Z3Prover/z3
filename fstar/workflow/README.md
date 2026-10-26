# `fstar-proof-checking` workflow

An [Atomic](https://github.com/bastani/atomic) workflow that iterates on the F* proof checker
from test evidence, following [`../workflow-instructions.txt`](../workflow-instructions.txt).
It reads Pulse checker reports, finds proof gaps, crashes, timeouts and slow proofs, repairs
them in theory-sliced git worktrees on at most 32 cores, verifies every candidate independently,
and publishes verified work to one branch and pull request at a time.

## Files

| Path | Purpose |
|---|---|
| `fstar-proof-checking.ts` | Workflow definition; the whole graph and its stop conditions are visible here. |
| `continuity.ts` | Launcher that evaluates the retrigger conditions and starts bounded runs. |
| `lib/reports.ts`, `lib/theories.ts` | Normalize Pulse reports and F* build logs into findings; classify theories. |
| `lib/sources.ts` | Read-only GitHub run listing and artifact download; local corpus scans. |
| `lib/state.ts` | Locked, atomically written state: dedup, claims, backoff, publication. |
| `lib/plan.ts`, `lib/git.ts` | Theory slices, the 32-core budget, and slice worktrees. |
| `lib/gate.ts` | Deterministic soundness gate and slice verdicts. |
| `lib/publish.ts` | Branch/PR lifecycle and crash bug-report filing. |
| `lib/steps.ts` | Durable step bodies wrapped by `ctx.tool` in the workflow. |
| `lib/prompts.ts`, `lib/schemas.ts`, `lib/toolchain.ts` | Stage prompts, verdict schema, toolchain preflight. |
| `lib/atomic-host.ts` | Bun helper that loads Atomic's SDK modules for tests and the launcher. |
| `tests/` | `bun test` suite and small fixtures excerpted from real Pulse artifacts. |

## Registration and discovery

`.atomic/` is ignored by this repository, so the source lives here and is registered with the
project workflow configuration `.atomic/extensions/workflow/config.json`:

```json
{
  "workflows": {
    "fstar-proof-checking": { "path": "./fstar/workflow/fstar-proof-checking.ts" }
  }
}
```

The 32-core cap is enforced by the slice planner: the cores of all slices planned for an
iteration add up to at most `coreBudget` (≤ 32), and each slice's prompt bounds its build jobs
to its share. How many slices actually run at once is limited separately by Atomic's stage
concurrency (`defaultConcurrency`, default 3). Raising that setting only increases throughput.
It never lets the cores in use exceed the budget.

Then run `/workflow reload` and `/workflow inputs fstar-proof-checking`.

## Running

```text
/workflow fstar-proof-checking dryRun=true
/workflow fstar-proof-checking
/workflow fstar-proof-checking publish=live
/workflow fstar-proof-checking pulseRunIds='["40244844124"]' theories='["arrays","bitvectors"]'
```

* `dryRun=true` only plans. It does not call GitHub, run checkers or agent stages, create
  worktrees, or change state. Use it with `reportPaths` to inspect slicing and the 32-core plan.
* With the default `publish=dry-run`, a real run repairs and verifies findings and merges
  verified slices into a local integration branch. It queries GitHub only to plan publication.
  `publish=live` pushes and opens or updates the PR and files crash reports. `publish=none`
  never contacts the remote for publication.

The important inputs are `pulseRunIds`, `reportPaths`, `localCorpora`, `ocamlChecker` and
`cherryChecker`, `theories`, `maxIterations` (1–5), `coreBudget` (≤ 32), `coresPerSlice`,
`publish` and `dryRun`. `/workflow inputs fstar-proof-checking` lists them all.

### Requirements

The preflight needs:

* F* `v2026.09.27`, from the `fstarExe` input, `FSTAR_EXE`, `PATH`, or `C:\fstar\fstar\bin\fstar.exe`.
* PowerShell 7 (`pwsh`) for `fstar/tools/build_ocaml_checker.ps1`.
* opam switch `fstar53` with OCaml 5.3, inside WSL on Windows.
* Python 3 for `run_checker_regressions.py`.
* Optionally, Cherry F* (`CHERRY_FSTAR_EXE`).

Local corpora also need checker executables. Use the `ocamlChecker` and `cherryChecker` inputs,
or `Z3_FSTAR_CHECKER` and `Z3_FSTAR_CHERRY_CHECKER`. If the proof toolchain is missing, a real run
ends **blocked** before any agent stage and names the missing tools. It never reports
unchecked work as verified.

## What one run does

```text
preflight → source ─┬─ iter-i/triage ──(nothing actionable → stop)
                    │     └─ iter-i/plan  (theory slices, ≤32 cores, worktrees, claims)
                    │          ├─ iter-i/<slice>/repair   one fresh stage per slice, in its worktree
                    │          ├─ iter-i/<slice>/verify   fresh, schema-backed independent verifier
                    │          └─ iter-i/gate → iter-i/integrate → iter-i/integration/verify
                    │                         → iter-i/publish → iter-i/persist
                    └─ investigate/select → investigate/{checker-scalability, certificate-reformulation, diagnostics-ux} → finalize
```

1. **Source.** The workflow downloads up to `maxReports` unprocessed runs. Regression runs
   provide `pulse-checker-report-<id>-<attempt>` and `pulse-checker-cherry-report-<id>-<attempt>`.
   Failed or timed-out builds provide `pulse-checker-build-report`. Downloads use read-only `gh`
   and are cached under `<stateDir>/reports`. The source step also reads `reportPaths` and
   scans local corpora. `C:/z3test/regressions/smt2` uses the checker's `--interactive --stats
   --diagnostics` mode. `C:/bench/inputs` uses `run_checker_regressions.py run/diagnose/report`.
   Each scan takes a rotating window of `localCaseLimit` files.
2. **Normalize.** Findings are partial-rule families from `diagnostics.jsonl`, checker
   crashes, rejected proofs, whole-case checker timeouts, and F* build proof timeouts
   (`Error … The SMT query timed out`). Declarations whose
   `process_one_decl` time is over 2 s are slow obligations. Each finding has a stable
   fingerprint. The same family seen by several reports or checkers is merged.
3. **Triage.** Resolved findings are skipped. So are findings claimed by another run, in
   backoff, or blocked (unless their evidence changed). The rest are ordered: crashes, possible
   unsoundness, build timeouts, partial rules by affected proofs, checker timeouts, then slow proofs.
4. **Plan.** Findings are grouped into slices by theory and focus:
   * Theories: linear and non-linear arithmetic, UF, arrays, datatypes, bit-vectors, finite
     fields, floating point, quantifier instantiation and binding, other.
   * Focus: repair, performance, crash, or soundness.

   The run creates `coreBudget / coresPerSlice` slices at most. They split the budget, so the
   cores of running slices never exceed 32. Each slice has its own worktree under
   `<stateDir>/worktrees` and its own branch `fstar-proof-checking/work/<run>/i<n>-<slice>`.
5. **Repair and verify.** The repair prompt covers every instruction section:
   * Fill gaps with principled rules, not special-case pattern matching.
   * Decompose slow or timed-out proofs so they rely less on Z3.
   * Work around crashes and draft an FStarLang/FStar bug report.
   * Investigate suspected Z3 unsoundness with reduced, independently checked evidence.
   * Make quantifier instantiation and binding steps checkable.

   A fresh verifier rebuilds and re-runs the checks itself, then returns a schema verdict.
6. **Gate.** A slice is `verified` only if all of these hold:
   * The verifier says `verified`.
   * The toolchain really ran.
   * Every final command exited 0.
   * The diff is committed.
   * The diff adds no `admit`, `tadmit`, `assume`, `--admit_smt_queries` or `--lax`, and no
     higher module-wide `--z3rlimit`.

   Anything else is `unverified`, `rejected`, or `no-change`.
7. **Integrate and verify again.** Verified slices are merged into
   `fstar-proof-checking/integration/<run>`. Its base is the open publication branch, or
   `baseRef` if there is none. The merged diff is scanned again, and a fresh stage verifies the
   merged build before anything is published.
8. **Publish.** One branch receives pushes until it is merged or deleted (see below).
9. **Persist.** Under the state lock, the step records outcomes, processed reports, scan offsets
   and publication state.
   * Verified findings resolve.
   * Others back off for 6 h, 12 h, … and are blocked after 3 attempts.
   * A blocked finding is reopened if its evidence changes.
10. **Investigate.** Three report-only stages run when the findings changed since the last
    investigation (`excludedTools: edit, write`):
    * checker refactoring for speed and scalability, including finite-field checker optimizations;
    * Z3 certificate reformulation;
    * diagnostics and UX: rules-checked counts for PARTIAL and ACCEPT, and an admit-diagnostics mode.

A run stops when nothing is actionable, at `maxIterations`, after two iterations in a row
without a verified slice, or in a blocked state. Blocked states are a missing toolchain and a PR
closed without merging. Each has an actionable reason in the `summary` output.

## Publication lifecycle

Publication state is stored as `activeBranch`, `prNumber` and `sequence`.

| Remote state of the active branch | Action |
|---|---|
| No active branch | Push `fstar-proof-checking/<n+1>` (the first free name) and open a PR. |
| PR open | Push to the same branch; no new PR. |
| Branch exists, no PR (e.g. an interrupted earlier run) | Push and open the PR. Every `gh pr create` is preceded by `gh pr list --state open`, so re-running never duplicates a PR. |
| PR merged | Start `fstar-proof-checking/<n+1>` and a new PR. |
| Branch deleted | Start a new branch and PR. |
| PR closed without merging, branch still there | **Blocked.** Reopen the PR, or delete the branch to start a new one. |

Crash reports carry the hidden marker `fstar-proof-checking:crash:<fingerprint>` and are filed in
FStarLang/FStar only with `publish=live`, after a search for that marker finds nothing.
All git and gh calls go through one command runner and are logged to
`<runDir>/commands.jsonl`. Pushes and PR or issue edits are flagged `mutating`, and
`evidence.json` lists the flagged entries. The tests check that dry runs issue no flagged command.

## State and evidence

`<stateDir>` defaults to `.atomic/fstar-proof-checking/`, which is ignored by git.

* `state.json` holds processed reports, per-finding status, attempts, backoff and claims, the
  publication branch and PR, bug reports, local-scan offsets, and run history. Every change runs
  under the exclusive `state.lock`, which is reclaimed if it is stale or its process is dead.
  The file is replaced by write-then-rename.
* `reports/` caches downloaded artifacts.
* `runs/<runKey>/` holds:
  * `setup.json`, `findings.json`, `commands.jsonl` and `evidence.json`;
  * `iter-<n>/` with the actionable, plan, gate, integration, publication and persistence
    records, plus each slice's `findings.json`, `slice-report.md`, `verification.md` and drafts;
  * `investigations/` with the investigation reports.
* `worktrees/` holds slice worktrees. Clean ones are removed at the end of a run. Branches and
  commits stay, and dirty worktrees are kept for inspection.

## Continuity

A bounded run never retriggers itself. Continuity comes from running the launcher between runs:

```text
bun fstar/workflow/continuity.ts --check [--dry-run]     # print the JSON decision only
bun fstar/workflow/continuity.ts --launch                # start one run if a condition holds
bun fstar/workflow/continuity.ts --launch --dry-run      # same, but dryRun=true, publish=dry-run, in-memory journal
```

It evaluates the three conditions from the instructions:

1. A new, unprocessed Pulse regression report. Only completed `success` or `failure` runs on
   `--branch` (default `master`) count; skipped and approval-gated runs do not.
2. Partial proof rule families recorded in state that are not yet processed: open, out of
   backoff, or with an expired claim.
3. A failed `pulse-checker-build` run whose `build.log` contains SMT proof timeouts, a timed-out
   build job, or a local OCaml or Cherry build log (`--build-log <path>`) with proof timeouts.

`--launch` checks the toolchain and holds `launcher.lock`, so overlapping schedules skip. It then
runs the workflow with Atomic's programmatic `run(definition, inputs)` API, passing the new run
IDs as `pulseRunIds`. Offline options are `--runs-file <listing.json>` and `--no-remote`.

To schedule it every 6 hours on Windows (not registered by the setup):

```text
schtasks /Create /TN "z3 fstar-proof-checking" /SC HOURLY /MO 6 /F ^
  /TR "\"%USERPROFILE%\.bun\bin\bun.exe\" C:\z3atomic\fstar\workflow\continuity.ts --launch"
```

On the GitHub side, `pulse-checker-build.yml` → `pulse-checker-regressions.yml` →
`pulse-checker-repair.md` (`workflow_run`) keeps producing the reports this launcher picks up.

## Design notes

* **Child workflows.** `goal`, `ralph` and `adversarial-verification` were considered and not
  used:
  * `ctx.parallel` accepts only task steps, so per-slice children cannot fan out under one core
    budget.
  * The gate needs a domain-specific verdict (toolchain availability, final commands) and a
    deterministic soundness scan, not a generic rubric score.
  * The builtins' PR stages would conflict with the single-branch lifecycle above.

  Instead there is one fresh worker, one fresh verifier and one deterministic gate per slice.
* **Failure isolation.** Slice stages are started with `Promise.allSettled` over `ctx.task`, not
  `ctx.parallel`, because `ctx.parallel` rejects the whole set when one step fails and would
  discard the sibling verdicts. A failed slice stage counts as "no verdict", so the slice is
  `unverified`. As a result a provider outage in one slice does not pause the whole run.
* **Models.** Stages are unpinned and use the session model.
* **Steering.** The run context is wrapped with `withSteeringPropagationContext`. The soundness
  and scope contracts in each prompt are protected with `keepContext`.

## Tests

```text
bun test fstar/workflow
```

The tests cover:

* report normalization against excerpts of real artifacts (see `tests/fixtures/README.md`);
* build-log parsing and theory classification;
* retrigger conditions;
* lock contention, stale-lock reclaim, and serialization across four processes;
* dedup, backoff and claims;
* core allocation (≤ 32) and distinct worktrees and branches;
* worktree creation with long Windows paths;
* the soundness gate;
* the publication lifecycle with a fake git/gh that models the remote;
* the workflow itself: a dry run through Atomic's `run()`, and full-iteration topology with
  scripted durable steps.

The suite needs Bun and an installed `@bastani/atomic` package (located with
`ATOMIC_PACKAGE_DIR`, `npm root -g`, or `atomic` on `PATH`).

## Limitations

* F*, OCaml/opam and Cherry were not available on the machine where this workflow was set up.
  The repair, verification and integration stages have only been exercised with scripted
  stand-ins, and no proof was checked during setup.
* Slow obligations are per top-level F* declaration (`process_one_decl`), not per SMT query.
* Local corpus scans need a checker executable that runs on the host. The native checkers are
  Linux builds, normally run in WSL.
* The batch harness always takes the first `localCaseLimit` inputs in sorted order.
* With `publish=dry-run` or `none`, verified work stays on local
  `fstar-proof-checking/integration/<run>` branches, and the findings are still recorded as
  resolved.
* Crash bug reports are drafted by the crash slice, so a slice that writes no
  `bug-report.md` files nothing.

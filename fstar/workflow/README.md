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
| `lib/atomic-host.ts` | Locates the installed Atomic package and loads its SDK modules for the tests. |
| `lib/launch.ts`, `lib/node-run.ts` | The launcher's workflow run in a Node child process (Atomic's runtime). |
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
  worktrees, or change state: finding statuses, claims, processed-report cursors, scan offsets
  and pending publications stay byte-identical. Use it with `reportPaths` to inspect slicing
  and the 32-core plan.
* With the default `publish=dry-run`, a real run repairs and verifies findings and merges
  verified slices into a local integration branch. It queries GitHub only to plan publication.
  Its verified findings become `integrated` (not `resolved`) and the integration branch is
  recorded as a pending publication. `publish=live` pushes and opens or updates the PR and files
  crash reports; its first iteration also merges, re-verifies and pushes every pending
  publication, even when there are no new findings. `publish=none` never contacts the remote
  for publication.

The important inputs are `pulseRunIds`, `reportPaths`, `localCorpora`, `theories`,
`maxIterations` (1–5), `coreBudget` (≤ 32), `coresPerSlice`, `publish` and `dryRun`, plus the
toolchain inputs below. `/workflow inputs fstar-proof-checking` lists them all.

### Toolchain discovery

The checker is built and run on Linux, as in `pulse-checker-build.yml`: directly on a Linux host,
and inside a WSL distribution on Windows. The preflight first picks the build environment: the
`wslDistro` input, else `Z3_FSTAR_WSL_DISTRO`, else the first WSL distribution that has bash,
Ubuntu first. Docker's utility distributions are skipped, and the default distribution is not
assumed. In that environment it then looks for:

| Tool | Input / environment variable | Searched otherwise |
|---|---|---|
| F* `v2026.09.27` | `fstarExe` / `FSTAR_EXE` | `fstar.exe` on `PATH`, `~/.local/share/z3-clause-proofs-*/fstar-ci-v*/bin/fstar.exe`, `~/.cache/z3-pulse-*/fstar/bin/fstar.exe` |
| Cherry-capable F* (optional) | `cherryFstarExe` / `CHERRY_FSTAR_EXE` | `~/.local/share/z3-clause-proofs-*/fstar-nightly-*/bin/fstar.exe` |
| OCaml 5.3 opam switch | `opamRoot` / `Z3_FSTAR_OPAMROOT`; `opamSwitch` (default `fstar53`) | `$OPAMROOT` or `~/.opam`, `~/.local/share/z3-clause-proofs-*/opam`, `~/.cache/z3-pulse-*/opam` |
| Linux PowerShell 7 for `build_ocaml_checker.ps1` | `pwshExe` / `Z3_FSTAR_PWSH` | `pwsh` on `PATH`, `/opt/microsoft/powershell/7/pwsh`, `/mnt/c/Users/*/.copilot/session-state/*/files/linux-pwsh-*/pwsh` |
| Python 3 | none | `python3` on `PATH` |
| OCaml and Cherry checker builds | `ocamlChecker` / `Z3_FSTAR_CHECKER`; `cherryChecker` / `Z3_FSTAR_CHERRY_CHECKER` | the newest of `~/.local/share/z3-clause-proofs-*/{ci-fixed-checker, published-checkers/pulse-checker-*-linux-x86_64, checker, cherry-checker}`, `~/.cache/z3-pulse-*/checker`, `~/z3checker` |

A candidate counts only if it actually runs (`--version`, `ocamlc -version` through `opam exec`,
a PowerShell version query). Paths are paths inside the build environment, and every candidate
examined is recorded under `toolchain.candidates` in `runs/<runKey>/setup.json`. PowerShell runs
with `DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1`, because the portable Linux build aborts without
ICU otherwise, and with a private `XDG_CACHE_HOME`: a corrupted `~/.cache/powershell` startup
cache makes it crash (`FileLoadException: The given assembly name was invalid`). A PowerShell
that is found but still fails to run is reported as such, with its error output, under
`pwsh-failed` in the candidates and in the blocked reason, instead of as missing.

Stages receive the exact commands. On this machine the build and test command looks like:

```text
wsl -d Ubuntu -e bash -lc 'cd /mnt/c/<worktree> && export OPAMROOT=… && eval "$(opam env --switch=fstar53 --set-switch)" &&
  mkdir -p "$HOME/.cache/fstar-proof-checking/<key>/xdg-cache" &&
  DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1 XDG_CACHE_HOME="$HOME/.cache/fstar-proof-checking/<key>/xdg-cache"
  <pwsh> -NoProfile -File fstar/tools/build_ocaml_checker.ps1 -FstarExe <F*>
  -OpamSwitch fstar53 -Z3WindowsBuildDir "$HOME/.cache/fstar-proof-checking/<key>/z3" -Z3BuildDir … -CacheDir …
  -WslBuildDir … -BuildJobs <cores> -RunTests [-BuildCherry -CherryFstarExe <Cherry F*>]'
```

Each slice, its verifier (`<key>-verify`) and the integration check build into their own
directories, with their own PowerShell cache, so parallel slices never share a Z3 build, F*
cache, checker or startup cache. Local corpora run the discovered checkers through
`wsl -d <distro> -e <checker>`, and the batch harness runs as `python3` in the same environment
with `/mnt/<drive>/…` paths.

A real run needs F*, the opam switch and PowerShell. Without them it ends **blocked** before any
agent stage, naming each missing tool and the input that supplies it. It never reports unchecked
work as verified.

## What one run does

```text
preflight → reconcile-publications → source → record-sources
  ─┬─ iter-i/triage ──(nothing actionable → stop)
   │     └─ iter-i/plan  (theory slices, ≤32 cores, worktrees, claims)
   │          ├─ iter-i/<slice>/repair   one fresh stage per slice, in its worktree
   │          ├─ iter-i/<slice>/verify   fresh, schema-backed independent verifier
   │          └─ iter-i/gate → iter-i/integrate → iter-i/integration/verify
   │                         → iter-i/publish → iter-i/persist
   └─ investigate/select → investigate/{checker-scalability, certificate-reformulation, diagnostics-ux} → finalize
```

0. **Reconcile publications.** Before sourcing, the run asks the remote (read-only
   `git ls-remote` and `gh pr list`) about every branch that carries `resolved` findings and
   applies the status machine below: a merged PR makes its findings `merged`; a branch deleted
   before its PR merged reopens them. Integrated findings that no pending publication carries
   any more are reopened too. `publish=none` skips the remote queries, a dry run changes
   nothing, and state is written only when something changed, so reconciling twice is a no-op.
   The observations are kept in `runs/<runKey>/reconcile.json`.
1. **Source.** The workflow downloads up to `maxReports` unprocessed runs. Regression runs
   provide `pulse-checker-report-<id>-<attempt>` and `pulse-checker-cherry-report-<id>-<attempt>`.
   Failed or timed-out builds provide `pulse-checker-build-report`. Downloads use read-only `gh`
   and are cached under `<stateDir>/reports`. The source step also reads `reportPaths` (report
   directories, or single OCaml, Cherry or F* build logs of any name) and scans local corpora
   with the discovered checkers. `C:/z3test/regressions/smt2` uses the checker's `--interactive
   --stats --diagnostics` mode on a rotating window of `localCaseLimit` files. `C:/bench/inputs`
   (one directory per logic) uses `run_checker_regressions.py run/diagnose/report` on a window
   stratified by top-level directory: `localCaseLimit` cases are shared evenly between the
   directories, so with `localCaseLimit` at least the number of directories (41 for
   `C:/bench/inputs`; the default is 50) every run reaches every logic. Each directory rotates
   through its own files across runs, and with a smaller limit the share of the remainder rotates
   through the directories. The selected files are copied below the run directory and the
   harness checks that copy, because it would otherwise always take the sorted first
   `--max-cases` files of the whole corpus. Finally,
   the step re-sources findings already recorded in state that are eligible now: findings left
   open because the slice capacity was used up, retries whose backoff expired, claims abandoned
   by a crashed run, and reopened findings. A continuity launch for unprocessed partial rules
   therefore always has work to process.

   **Record sources.** Before any iteration can stop early, the run marks every sourced report
   processed, advances the scan windows, and records new findings as `open`, with a snapshot so
   later runs can re-source them. A run that finds nothing actionable, or that is blocked because
   the toolchain is missing, does not see the same reports as new again. Each finding's evidence
   time is when its newest report was produced: the Pulse run's creation time, a local report's
   modification time, or, for a local corpus scan, the build (modification) time of the prebuilt
   checker binary that ran it, because that binary may predate merged fixes. A `merged` finding
   whose evidence changed in a report produced after the merge is reopened here; see the status
   machine below.
2. **Normalize.** Findings are partial-rule families from `diagnostics.jsonl`, checker
   crashes, rejected proofs, whole-case checker timeouts, and F* build proof timeouts
   (`Error … The SMT query timed out`). Declarations whose
   `process_one_decl` time is over 2 s are slow obligations. Each finding has a stable
   fingerprint. The same family seen by several reports or checkers is merged.
3. **Triage.** Resolved and merged findings are skipped, and so are `integrated` ones that a
   pending publication carries (verified and awaiting publication). So are findings claimed by
   another run, in backoff, or blocked (unless their evidence changed). The rest are ordered:
   crashes, possible unsoundness, build timeouts, partial rules by affected proofs, checker
   timeouts, then slow proofs.
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
   * The diff passes the deterministic soundness scan of its added lines, in every changed text
     file:
     * F* sources (`.fst`, `.fsti`, `.fsx`): `admit` and `tadmit` with their variants
       (`admit_all`, `admitP`, `admit_dump`, `tadmit_t`, `admit_smt_queries`), `magic`,
       `unsafe_coerce`, and every `assume` (`assume val`, `assume type`, `assume new type`,
       `assume e`, Prims' `_assume`, Pulse's `assume_`), also qualified
       (`Pulse.Lib.Core.assume_`). A name counts only as a whole identifier (`_` and `'` are
       identifier characters), so `admitted`, `assumed` or `my_assume` pass.
     * OCaml sources (`.ml`, `.mli`, such as `fstar/ocaml_runtime`): `Obj.magic`, `Obj.repr`
       and `Obj.obj`, also qualified (`Stdlib.Obj.magic`).
     * Every file, including Makefiles, `*.mk`, shell, PowerShell, Python, JSON and YAML build or
       CI configuration: `admit_smt_queries`, `--admit_except`, `--lax`, `--z3rlimit_factor` and
       `--__no_positivity`. `#` comments in those formats are ignored.
     * A module-wide `--z3rlimit` (`#set-options`, `#reset-options`, or a build flag) above the
       value it replaces (F*'s default is 5). A raise in `#push-options` is only a warning.

     In F* and OCaml sources, comments (`(* … *)`, nested and across lines; `//` in F*),
     character literals (`'"'`, `'\''`, `'\\'`, …) and strings that carry no option are ignored.
     A changed line that still contains an existing escape counts as added, so it is rejected.
   * The verifier lists no soundness concern. Any entry in `soundnessConcerns`, whatever
     severity it is given, keeps the slice (and, at integration, the merged head) from being
     accepted, and is recorded as the reason.

   Anything else is `unverified`, `rejected`, or `no-change`.
7. **Integrate and verify again.** Each iteration merges its verified slices into its own branch
   `fstar-proof-checking/integration/<run>-i<n>`. Its base is the open publication branch, or
   `baseRef` if there is none. Recorded heads of pending publications are merged first, oldest
   first: in a `publish=live` run all of them, otherwise only this run's own earlier verified
   head, so a run's pending head accumulates its verified iterations. A merge whose integration
   verification failed stays on its own iteration's branch and never reaches a later head. The
   merged diff is scanned again, and a fresh stage verifies the merged build before anything is
   published. The integration verifier and the PR body list exactly the slices and finding
   fingerprints the head contains.
8. **Publish.** One branch receives pushes until it is merged or deleted (see below).
9. **Persist.** Under the state lock, the step records outcomes, publication state and pending
   publications. Reports and scan offsets were already recorded by `record-sources`.
   * Verified findings resolve only when a live push included them, and record where:
     `publishedOn` holds the branch, PR, pushed head and time. Otherwise they become
     `integrated` and the run's integration branch and head are recorded as a pending publication.
   * Others back off for 6 h, 12 h, … and are blocked after 3 attempts.
   * A blocked finding is reopened if its evidence changes.
   * Processed-report cursors and scan offsets advance in every real run, whatever `publish` is,
     because the findings themselves are kept in state. Only `dryRun=true` leaves them alone.
10. **Investigate.** Three report-only stages run when the findings changed since the last
    investigation (`excludedTools: edit, write`):
    * checker refactoring for speed and scalability, including finite-field checker optimizations;
    * Z3 certificate reformulation;
    * diagnostics and UX: rules-checked counts for PARTIAL and ACCEPT, and an admit-diagnostics mode.

A run stops when nothing is actionable, at `maxIterations`, after two iterations in a row
without a verified slice, or in a blocked state. Blocked states are a missing toolchain, a PR
closed without merging, and a push the remote refused as non-fast-forward. Each has an
actionable reason in the `summary` output.

## Publication lifecycle

Publication state is stored as `activeBranch`, `prNumber` and `sequence`. One rule
(`decideActiveBranch` in `lib/publish.ts`) decides what happens to the active branch, and both
the integration base and the push use it, so they always agree:

| Remote state of the active branch | Action |
|---|---|
| No active branch | Push `fstar-proof-checking/<n+1>` (the first free name) and open a PR. |
| PR open (even if an earlier PR from the same branch merged) | Integrate on top of the branch and push to it; no new PR. |
| Branch exists, no PR (e.g. an interrupted earlier run) | Integrate on top of the branch, push and open the PR. Every `gh pr create` is preceded by `gh pr list --state open`, so re-running never duplicates a PR. |
| PR merged (and none open) | Start `fstar-proof-checking/<n+1>` from `baseRef` and a new PR. |
| Branch deleted | Start a new branch and PR. Findings published on the deleted branch whose PR never merged are reopened (see below). |
| PR closed without merging, branch still there | **Blocked.** Reopen the PR, or delete the branch to start a new one (which reopens its findings). |
| The remote refuses the push as non-fast-forward (someone pushed to the branch meanwhile) | **Blocked**, never forced. The verified work stays `integrated` and pending; merge or remove the other commits, then relaunch. |

Crash reports carry the hidden marker `fstar-proof-checking:crash:<fingerprint>` and are filed in
FStarLang/FStar only with `publish=live`, after a search for that marker finds nothing.
All git and gh calls go through one command runner and are logged to
`<runDir>/commands.jsonl`. Pushes and PR or issue edits are flagged `mutating`, and
`evidence.json` lists the flagged entries. The tests check that dry runs issue no flagged command.

### Pending publications

Verified work that a run did not push (`publish=dry-run` or `none`, or a live run that ended
blocked) is kept in `state.json` under `pendingPublications`: the run key, the local
integration branch, its verified head, and exactly the findings and slices that head contains.
Its findings stay `integrated`, so they are neither repaired again nor lost. A run keeps one
entry: a later verified iteration of the same run merges the run's earlier head into its own
and replaces the entry.

The first iteration of the next `publish=live` run picks these up even without new findings.
It merges each recorded head into its integration branch, oldest first, scans the merge, and
verifies the merged build. Then it pushes by the lifecycle above: to the active branch while its
PR is open, or to a new branch and PR after a merge or deletion. Only after that push succeeds
do the findings resolve and the entries leave the list. An entry whose local branch is missing,
or whose merge conflicts or fails the soundness scan, stays pending with the reason in
`lastError`. Recreate the branch, or remove the entry from `state.json`: its findings are then
reopened by the next run and repaired again.

### Finding status machine

Every status change is appended to the finding's `transitions` (the last ten, each with time,
old and new status, and reason; a reopen also keeps the publication it gave up).

```text
open ──claim──▶ in_progress ──verified, not pushed──▶ integrated ──live push──▶ resolved ──PR merged──▶ merged
                     │                                                (publishedOn)            (mergedAt)
                     ├──failed──▶ unverified (backoff 6 h, 12 h, …) ──backoff over──▶ eligible again
                     └──failed 3 times──▶ blocked ──evidence changed──▶ claimed again
```

Reopen edges, all back to `open` with attempts reset and the reason recorded:

* **Publication lost** (`reconcile-publications`): a `resolved` finding's branch no longer exists
  and its PR never merged, because the PR was closed and the branch deleted, or the branch was
  deleted early. The transition keeps the lost branch, PR number and pushed head. Deleting a
  branch after its PR merged is not a loss.
* **Evidence after the merge** (`record-sources`): a `merged` finding shows up in a report
  produced after `mergedAt` with a different evidence digest (rule, detail or examples). If the
  report's production time is unknown, the changed evidence alone reopens it. A report produced
  before the merge, or with unchanged evidence, keeps it `merged`, with `keptReason` saying why.
  Local scans count from their checker binary's build time (OCaml and Cherry each from their own
  binary, in interactive and batch mode): a scan by a checker built before the merge keeps the
  finding `merged`, and a scan by a checker whose build time is unknown never reopens it.
* **Orphaned integration** (`reconcile-publications`, also counted by the continuity check): an
  `integrated` finding that no `pendingPublications` entry carries.

A `resolved` finding whose PR is still open (or closed while its branch still exists) is never
reopened by newer reports: master does not contain the fix yet. Its `keptReason` records this.
Reopened findings are re-sourced from state, so the next run's triage selects them, and they
count as unprocessed for the continuity check.

## State and evidence

`<stateDir>` defaults to `.atomic/fstar-proof-checking/`, which is ignored by git.

* `state.json` holds processed reports, per-finding status, attempts, backoff and claims, the
  publication branch and PR, pending publications, bug reports, local-scan offsets, and run
  history. Every change runs under the exclusive `state.lock`, which is reclaimed if it is stale
  or its process is dead. The file is replaced by write-then-rename.
* `reports/` caches downloaded artifacts.
* `runs/<runKey>/` holds:
  * `setup.json`, `reconcile.json` (the branch observations and status changes of
    `reconcile-publications`), `findings.json`, `commands.jsonl` and `evidence.json`;
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
bun fstar/workflow/continuity.ts --launch --publish live # same, and push verified work (including pending publications)
bun fstar/workflow/continuity.ts --launch --dry-run      # same, but dryRun=true, publish=dry-run, in-memory journal
```

The launcher runs under Bun, but the workflow run it starts executes in a child `node`
process (Node.js 22.19 or newer on `PATH`, the runtime of an npm-installed Atomic). Atomic's
persistent storage needs `node:sqlite`, which Bun 1.3 does not provide: the workflow journal
and the stage sessions (both in `~/.atomic/workflows/journal.sqlite` by default) and the
Intercom extension of every stage session. The launched run uses Atomic's default journal
(`ATOMIC_WORKFLOW_JOURNAL_PATH` and the `workflows.journal` setting apply), so Atomic can inspect
and resume it; `--journal <path>` selects another SQLite file, also for a `--dry-run`.

It evaluates the three conditions from the instructions:

1. A new, unprocessed Pulse regression report. Only completed `success` or `failure` runs on
   `--branch` (default `master`) count; skipped and approval-gated runs do not.
2. Partial proof rule families recorded in state that are not yet processed: open, out of
   backoff, or with an expired claim.
3. A failed `pulse-checker-build` run whose `build.log` contains SMT proof timeouts, a timed-out
   build job, or a local OCaml or Cherry build log (`--build-log <path>`, any file name) with
   proof timeouts. The launcher passes the log itself as a `reportPaths` entry, and the run
   records it under the same key, `local-build:<path>@<mtime>`. A processed log therefore does
   not retrigger again until it is rewritten.

`--launch` checks the toolchain, creates the state directory if it does not exist yet (`.atomic/`
is ignored, so a fresh clone has none), and holds `<state-dir>/launcher.lock`. A lock held by
another live launcher is an overlapping schedule: the launch is `skipped` with exit code 0. Any
other locking failure (for example, an unusable `--state-dir`) is reported as `failed` with exit
code 1, so a scheduler sees it. It then
runs the workflow with Atomic's programmatic `run(definition, inputs)` API, passing the new run
IDs as `pulseRunIds` and `--publish` (if given) as `publish`. The flags `--wsl-distro`,
`--opam-root`, `--opam-switch`, `--fstar`, `--cherry-fstar`, `--pwsh`, `--ocaml-checker` and
`--cherry-checker` override toolchain discovery, both for the launcher's check and for the
launched run. A run that ends without a status (Node missing, the workflow failing to load, a
journal that cannot be opened) is reported as `failed` with exit code 1; its `failure` names the
phase (`runtime`, `load`, `storage` or `run`) and the error class, and the stack is on stderr.
Offline options are `--runs-file <listing.json>` and `--no-remote`. The decision also reports
`pendingPublications`, the number of verified integrations waiting for a live push. That count
is not a retrigger condition. Pending work is pushed by the next live run, whatever started it.

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
* retrigger conditions, and the continuity loop end to end through the real launcher CLI: a
  partial-rule retrigger gives the launched run those rules, and a processed local build log
  does not retrigger until it is rewritten;
* toolchain discovery on a Windows host with a scripted `wsl` (a default distribution without
  bash; Ubuntu with a custom OPAMROOT, Linux F*, Cherry and checker builds; a PowerShell that is
  found but crashes), private PowerShell caches per build, and local corpus scans through the
  WSL checker;
* batch corpus rotation: every run reaches every logic directory, the next run takes the next
  files, the harness checks a staged copy, and a dry run moves nothing;
* lock contention, stale-lock reclaim, and serialization across four processes;
* dedup, backoff and claims;
* core allocation (≤ 32) and distinct worktrees and branches;
* worktree creation with long Windows paths;
* the soundness gate, including `magic`, `tadmit_t`, `admit_all`, `assume type`, `assume e`,
  `_assume`, Pulse's `assume_`, `--__no_positivity`, admits hidden after a `'"'` character
  literal, OCaml `Obj.magic`/`Obj.repr`/`Obj.obj`, `#reset-options` and build-flag rlimit raises,
  `--z3rlimit_factor`, `--admit_except`, Makefile, shell and CI flags, comments, character
  literals and identifiers that must not count, and verifier soundness concerns;
* the publication lifecycle with a fake git/gh that models the remote;
* pending publications and integration, using real git with a local bare remote and a scripted
  gh: dry-run verified work stays `integrated` and pending with no remote mutation; a later live
  run without new findings pushes it to a new branch and PR, or to a new branch after the active
  PR was merged; a missing pending branch stays pending with its reason; a merge whose
  integration verification failed never reaches the next iteration's pending head; a run's
  verified iterations accumulate in one pending entry; an integration verifier's soundness
  concern blocks the live push;
* the finding status machine with the same real git and scripted gh: a PR closed without merging
  whose branch was deleted reopens its findings (keeping the lost branch, PR and head) and the
  next run repairs and republishes them on a new branch; a branch deleted before any merge also
  reopens, and reconciling again leaves `state.json` byte-identical; a merged finding is reopened
  (and counted as unprocessed) only by changed evidence from a report produced after the merge;
  while the PR is open, newer reports keep it resolved; an integrated finding whose pending entry
  was removed is reopened; with an OPEN and a MERGED PR on the active branch, integration builds
  on that branch and the push fast-forwards, and a push the remote refuses as non-fast-forward
  ends blocked with the work pending and nothing forced; a local scan by a checker built before
  the merge keeps a merged finding, one by a checker built after it reopens it, and one by a
  checker of unknown build time never does; each backend's scans carry its own binary's build
  time in interactive and batch mode;
* the launcher lock: a fresh state directory is created and launched into, a live launcher's
  lock skips with exit 0, and any other lock failure is reported as failed with a nonzero exit;
* the workflow itself: dry runs through Atomic's `run()` (including that existing state stays
  byte-identical), full-iteration topology with scripted durable steps, a live run that
  continues past triage only to publish pending work, and runs that stop in iteration 1
  (nothing actionable, or toolchain missing) yet record their reports and findings.

The suite is hermetic: the workflow tests replace the preflight's toolchain probe and every
other test scripts its commands, so `bun test` never runs the host's `wsl`, opam, F* or
PowerShell. The one test that probes the real toolchain is skipped unless
`FSTAR_WORKFLOW_REAL_TOOLCHAIN=1` is set.

The suite needs Bun and an installed `@bastani/atomic` package (located with
`ATOMIC_PACKAGE_DIR`, `npm root -g`, or `atomic` on `PATH`).

## Limitations

* During setup, discovery found the WSL Ubuntu toolchain on this machine. The discovered checkers
  ran on z3test regressions in interactive mode, and the discovered F* verified a scratch module
  and `fstar/Z3AstTheory.fst`, the first checker module. The full `build_ocaml_checker.ps1` build
  and the repair, verification and integration agent stages were not run during setup; those
  stages have only been exercised with scripted stand-ins.
* On this machine the Linux PowerShell is found under `~/.copilot/session-state`. Installing
  `pwsh` in the WSL distribution, or setting `Z3_FSTAR_PWSH`, is more durable.
* Local checkers are the newest existing builds, which may predate the checked-out sources. A
  slice's verifier always rebuilds from its own worktree.
* Slow obligations are per top-level F* declaration (`process_one_decl`), not per SMT query.
* With `publish=dry-run` or `none`, verified work stays on local
  `fstar-proof-checking/integration/<run>-i<n>` branches until a `publish=live` run pushes it (see
  Pending publications). Deleting such a branch before then leaves its entry pending with a reason.
* PowerShell and the checker build run with a private `XDG_CACHE_HOME` per build, so caches
  under it (for example dune's) are not shared between builds.
* Crash bug reports are drafted by the crash slice, so a slice that writes no
  `bug-report.md` files nothing.

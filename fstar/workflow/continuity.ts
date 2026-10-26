/**
 * Continuity launcher for the `fstar-proof-checking` workflow.
 *
 *   bun fstar/workflow/continuity.ts --check  [--dry-run] [options]
 *   bun fstar/workflow/continuity.ts --launch [--dry-run] [options]
 *   bun fstar/workflow/continuity.ts --requeue-policy-blocked all|<fingerprint>[,...] [--dry-run]
 *   bun fstar/workflow/continuity.ts --reconcile-policy-blocked <atomicRunId> [--journal <path>] [--dry-run]
 *   bun fstar/workflow/continuity.ts --release-candidate all|<fingerprint>[,...] --decision <text> [--dry-run]
 *
 * --check   evaluates the three retrigger conditions from fstar/workflow-instructions.txt and
 *           prints a JSON decision: a new Pulse report, unprocessed partial proof rules, or an
 *           OCaml/Cherry checker build that timed out on proofs. GitHub access is read-only.
 * --launch  additionally starts one bounded workflow run through Atomic's programmatic
 *           `run(definition, inputs)` API when a condition holds, holding a launcher lock so
 *           scheduled invocations never overlap (it creates the state directory if missing).
 *           A lock held by another live launcher skips the launch (exit 0); any other locking
 *           failure is reported as `failed` (exit 1). A bounded run does not retrigger itself;
 *           schedule this launcher (see README) to get continuity. The run executes in a Node
 *           child process (Atomic's runtime; `node` on PATH, see lib/launch.ts): Atomic's SQLite
 *           storage needs `node:sqlite`, which Bun 1.3 lacks. A run that ends without a status
 *           is `failed` (exit 1) with `failure.phase` runtime, load, storage or run.
 * --dry-run never launches a live run: with --launch it runs the workflow with
 *           `dryRun: true, publish: "dry-run"` and an in-memory journal (unless --journal).
 * --journal <path> SQLite journal file for the launched run. Default: Atomic's own selection
 *           (ATOMIC_WORKFLOW_JOURNAL_PATH, settings, or ~/.atomic/workflows/journal.sqlite).
 * --publish none|dry-run|live is passed to the launched run (default: the workflow's `dry-run`).
 *           Verified work from non-live runs stays pending in state; a `--publish live` launch
 *           pushes it together with its own work.
 *
 * --requeue-policy-blocked all|<fingerprint>[,<fingerprint>...]
 *           moves findings held as `provider_policy_blocked` (an agent stage was rejected by the
 *           provider for policy, for example `cyber_policy`) back to `open`. Run it only once the
 *           restriction is resolved; with --dry-run it only lists what it would requeue.
 * --reconcile-policy-blocked <atomicRunId>
 *           reconciles state with a run that ended without persisting its outcomes, from its journal
 *           and stage sessions, read read-only (in a `node` child) from --journal (default
 *           ATOMIC_WORKFLOW_JOURNAL_PATH or ~/.atomic/workflows/journal.sqlite, which also holds the
 *           sessions by default). The findings of its policy-blocked stages, which a workflow version
 *           without provider classification recorded as failed attempts (or left claimed), are held
 *           with that attempt and backoff undone. Its other claims are released to `open`; findings
 *           whose slice branch carries a commit beyond the run's base keep it as `candidate`
 *           ({runKey, branch, commit}), which keeps them out of automatic work. It changes nothing
 *           while the run is active: a `running` run counts as ended (`crashed`, as Atomic reports
 *           it) only once its journal lease is unheld or older than Atomic's two-minute expiry on the
 *           journal clock. It never claims, takes over or resumes the run; do not resume it afterwards.
 *           With --dry-run it only reports what it would do.
 * --release-candidate all|<fingerprint>[,<fingerprint>...] --decision <text>
 *           clears the candidate of findings once its commit has been verified and decided on,
 *           recording the decision; automatic runs may then repair them. --dry-run only lists them.
 *
 * Options: --state-dir <dir> (default .atomic/fstar-proof-checking), --repo <owner/name>,
 *          --branch <name> (Pulse runs to consider; default master, "" for all),
 *          --runs-file <json> (offline `{regressions, build}` gh listings instead of gh),
 *          --build-log <path> (repeatable; local OCaml/Cherry build logs), --no-remote.
 * Toolchain discovery overrides (also passed to the launched run): --wsl-distro, --opam-root,
 *          --opam-switch, --fstar, --cherry-fstar, --pwsh, --ocaml-checker, --cherry-checker.
 */
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, isAbsolute, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnRunner } from "./lib/command.js";
import { evaluateContinuity, launchExclusively, type BuildEvidence } from "./lib/continuity.js";
import { committedBeyond } from "./lib/git.js";
import { readRunEvidenceInNode, runWorkflowInNode } from "./lib/launch.js";
import { policyHoldsFromRun } from "./lib/provider.js";
import { parseBuildLog } from "./lib/reports.js";
import { downloadRunReports, fromGhRuns, listPulseRuns, localReportKey, reportingRuns, reportKey, type PulseRun } from "./lib/sources.js";
import {
  holdPolicyBlocked, readState, releaseCandidates, releaseInterruptedClaims, requeuePolicyBlocked, withStateLock,
  type CandidateWork, type PolicyHold, type WorkflowState,
} from "./lib/state.js";
import { probeToolchain } from "./lib/toolchain.js";

interface Options {
  mode: "check" | "launch" | "requeue" | "reconcile" | "release-candidate";
  /** --requeue-policy-blocked: `all` or the fingerprints. */
  requeue?: "all" | string[];
  /** --reconcile-policy-blocked: the Atomic run id. */
  reconcileRunId?: string;
  /** --release-candidate: `all` or the fingerprints, and the operator's --decision. */
  releaseCandidates?: "all" | string[];
  decision?: string;
  dryRun: boolean;
  publish?: "none" | "dry-run" | "live";
  stateDir: string;
  repo: string;
  branch: string;
  runsFile?: string;
  buildLogs: string[];
  remote: boolean;
  /** Journal file for the launched run; default Atomic's own (memory for --dry-run). */
  journal?: string;
  /** Toolchain discovery overrides, passed to the preflight probe and to the launched run. */
  toolchain: Record<string, string>;
}

/** Launcher flags for toolchain discovery and the workflow inputs they set. */
const TOOLCHAIN_FLAGS: Record<string, string> = {
  "--wsl-distro": "wslDistro", "--opam-root": "opamRoot", "--opam-switch": "opamSwitch", "--fstar": "fstarExe",
  "--cherry-fstar": "cherryFstarExe", "--pwsh": "pwshExe", "--ocaml-checker": "ocamlChecker", "--cherry-checker": "cherryChecker",
};

function parseArgs(argv: string[], repoRoot: string): Options {
  const options: Options = { mode: "check", dryRun: false, stateDir: ".atomic/fstar-proof-checking", repo: "Z3Prover/z3", branch: "master", buildLogs: [], remote: true, toolchain: {} };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    const value = () => {
      const next = argv[++index];
      if (next === undefined) throw new Error(`${arg} requires a value`);
      return next;
    };
    if (arg === "--check") options.mode = "check";
    else if (arg === "--launch") options.mode = "launch";
    else if (arg === "--dry-run") options.dryRun = true;
    else if (arg === "--requeue-policy-blocked") {
      const selector = value();
      options.mode = "requeue";
      options.requeue = selector === "all" ? "all" : selector.split(",").map((item) => item.trim()).filter(Boolean);
    }
    else if (arg === "--reconcile-policy-blocked") {
      options.mode = "reconcile";
      options.reconcileRunId = value();
    }
    else if (arg === "--release-candidate") {
      const selector = value();
      options.mode = "release-candidate";
      options.releaseCandidates = selector === "all" ? "all" : selector.split(",").map((item) => item.trim()).filter(Boolean);
    }
    else if (arg === "--decision") options.decision = value();
    else if (arg === "--publish") {
      const mode = value();
      if (mode !== "none" && mode !== "dry-run" && mode !== "live") throw new Error(`--publish must be none, dry-run or live, not ${mode}`);
      options.publish = mode;
    }
    else if (arg === "--no-remote") options.remote = false;
    else if (arg === "--journal") options.journal = resolve(value());
    else if (arg === "--state-dir") options.stateDir = value();
    else if (arg === "--repo") options.repo = value();
    else if (arg === "--branch") options.branch = value();
    else if (arg === "--runs-file") options.runsFile = value();
    else if (arg === "--build-log") options.buildLogs.push(value());
    else if (arg !== undefined && arg in TOOLCHAIN_FLAGS) options.toolchain[TOOLCHAIN_FLAGS[arg] as string] = value();
    else throw new Error(`Unknown argument ${arg}`);
  }
  if (options.mode === "release-candidate" && !options.decision?.trim()) throw new Error("--release-candidate requires --decision <text>");
  if (!isAbsolute(options.stateDir)) options.stateDir = resolve(repoRoot, options.stateDir);
  return options;
}

async function listRuns(options: Options): Promise<{ runs: PulseRun[]; note: string }> {
  if (options.runsFile) {
    const listing = JSON.parse(readFileSync(options.runsFile, "utf8")) as { regressions: []; build: [] };
    return { runs: [...fromGhRuns(listing.regressions, "regressions"), ...fromGhRuns(listing.build, "build")], note: `runs from ${options.runsFile}` };
  }
  if (!options.remote) return { runs: [], note: "remote listing disabled (--no-remote)" };
  return { runs: await listPulseRuns(spawnRunner, { repo: options.repo, limit: 20, branch: options.branch || undefined }), note: `gh run list --repo ${options.repo}` };
}

/** Proof-timeout evidence for unprocessed failed builds (downloaded once into the report cache) and local logs. */
async function buildEvidence(runs: readonly PulseRun[], options: Options, processed: Record<string, unknown>): Promise<BuildEvidence[]> {
  const evidence: BuildEvidence[] = [];
  const builds = reportingRuns(runs).filter((run) => run.workflow === "build" && !(reportKey(run) in processed));
  if (options.remote && !options.runsFile) {
    for (const run of builds) {
      const report = await downloadRunReports(spawnRunner, run, { repo: options.repo, cacheDir: join(options.stateDir, "reports") });
      const log = join(report.directory, "pulse-checker-build-report", "build.log");
      evidence.push({ key: report.key, proofTimeouts: existsSync(log) ? parseBuildLog(readFileSync(log, "utf8")).timeouts.length : 0 });
    }
  }
  for (const path of options.buildLogs) {
    const absolute = resolve(path);
    // Same key the workflow records when it ingests this log through `reportPaths`.
    evidence.push({ key: localReportKey(absolute), proofTimeouts: parseBuildLog(readFileSync(absolute, "utf8")).timeouts.length, reportPath: absolute });
  }
  return evidence;
}

/** Release held provider-policy-blocked findings (the restriction was resolved); --dry-run only lists them. */
async function requeue(options: Options): Promise<number> {
  const selector = options.requeue ?? [];
  const now = new Date();
  const result = options.dryRun
    ? requeuePolicyBlocked(readState(options.stateDir), selector, now)
    : await withStateLock(options.stateDir, (state) => {
      const next = requeuePolicyBlocked(state, selector, now);
      return { ...(next.requeued.length > 0 ? { state: next.state } : {}), result: next };
    }, { owner: `requeue-${process.pid}` });
  console.log(JSON.stringify({ mode: "requeue-policy-blocked", dryRun: options.dryRun, stateDir: options.stateDir, applied: !options.dryRun && result.requeued.length > 0, requeued: result.requeued, notHeld: result.notHeld }, null, 2));
  return 0;
}

/** Clear decided candidates (their commit was verified and decided on); --dry-run only lists them. */
async function releaseCandidate(options: Options): Promise<number> {
  const selector = options.releaseCandidates ?? [];
  const decision = options.decision ?? "";
  const now = new Date();
  const result = options.dryRun
    ? releaseCandidates(readState(options.stateDir), selector, decision, now)
    : await withStateLock(options.stateDir, (state) => {
      const next = releaseCandidates(state, selector, decision, now);
      return { ...(next.released.length > 0 ? { state: next.state } : {}), result: next };
    }, { owner: `release-candidate-${process.pid}` });
  console.log(JSON.stringify({ mode: "release-candidate", dryRun: options.dryRun, stateDir: options.stateDir, decision, applied: !options.dryRun && result.released.length > 0, released: result.released, notCandidates: result.notCandidates }, null, 2));
  return 0;
}

/** Atomic run statuses during which the run may still write state (a `running` run whose lease expired is reported as `crashed`). */
const ACTIVE_RUN = new Set(["running", "paused", "awaiting_input", "pending"]);

/**
 * Commits that the ended run left on the slice branches of its interrupted findings, by fingerprint:
 * a slice branch (iter-<n>/plan.json) with commits beyond the run's base (setup.json `baseRef`, in
 * the run's repository) is a candidate. Only git reads are issued.
 */
async function candidateWork(runKey: string, runDir: string, interrupted: ReadonlySet<string>): Promise<Record<string, CandidateWork>> {
  const candidates: Record<string, CandidateWork> = {};
  if (interrupted.size === 0) return candidates;
  const setupPath = join(runDir, "setup.json");
  const recorded = JSON.parse(readFileSync(setupPath, "utf8")) as { setup?: { repoRoot?: string }; inputs?: { baseRef?: string } };
  const repoRoot = recorded.setup?.repoRoot;
  const base = recorded.inputs?.baseRef;
  if (!repoRoot || !base) throw new Error(`${setupPath} records no repository root or base ref`);
  for (const iteration of readdirSync(runDir).filter((name) => /^iter-\d+$/.test(name))) {
    const planPath = join(runDir, iteration, "plan.json");
    if (!existsSync(planPath)) continue;
    const plan = JSON.parse(readFileSync(planPath, "utf8")) as { slices?: Array<{ branch?: string; fingerprints?: string[] }> };
    for (const slice of plan.slices ?? []) {
      const fingerprints = (slice.fingerprints ?? []).filter((fingerprint) => interrupted.has(fingerprint));
      if (fingerprints.length === 0 || !slice.branch) continue;
      const commit = await committedBeyond(spawnRunner, repoRoot, slice.branch, base);
      if (commit) for (const fingerprint of fingerprints) candidates[fingerprint] = { runKey, branch: slice.branch, commit };
    }
  }
  return candidates;
}

/** Hold the run's policy-blocked findings, then release its remaining claims (keeping candidates). */
function reconcileEnded(state: WorkflowState, runKey: string, holds: readonly PolicyHold[], candidates: Readonly<Record<string, CandidateWork>>, now: Date) {
  const held = holdPolicyBlocked(state, holds, now);
  const released = releaseInterruptedClaims(held.state, { runKey, candidates, now });
  return { state: released.state, held: held.held, candidates: released.candidates, released: released.released, unchanged: held.unchanged };
}

/**
 * Reconcile state with an earlier run, from its durable evidence (journal and stage sessions,
 * read-only) and its plan and integration records: hold the findings of its policy-blocked
 * stages and, once the run has ended, release its other claims (keeping committed work as candidates).
 */
async function reconcile(options: Options, repoRoot: string): Promise<number> {
  const runId = options.reconcileRunId ?? "";
  const database = options.journal ?? (process.env.ATOMIC_WORKFLOW_JOURNAL_PATH || join(homedir(), ".atomic", "workflows", "journal.sqlite"));
  const report: Record<string, unknown> = { mode: "reconcile-policy-blocked", dryRun: options.dryRun, runId, journal: database, stateDir: options.stateDir };
  const evidence = await readRunEvidenceInNode({ runId, database, cwd: repoRoot });
  if (!evidence.ok) {
    console.log(JSON.stringify({ ...report, applied: false, failed: `could not read run ${runId}: ${evidence.error.name}: ${evidence.error.message}` }, null, 2));
    return 1;
  }
  const lease = evidence.lease ?? null;
  if (!evidence.runKey || !evidence.runDir) {
    console.log(JSON.stringify({ ...report, runStatus: evidence.status, journalStatus: evidence.journalStatus, lease, applied: false, failed: "the run has no preflight checkpoint (no run key or evidence directory)" }, null, 2));
    return 1;
  }
  const { runKey, runDir } = evidence;
  const now = new Date();
  const holds = policyHoldsFromRun({ runId, runKey, runDir, at: now.toISOString(), stages: evidence.stages });
  const stages = evidence.stages.filter((stage) => stage.kind !== "completed");
  Object.assign(report, { runStatus: evidence.status, journalStatus: evidence.journalStatus, lease, runKey, runDir, stages });
  if (ACTIVE_RUN.has(evidence.status)) {
    const preview = holdPolicyBlocked(readState(options.stateDir), holds, now);
    const renewed = lease ? ` (its lease was renewed ${Math.round(lease.ageMs / 1000)} s ago on the journal clock)` : "";
    const reason = `run ${runId} is ${evidence.status}${renewed}: state.json is not changed until it ends`;
    console.log(JSON.stringify({ ...report, applied: false, reason, wouldHold: preview.held, unchanged: preview.unchanged }, null, 2));
    return options.dryRun ? 0 : 1;
  }
  // The run has ended: the claims it still holds were interrupted. Their slices' committed work is read before the state lock.
  const heldPreview = holdPolicyBlocked(readState(options.stateDir), holds, now).state;
  const interrupted = new Set(Object.values(heldPreview.findings).filter((record) => record.status === "in_progress" && record.claimedBy === runKey).map((record) => record.fingerprint));
  let candidates: Record<string, CandidateWork>;
  try {
    candidates = await candidateWork(runKey, runDir, interrupted);
  } catch (error) {
    console.log(JSON.stringify({ ...report, applied: false, failed: `could not inspect the run's slice branches: ${error instanceof Error ? error.message : String(error)}` }, null, 2));
    return 1;
  }
  if (options.dryRun) {
    const preview = reconcileEnded(readState(options.stateDir), runKey, holds, candidates, now);
    console.log(JSON.stringify({ ...report, applied: false, reason: "dry run", wouldHold: preview.held, wouldKeepCandidates: preview.candidates, wouldRelease: preview.released, unchanged: preview.unchanged }, null, 2));
    return 0;
  }
  const result = await withStateLock(options.stateDir, (state) => {
    const next = reconcileEnded(state, runKey, holds, candidates, now);
    const changed = next.held.length + next.candidates.length + next.released.length > 0;
    return { ...(changed ? { state: next.state } : {}), result: { ...next, changed } };
  }, { owner: `reconcile-${process.pid}` });
  console.log(JSON.stringify({ ...report, applied: result.changed, held: result.held, candidates: result.candidates, released: result.released, unchanged: result.unchanged }, null, 2));
  return 0;
}

async function main(): Promise<number> {
  const repoRoot = resolve(import.meta.dirname ?? dirname(new URL(import.meta.url).pathname), "..", "..");
  const options = parseArgs(process.argv.slice(2), repoRoot);
  if (options.mode === "requeue") return requeue(options);
  if (options.mode === "reconcile") return reconcile(options, repoRoot);
  if (options.mode === "release-candidate") return releaseCandidate(options);
  const state = readState(options.stateDir);
  const { runs, note } = await listRuns(options);
  const evidence = await buildEvidence(runs, options, state.processedReports);
  const decision = evaluateContinuity({ runs, state, now: new Date(), buildEvidence: evidence });
  const report: Record<string, unknown> = { mode: options.mode, dryRun: options.dryRun, source: note, stateDir: options.stateDir, decision };
  if (options.mode === "check" || !decision.retrigger) {
    console.log(JSON.stringify({ ...report, launched: false }, null, 2));
    return 0;
  }
  if (!options.dryRun) {
    const toolchain = await probeToolchain(spawnRunner, { ...options.toolchain });
    if (!toolchain.available) {
      console.log(JSON.stringify({ ...report, launched: false, blocked: `proof-checking toolchain unavailable: ${toolchain.missing.join("; ")}` }, null, 2));
      return 2;
    }
  }
  const outcome = await launchExclusively(options.stateDir, async () => {
    const inputs = {
      pulseRunIds: decision.pulseRunIds,
      reportPaths: decision.reportPaths,
      stateDir: options.stateDir,
      repo: options.repo,
      pulseBranch: options.branch,
      ...options.toolchain,
      ...(options.publish ? { publish: options.publish } : {}),
      ...(options.dryRun ? { dryRun: true, publish: "dry-run" as const } : {}),
    };
    const journal = options.journal ? { path: options.journal } : options.dryRun ? { memory: true as const } : undefined;
    const run = await runWorkflowInNode({
      workflow: fileURLToPath(new URL("./fstar-proof-checking.ts", import.meta.url)),
      inputs,
      cwd: repoRoot,
      ...(journal ? { journal } : {}),
    });
    return { inputs, journal: journal ?? "atomic-default", run };
  });
  if (outcome.kind === "skipped") {
    // Another launcher holds the lock (an overlapping schedule): not a failure.
    console.log(JSON.stringify({ ...report, launched: false, skipped: outcome.reason }, null, 2));
    return 0;
  }
  if (outcome.kind === "failed") {
    console.log(JSON.stringify({ ...report, launched: false, failed: `could not take the launcher lock: ${outcome.reason}` }, null, 2));
    return 1;
  }
  const { inputs, journal, run } = outcome.value;
  if (!run.ok) {
    // No run status: Node, the workflow module, or Atomic's storage failed (the stack is on stderr).
    const failure = { phase: run.phase, error: run.error.name, message: run.error.message };
    console.log(JSON.stringify({ ...report, launched: false, inputs, journal, failed: `workflow run failed before reporting a status (${run.phase}): ${run.error.name}: ${run.error.message}`, failure }, null, 2));
    return 1;
  }
  console.log(JSON.stringify({ ...report, launched: true, inputs, journal, runId: run.runId, status: run.status, error: run.error, result: run.result }, null, 2));
  return run.status === "completed" ? 0 : 1;
}

main().then((code) => process.exit(code), (error) => {
  console.error(error instanceof Error ? error.stack ?? error.message : String(error));
  process.exit(1);
});

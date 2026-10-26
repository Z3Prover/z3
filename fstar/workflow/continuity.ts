/**
 * Continuity launcher for the `fstar-proof-checking` workflow.
 *
 *   bun fstar/workflow/continuity.ts --check  [--dry-run] [options]
 *   bun fstar/workflow/continuity.ts --launch [--dry-run] [options]
 *   bun fstar/workflow/continuity.ts --requeue-policy-blocked all|<fingerprint>[,...] [--dry-run]
 *   bun fstar/workflow/continuity.ts --reconcile-policy-blocked <atomicRunId> [--journal <path>] [--dry-run]
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
 *           holds the findings of that run's policy-blocked stages, which a workflow version without
 *           provider classification recorded as failed attempts (or left claimed): it reads the
 *           run's journal and stage sessions read-only (in a `node` child) from --journal (default
 *           ATOMIC_WORKFLOW_JOURNAL_PATH or ~/.atomic/workflows/journal.sqlite, which also holds the
 *           sessions by default), and undoes that run's attempt and backoff for them. It changes
 *           nothing while the run is still active; with --dry-run it only reports what it would do.
 *
 * Options: --state-dir <dir> (default .atomic/fstar-proof-checking), --repo <owner/name>,
 *          --branch <name> (Pulse runs to consider; default master, "" for all),
 *          --runs-file <json> (offline `{regressions, build}` gh listings instead of gh),
 *          --build-log <path> (repeatable; local OCaml/Cherry build logs), --no-remote.
 * Toolchain discovery overrides (also passed to the launched run): --wsl-distro, --opam-root,
 *          --opam-switch, --fstar, --cherry-fstar, --pwsh, --ocaml-checker, --cherry-checker.
 */
import { existsSync, readFileSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, isAbsolute, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnRunner } from "./lib/command.js";
import { evaluateContinuity, launchExclusively, type BuildEvidence } from "./lib/continuity.js";
import { readRunEvidenceInNode, runWorkflowInNode } from "./lib/launch.js";
import { policyHoldsFromRun } from "./lib/provider.js";
import { parseBuildLog } from "./lib/reports.js";
import { downloadRunReports, fromGhRuns, listPulseRuns, localReportKey, reportingRuns, reportKey, type PulseRun } from "./lib/sources.js";
import { holdPolicyBlocked, readState, requeuePolicyBlocked, withStateLock } from "./lib/state.js";
import { probeToolchain } from "./lib/toolchain.js";

interface Options {
  mode: "check" | "launch" | "requeue" | "reconcile";
  /** --requeue-policy-blocked: `all` or the fingerprints. */
  requeue?: "all" | string[];
  /** --reconcile-policy-blocked: the Atomic run id. */
  reconcileRunId?: string;
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

/** Atomic run statuses during which the run may still write state. */
const ACTIVE_RUN = new Set(["running", "paused", "awaiting_input", "pending"]);

/**
 * Hold the findings of an earlier run's policy-blocked stages, from that run's durable evidence
 * (journal and stage sessions, read-only) and its plan and integration records.
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
  if (!evidence.runKey || !evidence.runDir) {
    console.log(JSON.stringify({ ...report, runStatus: evidence.status, applied: false, failed: "the run has no preflight checkpoint (no run key or evidence directory)" }, null, 2));
    return 1;
  }
  const now = new Date();
  const holds = policyHoldsFromRun({ runId, runKey: evidence.runKey, runDir: evidence.runDir, at: now.toISOString(), stages: evidence.stages });
  const stages = evidence.stages.filter((stage) => stage.kind !== "completed");
  const active = ACTIVE_RUN.has(evidence.status);
  Object.assign(report, { runStatus: evidence.status, runKey: evidence.runKey, runDir: evidence.runDir, stages });
  if (options.dryRun || active) {
    const preview = holdPolicyBlocked(readState(options.stateDir), holds, now);
    const reason = active ? `run ${runId} is ${evidence.status}: state.json is not changed until it ends` : "dry run";
    console.log(JSON.stringify({ ...report, applied: false, reason, wouldHold: preview.held, unchanged: preview.unchanged }, null, 2));
    return active && !options.dryRun ? 1 : 0;
  }
  const result = await withStateLock(options.stateDir, (state) => {
    const next = holdPolicyBlocked(state, holds, now);
    return { ...(next.held.length > 0 ? { state: next.state } : {}), result: next };
  }, { owner: `reconcile-${process.pid}` });
  console.log(JSON.stringify({ ...report, applied: result.held.length > 0, held: result.held, unchanged: result.unchanged }, null, 2));
  return 0;
}

async function main(): Promise<number> {
  const repoRoot = resolve(import.meta.dirname ?? dirname(new URL(import.meta.url).pathname), "..", "..");
  const options = parseArgs(process.argv.slice(2), repoRoot);
  if (options.mode === "requeue") return requeue(options);
  if (options.mode === "reconcile") return reconcile(options, repoRoot);
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

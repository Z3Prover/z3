/**
 * Continuity launcher for the `fstar-proof-checking` workflow.
 *
 *   bun fstar/workflow/continuity.ts --check  [--dry-run] [options]
 *   bun fstar/workflow/continuity.ts --launch [--dry-run] [options]
 *
 * --check   evaluates the three retrigger conditions from fstar/workflow-instructions.txt and
 *           prints a JSON decision: a new Pulse report, unprocessed partial proof rules, or an
 *           OCaml/Cherry checker build that timed out on proofs. GitHub access is read-only.
 * --launch  additionally starts one bounded workflow run through Atomic's programmatic
 *           `run(definition, inputs)` API when a condition holds, holding a launcher lock so
 *           scheduled invocations never overlap. A bounded run does not retrigger itself;
 *           schedule this launcher (see README) to get continuity.
 * --dry-run never launches a live run: with --launch it runs the workflow with
 *           `dryRun: true, publish: "dry-run"` and an in-memory journal.
 * --publish none|dry-run|live is passed to the launched run (default: the workflow's `dry-run`).
 *           Verified work from non-live runs stays pending in state; a `--publish live` launch
 *           pushes it together with its own work.
 *
 * Options: --state-dir <dir> (default .atomic/fstar-proof-checking), --repo <owner/name>,
 *          --branch <name> (Pulse runs to consider; default master, "" for all),
 *          --runs-file <json> (offline `{regressions, build}` gh listings instead of gh),
 *          --build-log <path> (repeatable; local OCaml/Cherry build logs), --no-remote.
 * Toolchain discovery overrides (also passed to the launched run): --wsl-distro, --opam-root,
 *          --opam-switch, --fstar, --cherry-fstar, --pwsh, --ocaml-checker, --cherry-checker.
 */
import { existsSync, readFileSync } from "node:fs";
import { dirname, isAbsolute, join, resolve } from "node:path";
import { spawnRunner } from "./lib/command.js";
import { evaluateContinuity, type BuildEvidence } from "./lib/continuity.js";
import { parseBuildLog } from "./lib/reports.js";
import { downloadRunReports, fromGhRuns, listPulseRuns, localReportKey, reportingRuns, reportKey, type PulseRun } from "./lib/sources.js";
import { acquireLock, readState } from "./lib/state.js";
import { probeToolchain } from "./lib/toolchain.js";

interface Options {
  mode: "check" | "launch";
  dryRun: boolean;
  publish?: "none" | "dry-run" | "live";
  stateDir: string;
  repo: string;
  branch: string;
  runsFile?: string;
  buildLogs: string[];
  remote: boolean;
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
    else if (arg === "--publish") {
      const mode = value();
      if (mode !== "none" && mode !== "dry-run" && mode !== "live") throw new Error(`--publish must be none, dry-run or live, not ${mode}`);
      options.publish = mode;
    }
    else if (arg === "--no-remote") options.remote = false;
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

async function main(): Promise<number> {
  const repoRoot = resolve(import.meta.dirname ?? dirname(new URL(import.meta.url).pathname), "..", "..");
  const options = parseArgs(process.argv.slice(2), repoRoot);
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
  let release: () => void;
  try {
    release = await acquireLock(join(options.stateDir, "launcher.lock"), { owner: `launcher-${process.pid}`, timeoutMs: 0, staleMs: 12 * 3_600_000 });
  } catch (error) {
    console.log(JSON.stringify({ ...report, launched: false, skipped: (error as Error).message }, null, 2));
    return 0;
  }
  try {
    const { registerAtomicHostModules } = await import("./lib/atomic-host.js");
    await registerAtomicHostModules();
    const { default: definition } = await import("./fstar-proof-checking.js");
    const sdk = await import("@bastani/atomic/workflows");
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
    const result = await sdk.run(definition, inputs as never, {
      cwd: repoRoot,
      executionMode: "non_interactive",
      ...(options.dryRun ? { journal: { memory: true } } : {}),
    });
    console.log(JSON.stringify({ ...report, launched: true, inputs, runId: result.runId, status: result.status, error: result.error, result: result.result }, null, 2));
    return result.status === "completed" ? 0 : 1;
  } finally {
    release();
  }
}

main().then((code) => process.exit(code), (error) => {
  console.error(error instanceof Error ? error.stack ?? error.message : String(error));
  process.exit(1);
});

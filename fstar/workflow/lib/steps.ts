/**
 * Durable step bodies for the F* proof-checking workflow. The workflow entry file wraps each in
 * `ctx.tool(...)` so completed steps replay on resume; every external command goes through a
 * logging runner whose entries are appended to `<runDir>/commands.jsonl` as evidence.
 */
import { appendFileSync, existsSync, mkdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { basename, dirname, isAbsolute, join, resolve } from "node:path";
import { isRemoteMutation, runChecked, spawnRunner, type CommandLogEntry, type CommandRunner } from "./command.js";
import { collectSliceChanges, decideSliceOutcome, scanDiffForUnsoundness, type VerifierVerdict } from "./gate.js";
import { ensureWorktree, removeCleanWorktree } from "./git.js";
import { planSlices, type SliceFocus } from "./plan.js";
import {
  decideActiveBranch,
  executePublication,
  fileBugReports,
  gatherPublicationFacts,
  planPublication,
  remoteBranchStatus,
  type BugReportResult,
  type PublicationFacts,
  type PublishMode,
} from "./publish.js";
import { describeOutcome, isProviderFailure, type StageOutcome } from "./provider.js";
import { buildLogFindings, mergeFindings, normalizeReportTree, type Finding } from "./reports.js";
import {
  downloadRunReports,
  fromGhRuns,
  listPulseRuns,
  listSmt2,
  listSmt2ByGroup,
  localReportKey,
  reportingRuns,
  reportKey,
  scanBatchCorpus,
  scanInteractiveCorpus,
  selectStratifiedWindow,
  selectWindow,
  stageFiles,
  type GhRun,
  type PulseRun,
} from "./sources.js";
import {
  claimFindings,
  eligibleStateFindings,
  readState,
  reconcilePublications,
  recordOutcomes,
  recordSeen,
  settlePublications,
  triageFindings,
  withStateLock,
  type BranchObservation,
  type ProviderBlock,
  type PublicationLink,
  type SliceOutcome,
  type WorkflowState,
} from "./state.js";
import type { Theory } from "./theories.js";
import { probeToolchain, toEnvironmentPath, type ToolchainReport } from "./toolchain.js";

export interface WorkflowInputs {
  readonly pulseRunIds: readonly string[];
  readonly pulseBranch: string;
  readonly maxReports: number;
  readonly reportPaths: readonly string[];
  readonly localCorpora: readonly string[];
  readonly localCaseLimit: number;
  readonly ocamlChecker: string;
  readonly cherryChecker: string;
  readonly fstarExe: string;
  readonly cherryFstarExe: string;
  readonly wslDistro: string;
  readonly opamRoot: string;
  readonly opamSwitch: string;
  readonly pwshExe: string;
  readonly theories: readonly Theory[];
  readonly maxIterations: number;
  readonly coreBudget: number;
  readonly coresPerSlice: number;
  readonly maxFindingsPerSlice: number;
  readonly publish: PublishMode;
  readonly dryRun: boolean;
  readonly investigate: boolean;
  readonly stateDir: string;
  readonly repo: string;
  readonly remote: string;
  readonly baseRef: string;
  readonly prBase: string;
  readonly branchPrefix: string;
  readonly bugReportRepo: string;
}

export type RunSetup = {
  readonly repoRoot: string;
  readonly stateDir: string;
  readonly runKey: string;
  readonly runDir: string;
  readonly worktreeRoot: string;
  readonly startedAt: string;
  readonly toolchain: ToolchainReport;
};

/** Runner that records every command in `<runDir>/commands.jsonl`. */
export function evidenceRunner(runDir: string, inner: CommandRunner = spawnRunner): CommandRunner {
  return async (argv, options) => {
    const result = await inner(argv, options);
    const entry: CommandLogEntry = { argv: [...argv], cwd: options.cwd, code: result.code, mutating: isRemoteMutation(argv) };
    appendFileSync(join(runDir, "commands.jsonl"), `${JSON.stringify(entry)}\n`);
    return result;
  };
}

function writeJson(path: string, value: unknown): string {
  writeFileSync(path, `${JSON.stringify(value, null, 2)}\n`, "utf8");
  return path;
}

function readJson<T>(path: string): T {
  return JSON.parse(readFileSync(path, "utf8")) as T;
}

function iterationDir(setup: RunSetup, iteration: number): string {
  const directory = join(setup.runDir, `iter-${iteration}`);
  mkdirSync(directory, { recursive: true });
  return directory;
}

// ---------------------------------------------------------------- preflight

export async function preflight(inputs: WorkflowInputs, cwd: string, signal: AbortSignal, runner: CommandRunner = spawnRunner): Promise<RunSetup> {
  const repoRoot = (await runChecked(runner, ["git", "rev-parse", "--show-toplevel"], { cwd, timeoutMs: 30_000, signal })).replaceAll("/", "\\").replace(/^\\/, "/");
  const root = process.platform === "win32" ? repoRoot : repoRoot.replaceAll("\\", "/");
  const stateDir = isAbsolute(inputs.stateDir) ? inputs.stateDir : resolve(root, inputs.stateDir);
  const stamp = new Date().toISOString().replace(/[-:]/g, "").replace(/\.\d+Z$/, "Z");
  const runKey = `${stamp}-${Math.random().toString(16).slice(2, 6)}${inputs.dryRun ? "-dry" : ""}`;
  const runDir = join(stateDir, "runs", runKey);
  mkdirSync(runDir, { recursive: true });
  const toolchain = await probeToolchain(evidenceRunner(runDir, runner), {
    wslDistro: inputs.wslDistro || undefined,
    fstarExe: inputs.fstarExe || undefined,
    cherryFstarExe: inputs.cherryFstarExe || undefined,
    opamRoot: inputs.opamRoot || undefined,
    opamSwitch: inputs.opamSwitch || undefined,
    pwshExe: inputs.pwshExe || undefined,
    ocamlChecker: inputs.ocamlChecker || undefined,
    cherryChecker: inputs.cherryChecker || undefined,
    signal,
  });
  const setup: RunSetup = { repoRoot: root, stateDir, runKey, runDir, worktreeRoot: join(stateDir, "worktrees"), startedAt: new Date().toISOString(), toolchain };
  writeJson(join(runDir, "setup.json"), { setup, inputs });
  return setup;
}
// ---------------------------------------------------------------- publication reconciliation

export type ReconcileSummary = {
  readonly committed: boolean;
  /** Branches whose remote status was queried (read-only). */
  readonly checked: string[];
  readonly merged: string[];
  readonly reopened: string[];
  readonly kept: string[];
};

/**
 * Before sourcing: query (read-only) the branches that carry resolved findings and apply the
 * lifecycle — merged PRs make their findings `merged`; a branch deleted before its PR merged
 * reopens its findings, keeping the lost branch, PR and head on record — and reopen integrated
 * findings that no pending publication carries. `publish=none` never queries the remote; a dry
 * run changes nothing. State is written only when something changed, so re-running is a no-op.
 */
export async function reconcilePublicationsStep(setup: RunSetup, inputs: WorkflowInputs, signal: AbortSignal, inner?: CommandRunner): Promise<ReconcileSummary> {
  if (inputs.dryRun) return { committed: false, checked: [], merged: [], reopened: [], kept: [] };
  const runner = evidenceRunner(setup.runDir, inner);
  const branches = inputs.publish === "none" ? [] : [...new Set(Object.values(readState(setup.stateDir).findings)
    .flatMap((record) => (record.status === "resolved" && record.publishedOn ? [record.publishedOn.branch] : [])))].sort();
  const observed: Record<string, BranchObservation> = {};
  for (const branch of branches) {
    observed[branch] = await remoteBranchStatus(runner, branch, { repo: inputs.repo, remote: inputs.remote, prefix: inputs.branchPrefix, cwd: setup.repoRoot, timeoutMs: 60_000, signal });
  }
  const summary = await withStateLock(setup.stateDir, (state) => {
    const result = reconcilePublications(state, observed, new Date());
    const changed = JSON.stringify(result.state) !== JSON.stringify(state);
    return { ...(changed ? { state: result.state } : {}), result: { committed: changed, checked: branches, merged: result.merged, reopened: result.reopened, kept: result.kept } };
  }, { owner: setup.runKey });
  writeJson(join(setup.runDir, "reconcile.json"), { ...summary, observed });
  return summary;
}

// ---------------------------------------------------------------- sourcing

export type SourceSummary = {
  readonly findingsPath: string;
  readonly total: number;
  readonly byKind: Record<string, number>;
  readonly byTheory: Record<string, number>;
  /** `producedAt`: when the report was produced (Pulse run creation time, local file modification time). */
  readonly reports: Array<{ key: string; directory: string; artifacts: string[]; missing: string[]; producedAt?: string }>;
  /**
   * Next scan position per corpus and checker; batch corpora also rotate within each logic directory (`groupOffsets`).
   * `checkerBuiltAt`: build time of the prebuilt checker binary that ran the scan (unknown: absent).
   */
  readonly localScans: Record<string, { offset: number; cases: number; mode: string; groupOffsets?: Record<string, number>; checkerBuiltAt?: string }>;
  /** Fingerprints re-sourced from state (eligible earlier findings no current source reported). */
  readonly carried: string[];
  readonly diagnostics: string[];
};

const REGRESSIONS_NAME = "Pulse verification and native checker regressions";
const BUILD_NAME = "Build Pulse native checkers";

async function explicitRuns(runner: CommandRunner, inputs: WorkflowInputs, signal: AbortSignal): Promise<PulseRun[]> {
  const runs: PulseRun[] = [];
  for (const id of inputs.pulseRunIds) {
    const output = await runChecked(runner, [
      "gh", "run", "view", id, "--repo", inputs.repo, "--json", "databaseId,attempt,status,conclusion,createdAt,headBranch,workflowName",
    ], { timeoutMs: 60_000, signal });
    const row = JSON.parse(output) as GhRun & { workflowName: string };
    if (row.workflowName !== REGRESSIONS_NAME && row.workflowName !== BUILD_NAME) {
      throw new Error(`Run ${id} belongs to "${row.workflowName}", not a Pulse checker workflow`);
    }
    runs.push(...fromGhRuns([row], row.workflowName === BUILD_NAME ? "build" : "regressions"));
  }
  return runs;
}

/**
 * Collect findings from Pulse workflow reports (GitHub, read-only), local report directories and
 * build logs, local corpora, and eligible findings already recorded in state (deferred by slice
 * capacity, retries out of backoff, abandoned claims). In a dry run nothing remote is contacted
 * and no checker is executed.
 */
export async function sourceFindings(setup: RunSetup, inputs: WorkflowInputs, signal: AbortSignal, inner?: CommandRunner): Promise<SourceSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const diagnostics: string[] = [];
  const findings: Finding[] = [];
  const reports: SourceSummary["reports"] = [];
  const state = readState(setup.stateDir);
  if (inputs.dryRun) {
    diagnostics.push("Dry run: GitHub Pulse reports were not listed or downloaded.");
  } else {
    const runs = inputs.pulseRunIds.length > 0
      ? await explicitRuns(runner, inputs, signal)
      : reportingRuns(await listPulseRuns(runner, { repo: inputs.repo, limit: 20, branch: inputs.pulseBranch || undefined, signal }))
        .filter((run) => !(reportKey(run) in state.processedReports))
        .slice(0, inputs.maxReports);
    if (runs.length === 0) diagnostics.push("No unprocessed Pulse reports were found.");
    for (const run of runs) {
      const downloaded = await downloadRunReports(runner, run, { repo: inputs.repo, cacheDir: join(setup.stateDir, "reports"), signal });
      reports.push({ key: downloaded.key, directory: downloaded.directory, artifacts: downloaded.artifacts, missing: downloaded.missing, producedAt: run.createdAt });
      if (downloaded.missing.length > 0) diagnostics.push(`${downloaded.key}: missing or expired artifacts ${downloaded.missing.join(", ")}`);
      const normalized = normalizeReportTree(downloaded.directory, { source: downloaded.key });
      findings.push(...normalized.findings);
      diagnostics.push(...normalized.diagnostics);
      if (run.workflow === "build" && run.conclusion === "timed_out") {
        diagnostics.push(`${downloaded.key}: the CI build job timed out; see its build.log for the last module verified.`);
      }
    }
  }
  for (const path of inputs.reportPaths) {
    const absolute = resolve(setup.repoRoot, path);
    if (!existsSync(absolute)) {
      diagnostics.push(`Report path ${absolute} does not exist.`);
      continue;
    }
    const key = localReportKey(absolute);
    const stats = statSync(absolute);
    const producedAt = stats.mtime.toISOString();
    if (stats.isDirectory()) {
      reports.push({ key, directory: absolute, artifacts: [basename(absolute)], missing: [], producedAt });
      const normalized = normalizeReportTree(absolute, { source: key });
      findings.push(...normalized.findings);
      diagnostics.push(...normalized.diagnostics);
    } else {
      // A single OCaml/Cherry/F* build log (for example from the continuity launcher's --build-log).
      reports.push({ key, directory: dirname(absolute), artifacts: [basename(absolute)], missing: [], producedAt });
      findings.push(...buildLogFindings(absolute, { source: key }));
    }
  }
  const local = await scanLocalCorpora(runner, setup, inputs, state, signal);
  findings.push(...local.findings);
  diagnostics.push(...local.diagnostics);
  const fresh = mergeFindings(findings);
  const seen = new Set(fresh.map((finding) => finding.fingerprint));
  const carried = eligibleStateFindings(state, new Date()).filter((finding) => !seen.has(finding.fingerprint));
  if (carried.length > 0) diagnostics.push(`${carried.length} eligible finding(s) recorded in state were re-sourced.`);
  const merged = [...fresh, ...carried];
  const count = (key: (finding: Finding) => string) => merged.reduce<Record<string, number>>((counts, finding) => {
    counts[key(finding)] = (counts[key(finding)] ?? 0) + 1;
    return counts;
  }, {});
  const findingsPath = writeJson(join(setup.runDir, "findings.json"), merged);
  return {
    findingsPath, total: merged.length, byKind: count((f) => f.kind), byTheory: count((f) => f.theory), reports, localScans: local.scans,
    carried: carried.map((finding) => finding.fingerprint), diagnostics,
  };
}

/**
 * Run the discovered checkers on the local corpora inside the build environment: z3test
 * `regressions/smt2` scripts in `--interactive` mode over a rotating window, other corpora
 * through the batch harness over a window stratified by top-level (logic) directory, staged as
 * copies below the run directory.
 */
export async function scanLocalCorpora(
  runner: CommandRunner,
  setup: RunSetup,
  inputs: WorkflowInputs,
  state: WorkflowState,
  signal: AbortSignal,
): Promise<{ findings: Finding[]; diagnostics: string[]; scans: SourceSummary["localScans"] }> {
  const findings: Finding[] = [];
  const diagnostics: string[] = [];
  const scans: SourceSummary["localScans"] = {};
  const toolchain = setup.toolchain;
  const toEnvironment = (path: string) => toEnvironmentPath(toolchain.environment, path);
  for (const corpus of inputs.localCorpora) {
    if (!existsSync(corpus)) {
      diagnostics.push(`Local corpus ${corpus} does not exist; skipped.`);
      continue;
    }
    const checkers = [["ocaml", toolchain.ocamlChecker], ["cherry", toolchain.cherryChecker]] as const;
    const available = checkers.filter(([, path]) => path !== undefined);
    if (!toolchain.environment || available.length === 0) {
      diagnostics.push(`Local corpus ${corpus} skipped: no checker executable was found (set ocamlChecker/cherryChecker or Z3_FSTAR_CHECKER/Z3_FSTAR_CHERRY_CHECKER).`);
      continue;
    }
    if (inputs.dryRun) {
      diagnostics.push(`Dry run: local corpus ${corpus} was not executed.`);
      continue;
    }
    // z3test regression inputs are incremental scripts: use interactive mode. Other corpora use the batch harness.
    const interactive = /regressions[\\/]+smt2$/i.test(corpus.replace(/[\\/]+$/, ""));
    const files = interactive ? listSmt2(corpus) : [];
    const groups = interactive ? [] : listSmt2ByGroup(corpus);
    for (const [kind, checker] of available) {
      const outputDir = join(setup.runDir, "local", `${kind}-${basename(corpus)}`);
      const key = `local-scan:${kind}:${corpus}`;
      // A scan's evidence dates from its checker binary's build, which can predate merged fixes.
      const builtAt = kind === "ocaml" ? toolchain.ocamlCheckerBuiltAt : toolchain.cherryCheckerBuiltAt;
      const dated = builtAt ? { checkerBuiltAt: builtAt } : {};
      if (interactive) {
        const window = selectWindow(files, state.localScans[key]?.offset ?? 0, inputs.localCaseLimit);
        const scan = await scanInteractiveCorpus(runner, {
          checkerArgv: [...toolchain.environment.execArgv, checker as string], corpus, files: window.selected, outputDir,
          caseTimeoutMs: 60_000, solverTimeoutMs: 10_000, concurrency: Math.max(1, Math.min(inputs.coreBudget, 32)), signal,
        });
        scans[key] = { offset: window.nextOffset, cases: scan.cases, mode: "interactive", ...dated };
      } else if (toolchain.python) {
        const window = selectStratifiedWindow(groups, state.localScans[key], inputs.localCaseLimit);
        if (window.selected.length === 0) {
          diagnostics.push(`Local corpus ${corpus} has no .smt2 inputs to check (or localCaseLimit is 0); skipped for ${kind}.`);
          continue;
        }
        // The harness checks every input below the staged copy of this window.
        const staged = stageFiles(corpus, window.selected, join(`${outputDir}-inputs`, basename(corpus)));
        await scanBatchCorpus(runner, {
          pythonArgv: [...toolchain.environment.execArgv, toolchain.python], toEnvironment, repoRoot: setup.repoRoot, checker: checker as string, corpus: staged,
          maxCases: window.selected.length, outputDir, totalTimeoutSeconds: 1800, signal,
        });
        scans[key] = { offset: window.nextOffset, groupOffsets: window.groupOffsets, cases: window.selected.length, mode: "batch", ...dated };
      } else {
        diagnostics.push(`Local corpus ${corpus} skipped for ${kind}: Python 3 is required for the batch harness.`);
        continue;
      }
      const normalized = normalizeReportTree(outputDir, { source: key });
      findings.push(...normalized.findings);
      diagnostics.push(...normalized.diagnostics);
    }
  }
  return { findings, diagnostics, scans };
}

export type RecordedSources = { readonly committed: boolean; readonly processedReports: string[]; readonly seen: number };

/**
 * Record what this run ingested before any iteration can stop early: every sourced report is
 * processed, local scan windows advance, and new findings enter state as `open` so later runs
 * re-source them. A finding's evidence time is its newest report's production time (for a local
 * scan, the build time of the checker binary that ran it), which decides whether evidence follows
 * a merge. Dry runs record nothing.
 */
export async function recordSourcesStep(setup: RunSetup, inputs: WorkflowInputs, source: SourceSummary): Promise<RecordedSources> {
  const processedReports = source.reports.map((report) => report.key);
  const carried = new Set(source.carried);
  const fresh = readJson<Finding[]>(source.findingsPath).filter((finding) => !carried.has(finding.fingerprint));
  if (inputs.dryRun) return { committed: false, processedReports, seen: fresh.length };
  await withStateLock(setup.stateDir, (state) => {
    const now = new Date();
    const producedTimes = new Map<string, string>(source.reports.flatMap((report) => (report.producedAt ? [[report.key, report.producedAt] as const] : [])));
    // Local scans run a prebuilt checker: their evidence is as recent as that binary, not the scan.
    const undatedScans = new Set<string>();
    for (const [key, scan] of Object.entries(source.localScans)) {
      if (scan.checkerBuiltAt) producedTimes.set(key, scan.checkerBuiltAt);
      else undatedScans.add(key);
    }
    // The newest known time; `null` when the only evidence is a scan by a checker of unknown build time.
    const producedAt = (finding: Finding) => {
      const newest = finding.sources.map((key) => producedTimes.get(key)).filter((time): time is string => time !== undefined).sort().pop();
      return newest ?? (finding.sources.length > 0 && finding.sources.every((key) => undatedScans.has(key)) ? null : undefined);
    };
    const reportsSeen = { ...state.processedReports };
    for (const key of processedReports) reportsSeen[key] = { processedAt: now.toISOString(), findings: source.total };
    const localScans = { ...state.localScans };
    for (const [key, scan] of Object.entries(source.localScans)) {
      localScans[key] = { at: now.toISOString(), offset: scan.offset, ...(scan.groupOffsets ? { groupOffsets: scan.groupOffsets } : {}) };
    }
    return { state: { ...recordSeen(state, fresh, now, producedAt), processedReports: reportsSeen, localScans }, result: undefined };
  }, { owner: setup.runKey });
  writeJson(join(setup.runDir, "sources-recorded.json"), { processedReports, seen: fresh.length, localScans: source.localScans });
  return { committed: true, processedReports, seen: fresh.length };
}

// ---------------------------------------------------------------- triage and planning

export type TriageSummary = {
  readonly actionablePath: string;
  readonly actionable: number;
  readonly skipped: Record<string, number>;
  /** Verified integrations from earlier runs that still await a live push. */
  readonly pendingPublications: number;
};

export function triageStep(setup: RunSetup, inputs: WorkflowInputs, findingsPath: string, iteration: number, exclude: readonly string[]): TriageSummary {
  const findings = readJson<Finding[]>(findingsPath);
  const state = readState(setup.stateDir);
  const result = triageFindings(findings, state, { now: new Date(), theories: inputs.theories, exclude: new Set(exclude) });
  const actionablePath = writeJson(join(iterationDir(setup, iteration), "actionable.json"), result.actionable);
  return { actionablePath, actionable: result.actionable.length, skipped: result.skipped, pendingPublications: state.pendingPublications.length };
}

export type SliceSummary = {
  readonly id: string;
  readonly theory: Theory;
  readonly focus: SliceFocus;
  readonly cores: number;
  readonly branch: string;
  readonly worktree: string;
  readonly sliceDir: string;
  readonly findingsPath: string;
  readonly reportPath: string;
  readonly verifyPath: string;
  readonly fingerprints: string[];
};

export type PlanSummary = {
  readonly slices: SliceSummary[];
  readonly concurrency: number;
  readonly totalCores: number;
  readonly coreBudget: number;
  readonly deferred: number;
  readonly worktreesCreated: boolean;
};

/** Plan slices; outside dry runs also create each slice worktree and claim its findings in state. */
export async function planStep(setup: RunSetup, inputs: WorkflowInputs, actionablePath: string, iteration: number, signal: AbortSignal, inner?: CommandRunner): Promise<PlanSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const actionable = readJson<Finding[]>(actionablePath);
  const plan = planSlices(actionable, {
    coreBudget: inputs.coreBudget, coresPerSlice: inputs.coresPerSlice, maxFindingsPerSlice: inputs.maxFindingsPerSlice,
    runKey: setup.runKey, iteration, worktreeRoot: setup.worktreeRoot, branchPrefix: inputs.branchPrefix,
  });
  const slices = plan.slices.map((slice): SliceSummary => {
    const sliceDir = join(iterationDir(setup, iteration), slice.id);
    mkdirSync(sliceDir, { recursive: true });
    return {
      id: slice.id, theory: slice.theory, focus: slice.focus, cores: slice.cores, branch: slice.branch, worktree: slice.worktree, sliceDir,
      findingsPath: writeJson(join(sliceDir, "findings.json"), slice.findings),
      reportPath: join(sliceDir, "slice-report.md"),
      verifyPath: join(sliceDir, "verification.md"),
      fingerprints: slice.findings.map((finding) => finding.fingerprint),
    };
  });
  if (!inputs.dryRun && slices.length > 0) {
    mkdirSync(setup.worktreeRoot, { recursive: true });
    for (const slice of slices) {
      await ensureWorktree(runner, setup.repoRoot, { path: slice.worktree, branch: slice.branch, base: inputs.baseRef, signal });
    }
    await withStateLock(setup.stateDir, (state) => ({
      state: claimFindings(state, plan.slices.flatMap((slice) => slice.findings), { runKey: setup.runKey, now: new Date() }),
      result: undefined,
    }), { owner: setup.runKey });
  }
  const summary: PlanSummary = {
    slices, concurrency: plan.concurrency, totalCores: plan.totalCores, coreBudget: plan.coreBudget,
    deferred: plan.deferred.length, worktreesCreated: !inputs.dryRun && slices.length > 0,
  };
  writeJson(join(iterationDir(setup, iteration), "plan.json"), summary);
  return summary;
}

// ---------------------------------------------------------------- gate

export type GateSummary = {
  readonly slices: Array<{ id: string; status: SliceOutcome | "not-run"; reasons: string[]; head?: string; changedFiles: number; warnings: string[]; provider?: StageOutcome }>;
  readonly verified: number;
};

/**
 * Gate each slice. A slice whose repair or verify stage ended on a provider error (`providers`)
 * is not gated: it is `provider-policy-blocked` or `provider-unavailable`, never verified.
 */
export async function gateStep(
  setup: RunSetup,
  inputs: WorkflowInputs,
  plan: PlanSummary,
  verdicts: ReadonlyArray<VerifierVerdict | null>,
  iteration: number,
  signal: AbortSignal,
  inner?: CommandRunner,
  providers: ReadonlyArray<StageOutcome | null> = [],
): Promise<GateSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const slices: GateSummary["slices"] = [];
  for (const [index, slice] of plan.slices.entries()) {
    if (inputs.dryRun) {
      slices.push({ id: slice.id, status: "not-run", reasons: ["dry run: no agent stages were executed"], changedFiles: 0, warnings: [] });
      continue;
    }
    const provider = providers[index];
    if (isProviderFailure(provider)) {
      slices.push({ id: slice.id, status: provider.kind, reasons: [describeOutcome(provider)], changedFiles: 0, warnings: [], provider });
      continue;
    }
    const changes = await collectSliceChanges(runner, slice.worktree, inputs.baseRef, signal);
    const scan = scanDiffForUnsoundness(changes.diff);
    const outcome = decideSliceOutcome({
      scan, changedFiles: changes.changedFiles, uncommitted: changes.uncommitted, verifier: verdicts[index] ?? undefined, toolchainAvailable: setup.toolchain.available,
    });
    slices.push({
      id: slice.id, status: outcome.status, reasons: outcome.reasons, head: changes.head, changedFiles: changes.changedFiles,
      warnings: scan.warnings.map((item) => `${item.file}: ${item.pattern} (${item.line})`),
    });
  }
  const summary = { slices, verified: slices.filter((slice) => slice.status === "verified").length };
  writeJson(join(iterationDir(setup, iteration), "gate.json"), summary);
  return summary;
}

/** Record how a group of agent stages ended (`<runDir>/<group>.json`, for example `iter-1/repair-outcomes.json`). */
export function recordStageOutcomes(setup: RunSetup, group: string, outcomes: StageOutcome[]): StageOutcome[] {
  const path = join(setup.runDir, `${group}.json`);
  mkdirSync(dirname(path), { recursive: true });
  writeJson(path, outcomes);
  return outcomes;
}

// ---------------------------------------------------------------- integration

/** A slice whose change an integration head contains, and the earlier run whose pending integration brought it (if any). */
export type IntegratedSlice = { readonly slice: string; readonly fingerprints: string[]; readonly from?: string };

export type IntegrationSummary = {
  readonly worktree?: string;
  readonly branch?: string;
  readonly base: string;
  readonly merged: string[];
  readonly conflicts: string[];
  readonly rejected: string[];
  /** Run keys of still unpublished verified integrations merged in (earlier runs in live mode, and this run's earlier iterations). */
  readonly pendingMerged: string[];
  /** Pending integrations that could not be merged; they stay pending with this reason. */
  readonly pendingFailed: Array<{ runKey: string; reason: string }>;
  /** Exactly the verified slices whose changes `head` contains on top of `base`. */
  readonly contents: IntegratedSlice[];
  readonly head?: string;
  readonly note: string;
};

async function publicationFacts(runner: CommandRunner, setup: RunSetup, inputs: WorkflowInputs, state: WorkflowState, signal: AbortSignal): Promise<PublicationFacts> {
  if (inputs.dryRun || inputs.publish === "none") {
    return { known: false, branchExists: false, prs: [], freeBranch: `${inputs.branchPrefix}/${state.publication.sequence + 1}` };
  }
  return gatherPublicationFacts(runner, state.publication, { repo: inputs.repo, remote: inputs.remote, prefix: inputs.branchPrefix, cwd: setup.repoRoot, timeoutMs: 60_000, signal });
}

/** Merge one verified ref into the integration worktree; a merge that conflicts or fails the soundness scan is undone. */
async function mergeVerified(runner: CommandRunner, inTree: { cwd: string; timeoutMs: number; signal: AbortSignal }, ref: string, message: string): Promise<"merged" | "conflict" | "unsound"> {
  const before = await runChecked(runner, ["git", "rev-parse", "HEAD"], inTree);
  const merge = await runner(["git", "merge", "--no-ff", "--no-edit", "-m", message, ref], inTree);
  if (merge.code !== 0) {
    await runner(["git", "merge", "--abort"], inTree);
    return "conflict";
  }
  // Re-scan the merged result: a merge must not introduce what the slice gate would reject.
  const scan = scanDiffForUnsoundness(await runChecked(runner, ["git", "diff", "--no-color", `${before}..HEAD`], inTree));
  if (scan.violations.length > 0) {
    await runChecked(runner, ["git", "reset", "--hard", before], inTree);
    return "unsound";
  }
  return "merged";
}

/**
 * Merge verified slice branches into a fresh integration worktree for this iteration, based on
 * the active publication branch when it is still open. Earlier verified integrations that were
 * never pushed are merged first (oldest first): in live runs all of them, so they are published
 * with it, otherwise only this run's own earlier iterations, so this run's pending head keeps
 * accumulating verified work. Merges whose verification failed in an earlier iteration live only
 * on that iteration's branch and never reach a later head.
 */
export async function integrateStep(setup: RunSetup, inputs: WorkflowInputs, plan: PlanSummary, gate: GateSummary, iteration: number, signal: AbortSignal, inner?: CommandRunner): Promise<IntegrationSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const verified = plan.slices.filter((slice) => gate.slices.find((item) => item.id === slice.id)?.status === "verified");
  const state = readState(setup.stateDir);
  const live = !inputs.dryRun && inputs.publish === "live";
  const pending = state.pendingPublications.filter((entry) => live || entry.runKey === setup.runKey);
  const empty = { merged: [], conflicts: [], rejected: [], pendingMerged: [], pendingFailed: [], contents: [] };
  if (inputs.dryRun || (verified.length === 0 && !pending.some((entry) => entry.runKey !== setup.runKey))) {
    const summary: IntegrationSummary = { base: inputs.baseRef, ...empty, note: inputs.dryRun ? "dry run: nothing to integrate" : "no verified slices to integrate" };
    writeJson(join(iterationDir(setup, iteration), "integration.json"), summary);
    return summary;
  }
  const facts = await publicationFacts(runner, setup, inputs, state, signal);
  const active = state.publication.activeBranch;
  // The publish plan's rule (decideActiveBranch): build on the active branch unless the plan starts a new one.
  const continueActive = active !== undefined && facts.known && facts.branchExists && decideActiveBranch(active, facts).kind !== "new-branch";
  const options = { cwd: setup.repoRoot, timeoutMs: 10 * 60_000, signal };
  let base = inputs.baseRef;
  if (continueActive) {
    await runChecked(runner, ["git", "fetch", inputs.remote, `refs/heads/${active}:refs/remotes/${inputs.remote}/${active}`], options);
    base = `${inputs.remote}/${active}`;
  }
  const worktree = join(setup.worktreeRoot, `${setup.runKey}-integration-i${iteration}`);
  const branch = `${inputs.branchPrefix}/integration/${setup.runKey}-i${iteration}`;
  await ensureWorktree(runner, setup.repoRoot, { path: worktree, branch, base, signal });
  const inTree = { cwd: worktree, timeoutMs: 10 * 60_000, signal };
  const pendingMerged: string[] = [];
  const pendingFailed: IntegrationSummary["pendingFailed"] = [];
  const contents: IntegratedSlice[] = [];
  for (const entry of pending) {
    if ((await runner(["git", "show-ref", "--verify", "--quiet", `refs/heads/${entry.branch}`], inTree)).code !== 0) {
      pendingFailed.push({ runKey: entry.runKey, reason: `local integration branch ${entry.branch} is missing; recreate it at ${entry.head} or remove this pending entry from state.json` });
      continue;
    }
    // Merge the verified head that was recorded, not whatever the branch points to now.
    const outcome = await mergeVerified(runner, inTree, entry.head, `Publish verified integration ${entry.runKey}`);
    if (outcome === "merged") {
      pendingMerged.push(entry.runKey);
      contents.push(...pendingContents(entry));
    } else {
      pendingFailed.push({ runKey: entry.runKey, reason: outcome === "conflict" ? `merging ${entry.head} onto ${base} conflicts` : `merging ${entry.head} onto ${base} failed the soundness scan` });
    }
  }
  // This run's earlier verified head is on this run's base, so it always merges; if it did not, its entry would be superseded wrongly.
  const own = pendingFailed.find((item) => item.runKey === setup.runKey);
  if (own) throw new Error(`cannot carry this run's verified integration forward: ${own.reason}`);
  const merged: string[] = [];
  const conflicts: string[] = [];
  const rejected: string[] = [];
  for (const slice of verified) {
    const outcome = await mergeVerified(runner, inTree, slice.branch, `Integrate verified slice ${slice.id}`);
    if (outcome === "merged") {
      merged.push(slice.id);
      contents.push({ slice: slice.id, fingerprints: slice.fingerprints });
    } else {
      (outcome === "conflict" ? conflicts : rejected).push(slice.id);
    }
  }
  const head = await runChecked(runner, ["git", "rev-parse", "HEAD"], inTree);
  const summary: IntegrationSummary = {
    worktree, branch, base, merged, conflicts, rejected, pendingMerged, pendingFailed, contents, head,
    note: `merged ${merged.length} verified slice(s) and ${pendingMerged.length} pending integration(s) onto ${base}`,
  };
  writeJson(join(iterationDir(setup, iteration), "integration.json"), summary);
  return summary;
}

/** What a pending integration contains: its recorded slices and their findings. */
function pendingContents(entry: WorkflowState["pendingPublications"][number]): IntegratedSlice[] {
  return [{ slice: entry.slices.join(", "), fingerprints: entry.fingerprints, from: entry.runKey }];
}

// ---------------------------------------------------------------- publication

export type PublicationSummary = {
  readonly mode: PublishMode;
  readonly action: string;
  readonly branch?: string;
  readonly executed: boolean;
  readonly summary: string;
  readonly prUrl?: string;
  readonly blocked?: string;
  readonly integrationVerified: boolean;
  /** Why the integrated head was not accepted for publication (empty when it was). */
  readonly integrationReasons: string[];
  /** The integration verifier ended on a provider error instead of returning a verdict. */
  readonly integrationProvider?: StageOutcome;
  readonly bugReports: Array<BugReportResult & { draft: string }>;
  readonly publication: WorkflowState["publication"];
};

function bugReportDrafts(plan: PlanSummary): Array<{ fingerprint: string; title: string; bodyFile: string }> {
  return plan.slices.flatMap((slice) => {
    const path = join(slice.sliceDir, "bug-report.md");
    if (slice.focus !== "crash" || !existsSync(path) || !slice.fingerprints[0]) return [];
    const title = /^#\s+(.+)$/m.exec(readFileSync(path, "utf8"))?.[1]?.trim() ?? `Checker crash (${slice.id})`;
    return [{ fingerprint: slice.fingerprints[0], title, bodyFile: path }];
  });
}

function prBody(setup: RunSetup, plan: PlanSummary, gate: GateSummary, integration: IntegrationSummary, verdict: VerifierVerdict | null): string {
  const slices = new Map(plan.slices.map((slice) => [slice.id, slice]));
  return [
    "## Verified F* proof-checker improvements",
    "",
    "Produced by the `fstar-proof-checking` Atomic workflow (fstar/workflow). Each slice was implemented in its own worktree, independently re-verified, scanned for admits/assumptions/raised global rlimits, merged, and the merged result was verified again.",
    "",
    "| Slice | Theory | Focus | Findings | Integrated by run |",
    "|---|---|---|---|---|",
    ...integration.contents.map((item) => {
      const slice = item.from === undefined ? slices.get(item.slice) : undefined;
      return `| ${item.slice} | ${slice?.theory ?? "-"} | ${slice?.focus ?? "-"} | ${item.fingerprints.join(", ")} | ${item.from ?? setup.runKey} |`;
    }),
    "",
    "## Verification",
    "",
    `- Integrated head: \`${integration.head ?? "unknown"}\` on base \`${integration.base}\`.`,
    `- Integration verdict: ${verdict?.verdict ?? "missing"} — ${verdict?.summary ?? ""}`,
    ...(verdict?.commands ?? []).filter((command) => command.phase === "final").map((command) => `- \`${command.command}\` → exit ${command.exitCode}`),
    ...gate.slices.filter((slice) => integration.merged.includes(slice.id)).flatMap((slice) => slice.warnings.map((warning) => `- Warning (${slice.id}): ${warning}`)),
    "",
    `Run: \`${setup.runKey}\`; evidence directory (local): \`${setup.runDir}\`.`,
    "",
    `<!-- fstar-proof-checking:run:${setup.runKey} -->`,
  ].join("\n");
}

/** Gate publication on the integrated verdict, then plan (and in live mode carry out) the branch/PR lifecycle. */
export async function publishStep(
  setup: RunSetup,
  inputs: WorkflowInputs,
  plan: PlanSummary,
  gate: GateSummary,
  integration: IntegrationSummary,
  verdict: VerifierVerdict | null,
  iteration: number,
  signal: AbortSignal,
  inner?: CommandRunner,
  integrationProvider?: StageOutcome | null,
): Promise<PublicationSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const state = readState(setup.stateDir);
  const integrated = integration.merged.length + integration.pendingMerged.length;
  const decision = integrated > 0
    ? decideSliceOutcome({ scan: { violations: [], warnings: [] }, changedFiles: integrated, uncommitted: false, verifier: verdict ?? undefined, toolchainAvailable: setup.toolchain.available })
    : { status: "no-change" as const, reasons: ["nothing was integrated"] };
  const integrationVerified = decision.status === "verified";
  const facts = await publicationFacts(runner, setup, inputs, state, signal);
  const publicationPlan = planPublication(state.publication, facts, { prefix: inputs.branchPrefix, hasChanges: integrationVerified });
  const bodyFile = join(iterationDir(setup, iteration), "pr-body.md");
  writeFileSync(bodyFile, prBody(setup, plan, gate, integration, verdict), "utf8");
  const result = integrationVerified && integration.worktree
    ? await executePublication(runner, publicationPlan, {
      mode: inputs.publish, repo: inputs.repo, remote: inputs.remote, prefix: inputs.branchPrefix, base: inputs.prBase,
      cwd: integration.worktree, title: "F* proof checker: verified improvements (fstar-proof-checking)", bodyFile, timeoutMs: 5 * 60_000, signal,
    })
    : { executed: false, state: state.publication, summary: `${publicationPlan.action.kind}: ${publicationPlan.action.reason}` };
  const drafts = bugReportDrafts(plan);
  const filed: BugReportResult[] = drafts.length === 0 || inputs.dryRun || inputs.publish === "none"
    ? drafts.map((draft) => ({ fingerprint: draft.fingerprint, action: "would-create" as const }))
    : await fileBugReports(runner, drafts, { repo: inputs.bugReportRepo, mode: inputs.publish, timeoutMs: 60_000, signal });
  const bugReports = filed.map((report, index) => ({ ...report, draft: drafts[index]?.bodyFile ?? "" }));
  const action = publicationPlan.action;
  const summary: PublicationSummary = {
    mode: inputs.publish,
    action: action.kind,
    branch: "branch" in action ? action.branch : undefined,
    executed: result.executed,
    summary: result.summary,
    prUrl: "prUrl" in result ? result.prUrl : undefined,
    // A plan that blocks (PR closed without merging) or a push the remote refused as non-fast-forward.
    blocked: action.kind === "blocked" ? action.reason : "blocked" in result ? result.blocked : undefined,
    integrationVerified,
    integrationReasons: integrationVerified ? [] : [...(isProviderFailure(integrationProvider) ? [describeOutcome(integrationProvider)] : []), ...decision.reasons],
    ...(isProviderFailure(integrationProvider) ? { integrationProvider } : {}),
    bugReports,
    publication: result.state,
  };
  writeJson(join(iterationDir(setup, iteration), "publication.json"), { ...summary, plan: publicationPlan });
  return summary;
}

// ---------------------------------------------------------------- persistence

export type PersistSummary = {
  readonly committed: boolean;
  readonly outcomes: Array<{ fingerprint: string; status: SliceOutcome; note: string; provider?: ProviderBlock }>;
  /** Whether verified work was pushed live; otherwise it is recorded as integrated and pending. */
  readonly published: boolean;
};

/** What a held finding records about the stage the provider rejected. */
function providerBlockOf(outcome: StageOutcome, runKey: string): ProviderBlock {
  return {
    runKey, stage: outcome.stage, ...(outcome.sessionId ? { sessionId: outcome.sessionId } : {}), ...(outcome.code ? { code: outcome.code } : {}),
    error: outcome.error ?? "provider policy rejection", at: outcome.at,
  };
}

/**
 * Record outcomes, publication state and pending publications (not in dry runs); what the run
 * ingested was already recorded by `recordSourcesStep`. Verified findings resolve only when a
 * live push included them; otherwise they become `integrated` and the integration branch is kept
 * as a pending publication that the next live run merges and pushes. Slices whose stages (or
 * integration verifier) ended on a provider error record that, not a proof failure.
 */
export async function persistStep(
  setup: RunSetup,
  inputs: WorkflowInputs,
  plan: PlanSummary,
  gate: GateSummary,
  integration: IntegrationSummary,
  publication: PublicationSummary,
  iteration: number,
): Promise<PersistSummary> {
  const published = publication.executed;
  const outcomes: PersistSummary["outcomes"] = [];
  for (const slice of plan.slices) {
    const gated = gate.slices.find((item) => item.id === slice.id);
    if (!gated || gated.status === "not-run") continue;
    let status: SliceOutcome = gated.status;
    let note = gated.reasons.join("; ");
    let provider = gated.provider;
    if (status === "verified") {
      if (integration.conflicts.includes(slice.id)) [status, note] = ["integration-conflict", `merge conflict on ${integration.branch}`];
      else if (integration.rejected.includes(slice.id)) [status, note] = ["rejected", "merged diff failed the soundness scan"];
      else if (publication.integrationProvider && !publication.integrationVerified) {
        provider = publication.integrationProvider;
        [status, note] = [provider.kind as SliceOutcome, `integration verification: ${describeOutcome(provider)}`];
      }
      else if (!publication.integrationVerified) [status, note] = ["unverified", `integration verification did not pass: ${publication.integrationReasons.join("; ")}`];
      else note = `verified; integrated on ${integration.branch}${published ? ` and published (${publication.prUrl ?? publication.branch})` : `; not published (publish: ${publication.mode}, ${publication.summary})`}`;
    }
    const held = status === "provider-policy-blocked" && provider ? { provider: providerBlockOf(provider, setup.runKey) } : {};
    for (const fingerprint of slice.fingerprints) outcomes.push({ fingerprint, status, note, ...held });
  }
  if (inputs.dryRun) {
    writeJson(join(iterationDir(setup, iteration), "persist.json"), { committed: false, outcomes, published });
    return { committed: false, outcomes, published };
  }
  // The pending entry records exactly what the head contains: this iteration's slices and the pending integrations merged into it.
  const unpublished = !published && publication.integrationVerified && integration.merged.length > 0 && integration.branch && integration.head
    ? {
      runKey: setup.runKey, branch: integration.branch, head: integration.head, recordedAt: new Date().toISOString(),
      fingerprints: [...new Set(integration.contents.flatMap((item) => item.fingerprints))], slices: [...new Set(integration.contents.map((item) => item.slice))],
    }
    : undefined;
  await withStateLock(setup.stateDir, (state) => {
    const now = new Date();
    const pushed = publication.publication;
    const publishedOn: PublicationLink | undefined = published && pushed.activeBranch
      ? { branch: pushed.activeBranch, prNumber: pushed.prNumber, prUrl: pushed.prUrl, head: integration.head, at: now.toISOString() }
      : undefined;
    let next = recordOutcomes(state, outcomes, { runKey: setup.runKey, now, published, publishedOn });
    next = settlePublications(next, { runKey: setup.runKey, published, publishedOn, included: integration.pendingMerged, failed: integration.pendingFailed, added: unpublished, now });
    const bugReports = { ...next.bugReports };
    for (const report of publication.bugReports) {
      bugReports[report.fingerprint] = { draft: report.draft, issueUrl: report.url ?? bugReports[report.fingerprint]?.issueUrl, filedAt: report.action === "created" ? now.toISOString() : bugReports[report.fingerprint]?.filedAt };
    }
    next = { ...next, bugReports, publication: published ? publication.publication : next.publication };
    return { state: next, result: undefined };
  }, { owner: setup.runKey });
  writeJson(join(iterationDir(setup, iteration), "persist.json"), { committed: true, outcomes, published, pending: unpublished ?? null });
  return { committed: true, outcomes, published };
}

// ---------------------------------------------------------------- investigation and finalization

export function selectInvestigation(setup: RunSetup, inputs: WorkflowInputs, source: SourceSummary): { run: boolean; reason: string; digest: string } {
  const findings = readJson<Finding[]>(source.findingsPath);
  const digest = findings.map((finding) => finding.fingerprint).sort().join(",");
  const previous = readState(setup.stateDir).investigation?.digest;
  if (!inputs.investigate) return { run: false, reason: "investigations disabled by input", digest };
  if (inputs.dryRun) return { run: false, reason: "dry run: investigations not executed", digest };
  if (findings.length === 0) return { run: false, reason: "no findings to investigate", digest };
  if (previous === digest) return { run: false, reason: "findings unchanged since the last investigation", digest };
  return { run: true, reason: "findings changed since the last investigation", digest };
}

export type FinalSummary = {
  readonly evidencePath: string;
  readonly mutatingCommands: number;
  readonly worktrees: Record<string, string>;
};

export async function finalizeStep(
  setup: RunSetup,
  inputs: WorkflowInputs,
  record: {
    status: string; stopReason: string; iterations: unknown[]; investigation: { run: boolean; reason: string; digest: string }; verified: number; attempted: number;
    /** Agent stages that ended on a provider error (policy rejection or outage), with their evidence. */
    providerFailures?: readonly StageOutcome[];
  },
  worktrees: readonly string[],
  signal: AbortSignal,
  inner?: CommandRunner,
): Promise<FinalSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const removed: Record<string, string> = {};
  for (const path of worktrees) removed[path] = await removeCleanWorktree(runner, setup.repoRoot, path, signal);
  const commandsPath = join(setup.runDir, "commands.jsonl");
  const commands = existsSync(commandsPath)
    ? readFileSync(commandsPath, "utf8").split(/\r?\n/).filter(Boolean).map((line) => JSON.parse(line) as CommandLogEntry)
    : [];
  const mutating = commands.filter((entry) => entry.mutating);
  const evidencePath = writeJson(join(setup.runDir, "evidence.json"), {
    runKey: setup.runKey, startedAt: setup.startedAt, endedAt: new Date().toISOString(), inputs, toolchain: setup.toolchain,
    ...record, worktrees: removed, commandCount: commands.length, mutatingCommands: mutating,
  });
  if (!inputs.dryRun) {
    await withStateLock(setup.stateDir, (state) => ({
      state: {
        ...state,
        investigation: record.investigation.run ? { digest: record.investigation.digest, at: new Date().toISOString() } : state.investigation,
        runs: [...state.runs, { runKey: setup.runKey, startedAt: setup.startedAt, endedAt: new Date().toISOString(), stopReason: record.stopReason, verified: record.verified, attempted: record.attempted }].slice(-50),
      },
      result: undefined,
    }), { owner: setup.runKey });
  }
  return { evidencePath, mutatingCommands: mutating.length, worktrees: removed };
}

/**
 * Durable step bodies for the F* proof-checking workflow. The workflow entry file wraps each in
 * `ctx.tool(...)` so completed steps replay on resume; every external command goes through a
 * logging runner whose entries are appended to `<runDir>/commands.jsonl` as evidence.
 */
import { appendFileSync, existsSync, mkdirSync, readFileSync, statSync, writeFileSync } from "node:fs";
import { basename, isAbsolute, join, resolve } from "node:path";
import { isRemoteMutation, runChecked, spawnRunner, type CommandLogEntry, type CommandRunner } from "./command.js";
import { collectSliceChanges, decideSliceOutcome, scanDiffForUnsoundness, type VerifierVerdict } from "./gate.js";
import { ensureWorktree, removeCleanWorktree } from "./git.js";
import { planSlices, type SliceFocus } from "./plan.js";
import {
  executePublication,
  fileBugReports,
  gatherPublicationFacts,
  planPublication,
  type BugReportResult,
  type PublicationFacts,
  type PublishMode,
} from "./publish.js";
import { mergeFindings, normalizeReportTree, type Finding } from "./reports.js";
import {
  downloadRunReports,
  fromGhRuns,
  listPulseRuns,
  listSmt2,
  reportingRuns,
  reportKey,
  scanBatchCorpus,
  scanInteractiveCorpus,
  selectWindow,
  type GhRun,
  type PulseRun,
} from "./sources.js";
import {
  claimFindings,
  readState,
  recordOutcomes,
  recordSeen,
  triageFindings,
  withStateLock,
  type SliceOutcome,
  type WorkflowState,
} from "./state.js";
import type { Theory } from "./theories.js";
import { probeToolchain, type ToolchainReport } from "./toolchain.js";

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
    fstarExe: inputs.fstarExe || undefined,
    cherryFstarExe: inputs.cherryFstarExe || undefined,
    ocamlChecker: inputs.ocamlChecker || undefined,
    cherryChecker: inputs.cherryChecker || undefined,
    signal,
  });
  const setup: RunSetup = { repoRoot: root, stateDir, runKey, runDir, worktreeRoot: join(stateDir, "worktrees"), startedAt: new Date().toISOString(), toolchain };
  writeJson(join(runDir, "setup.json"), { setup, inputs });
  return setup;
}

// ---------------------------------------------------------------- sourcing

export type SourceSummary = {
  readonly findingsPath: string;
  readonly total: number;
  readonly byKind: Record<string, number>;
  readonly byTheory: Record<string, number>;
  readonly reports: Array<{ key: string; directory: string; artifacts: string[]; missing: string[] }>;
  readonly localScans: Record<string, { offset: number; cases: number; mode: string }>;
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
 * Collect findings from Pulse workflow reports (GitHub, read-only), local report directories,
 * and local corpora. In a dry run nothing remote is contacted and no checker is executed.
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
      reports.push({ key: downloaded.key, directory: downloaded.directory, artifacts: downloaded.artifacts, missing: downloaded.missing });
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
    const directory = statSync(absolute).isDirectory() ? absolute : resolve(absolute, "..");
    const key = `local-report:${directory}`;
    reports.push({ key, directory, artifacts: [basename(directory)], missing: [] });
    const normalized = normalizeReportTree(directory, { source: key });
    findings.push(...normalized.findings);
    diagnostics.push(...normalized.diagnostics);
  }
  const localScans: SourceSummary["localScans"] = {};
  for (const corpus of inputs.localCorpora) {
    if (!existsSync(corpus)) {
      diagnostics.push(`Local corpus ${corpus} does not exist; skipped.`);
      continue;
    }
    const checkers = [["ocaml", setup.toolchain.ocamlChecker], ["cherry", setup.toolchain.cherryChecker]] as const;
    const available = checkers.filter(([, path]) => path !== undefined);
    if (available.length === 0) {
      diagnostics.push(`Local corpus ${corpus} skipped: no checker executable configured (set ocamlChecker/cherryChecker or Z3_FSTAR_CHECKER/Z3_FSTAR_CHERRY_CHECKER).`);
      continue;
    }
    if (inputs.dryRun) {
      diagnostics.push(`Dry run: local corpus ${corpus} was not executed.`);
      continue;
    }
    // z3test regression inputs are incremental scripts: use interactive mode. Other corpora use the batch harness.
    const interactive = /regressions[\\/]+smt2$/i.test(corpus.replace(/[\\/]+$/, ""));
    for (const [kind, checker] of available) {
      const outputDir = join(setup.runDir, "local", `${kind}-${basename(corpus)}`);
      const key = `local-scan:${kind}:${corpus}`;
      if (interactive) {
        const files = listSmt2(corpus);
        const window = selectWindow(files, state.localScans[key]?.offset ?? 0, inputs.localCaseLimit);
        const scan = await scanInteractiveCorpus(runner, {
          checker: checker as string, corpus, files: window.selected, outputDir,
          caseTimeoutMs: 60_000, solverTimeoutMs: 10_000, concurrency: Math.max(1, Math.min(inputs.coreBudget, 32)), signal,
        });
        localScans[key] = { offset: window.nextOffset, cases: scan.cases, mode: "interactive" };
      } else if (setup.toolchain.python) {
        await scanBatchCorpus(runner, {
          python: setup.toolchain.python, repoRoot: setup.repoRoot, checker: checker as string, corpus,
          maxCases: inputs.localCaseLimit, outputDir, totalTimeoutSeconds: 1800, signal,
        });
        localScans[key] = { offset: 0, cases: inputs.localCaseLimit, mode: "batch" };
      } else {
        diagnostics.push(`Local corpus ${corpus} skipped for ${kind}: Python is required for the batch harness.`);
        continue;
      }
      const normalized = normalizeReportTree(outputDir, { source: key });
      findings.push(...normalized.findings);
      diagnostics.push(...normalized.diagnostics);
    }
  }
  const merged = mergeFindings(findings);
  const count = (key: (finding: Finding) => string) => merged.reduce<Record<string, number>>((counts, finding) => {
    counts[key(finding)] = (counts[key(finding)] ?? 0) + 1;
    return counts;
  }, {});
  const findingsPath = writeJson(join(setup.runDir, "findings.json"), merged);
  return { findingsPath, total: merged.length, byKind: count((f) => f.kind), byTheory: count((f) => f.theory), reports, localScans, diagnostics };
}

// ---------------------------------------------------------------- triage and planning

export type TriageSummary = {
  readonly actionablePath: string;
  readonly actionable: number;
  readonly skipped: Record<string, number>;
};

export function triageStep(setup: RunSetup, inputs: WorkflowInputs, findingsPath: string, iteration: number, exclude: readonly string[]): TriageSummary {
  const findings = readJson<Finding[]>(findingsPath);
  const result = triageFindings(findings, readState(setup.stateDir), { now: new Date(), theories: inputs.theories, exclude: new Set(exclude) });
  const actionablePath = writeJson(join(iterationDir(setup, iteration), "actionable.json"), result.actionable);
  return { actionablePath, actionable: result.actionable.length, skipped: result.skipped };
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
  readonly slices: Array<{ id: string; status: SliceOutcome | "not-run"; reasons: string[]; head?: string; changedFiles: number; warnings: string[] }>;
  readonly verified: number;
};

export async function gateStep(
  setup: RunSetup,
  inputs: WorkflowInputs,
  plan: PlanSummary,
  verdicts: ReadonlyArray<VerifierVerdict | null>,
  iteration: number,
  signal: AbortSignal,
  inner?: CommandRunner,
): Promise<GateSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const slices: GateSummary["slices"] = [];
  for (const [index, slice] of plan.slices.entries()) {
    if (inputs.dryRun) {
      slices.push({ id: slice.id, status: "not-run", reasons: ["dry run: no agent stages were executed"], changedFiles: 0, warnings: [] });
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

// ---------------------------------------------------------------- integration

export type IntegrationSummary = {
  readonly worktree?: string;
  readonly branch?: string;
  readonly base: string;
  readonly merged: string[];
  readonly conflicts: string[];
  readonly rejected: string[];
  readonly head?: string;
  readonly note: string;
};

async function publicationFacts(runner: CommandRunner, setup: RunSetup, inputs: WorkflowInputs, state: WorkflowState, signal: AbortSignal): Promise<PublicationFacts> {
  if (inputs.dryRun || inputs.publish === "none") {
    return { known: false, branchExists: false, prs: [], freeBranch: `${inputs.branchPrefix}/${state.publication.sequence + 1}` };
  }
  return gatherPublicationFacts(runner, state.publication, { repo: inputs.repo, remote: inputs.remote, prefix: inputs.branchPrefix, cwd: setup.repoRoot, timeoutMs: 60_000, signal });
}

/** Merge verified slice branches into a per-run integration worktree, based on the active publication branch when it is still open. */
export async function integrateStep(setup: RunSetup, inputs: WorkflowInputs, plan: PlanSummary, gate: GateSummary, iteration: number, signal: AbortSignal, inner?: CommandRunner): Promise<IntegrationSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const verified = plan.slices.filter((slice) => gate.slices.find((item) => item.id === slice.id)?.status === "verified");
  if (inputs.dryRun || verified.length === 0) {
    const summary: IntegrationSummary = { base: inputs.baseRef, merged: [], conflicts: [], rejected: [], note: inputs.dryRun ? "dry run: nothing to integrate" : "no verified slices to integrate" };
    writeJson(join(iterationDir(setup, iteration), "integration.json"), summary);
    return summary;
  }
  const state = readState(setup.stateDir);
  const facts = await publicationFacts(runner, setup, inputs, state, signal);
  const active = state.publication.activeBranch;
  const continueActive = active !== undefined && facts.known && facts.branchExists && !facts.prs.some((pr) => pr.state === "MERGED");
  const options = { cwd: setup.repoRoot, timeoutMs: 10 * 60_000, signal };
  let base = inputs.baseRef;
  if (continueActive) {
    await runChecked(runner, ["git", "fetch", inputs.remote, `refs/heads/${active}:refs/remotes/${inputs.remote}/${active}`], options);
    base = `${inputs.remote}/${active}`;
  }
  const worktree = join(setup.worktreeRoot, `${setup.runKey}-integration`);
  const branch = `${inputs.branchPrefix}/integration/${setup.runKey}`;
  await ensureWorktree(runner, setup.repoRoot, { path: worktree, branch, base, signal });
  const inTree = { cwd: worktree, timeoutMs: 10 * 60_000, signal };
  const merged: string[] = [];
  const conflicts: string[] = [];
  const rejected: string[] = [];
  for (const slice of verified) {
    const before = await runChecked(runner, ["git", "rev-parse", "HEAD"], inTree);
    const merge = await runner(["git", "merge", "--no-ff", "--no-edit", "-m", `Integrate verified slice ${slice.id}`, slice.branch], inTree);
    if (merge.code !== 0) {
      await runner(["git", "merge", "--abort"], inTree);
      conflicts.push(slice.id);
      continue;
    }
    // Re-scan the merged result: a merge must not introduce what the slice gate would reject.
    const scan = scanDiffForUnsoundness(await runChecked(runner, ["git", "diff", "--no-color", `${before}..HEAD`], inTree));
    if (scan.violations.length > 0) {
      await runChecked(runner, ["git", "reset", "--hard", before], inTree);
      rejected.push(slice.id);
      continue;
    }
    merged.push(slice.id);
  }
  const head = await runChecked(runner, ["git", "rev-parse", "HEAD"], inTree);
  const summary: IntegrationSummary = { worktree, branch, base, merged, conflicts, rejected, head, note: `merged ${merged.length} verified slice(s) onto ${base}` };
  writeJson(join(iterationDir(setup, iteration), "integration.json"), summary);
  return summary;
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
  const merged = plan.slices.filter((slice) => integration.merged.includes(slice.id));
  return [
    "## Verified F* proof-checker improvements",
    "",
    "Produced by the `fstar-proof-checking` Atomic workflow (fstar/workflow). Each slice was implemented in its own worktree, independently re-verified, scanned for admits/assumptions/raised global rlimits, merged, and the merged result was verified again.",
    "",
    "| Slice | Theory | Focus | Findings |",
    "|---|---|---|---|",
    ...merged.map((slice) => `| ${slice.id} | ${slice.theory} | ${slice.focus} | ${slice.fingerprints.join(", ")} |`),
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
): Promise<PublicationSummary> {
  const runner = evidenceRunner(setup.runDir, inner);
  const state = readState(setup.stateDir);
  const integrationVerified = integration.merged.length > 0 && decideSliceOutcome({
    scan: { violations: [], warnings: [] }, changedFiles: integration.merged.length, uncommitted: false, verifier: verdict ?? undefined, toolchainAvailable: setup.toolchain.available,
  }).status === "verified";
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
    blocked: action.kind === "blocked" ? action.reason : undefined,
    integrationVerified,
    bugReports,
    publication: result.state,
  };
  writeJson(join(iterationDir(setup, iteration), "publication.json"), { ...summary, plan: publicationPlan });
  return summary;
}

// ---------------------------------------------------------------- persistence

export type PersistSummary = {
  readonly committed: boolean;
  readonly outcomes: Array<{ fingerprint: string; status: SliceOutcome; note: string }>;
  readonly processedReports: string[];
};

/** Record outcomes, processed reports, local scan offsets and publication state (not in dry runs). */
export async function persistStep(
  setup: RunSetup,
  inputs: WorkflowInputs,
  source: SourceSummary,
  plan: PlanSummary,
  gate: GateSummary,
  integration: IntegrationSummary,
  publication: PublicationSummary,
  iteration: number,
): Promise<PersistSummary> {
  const outcomes: PersistSummary["outcomes"] = [];
  for (const slice of plan.slices) {
    const gated = gate.slices.find((item) => item.id === slice.id);
    if (!gated || gated.status === "not-run") continue;
    let status: SliceOutcome = gated.status;
    let note = gated.reasons.join("; ");
    if (status === "verified") {
      if (integration.conflicts.includes(slice.id)) [status, note] = ["integration-conflict", `merge conflict on ${integration.branch}`];
      else if (integration.rejected.includes(slice.id)) [status, note] = ["rejected", "merged diff failed the soundness scan"];
      else if (!publication.integrationVerified) [status, note] = ["unverified", "integration verification did not pass"];
      else note = `verified; integrated on ${integration.branch}${publication.prUrl ? ` (${publication.prUrl})` : ` (publish: ${publication.mode})`}`;
    }
    for (const fingerprint of slice.fingerprints) outcomes.push({ fingerprint, status, note });
  }
  const processedReports = iteration === 1 ? source.reports.map((report) => report.key) : [];
  if (inputs.dryRun) {
    writeJson(join(iterationDir(setup, iteration), "persist.json"), { committed: false, outcomes, processedReports });
    return { committed: false, outcomes, processedReports };
  }
  await withStateLock(setup.stateDir, (state) => {
    const now = new Date();
    let next = iteration === 1 ? recordSeen(state, readJson<Finding[]>(source.findingsPath), now) : state;
    next = recordOutcomes(next, outcomes, { runKey: setup.runKey, now });
    const reportsSeen = { ...next.processedReports };
    for (const key of processedReports) reportsSeen[key] = { processedAt: now.toISOString(), findings: source.total };
    const localScans = { ...next.localScans };
    if (iteration === 1) {
      for (const [key, scan] of Object.entries(source.localScans)) localScans[key] = { at: now.toISOString(), offset: scan.offset };
    }
    const bugReports = { ...next.bugReports };
    for (const report of publication.bugReports) {
      bugReports[report.fingerprint] = { draft: report.draft, issueUrl: report.url ?? bugReports[report.fingerprint]?.issueUrl, filedAt: report.action === "created" ? now.toISOString() : bugReports[report.fingerprint]?.filedAt };
    }
    next = { ...next, processedReports: reportsSeen, localScans, bugReports, publication: publication.executed ? publication.publication : next.publication };
    return { state: next, result: undefined };
  }, { owner: setup.runKey });
  writeJson(join(iterationDir(setup, iteration), "persist.json"), { committed: true, outcomes, processedReports });
  return { committed: true, outcomes, processedReports };
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
  record: { status: string; stopReason: string; iterations: unknown[]; investigation: { run: boolean; reason: string; digest: string }; verified: number; attempted: number },
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

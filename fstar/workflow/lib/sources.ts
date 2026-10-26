/**
 * Input sources: Pulse workflow runs and their report artifacts on GitHub (read-only), and the
 * local corpora named in the instructions (z3test `regressions/smt2` in interactive mode and
 * `C:\bench\inputs` in batch mode through `fstar/tools/run_checker_regressions.py`).
 */
import { copyFileSync, existsSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, statSync, writeFileSync } from "node:fs";
import { basename, dirname, join, relative, resolve } from "node:path";
import { runChecked, type CommandRunner } from "./command.js";

/**
 * Processed-report key of a local report: `local-report:<dir>` for a report directory, and
 * `local-build:<file>@<mtimeMs>` for a single build log, so a rewritten log is new evidence.
 * The workflow records these keys and the continuity launcher checks the same keys.
 */
export function localReportKey(path: string): string {
  const absolute = resolve(path);
  const stats = statSync(absolute);
  return stats.isDirectory() ? `local-report:${absolute}` : `local-build:${absolute}@${Math.trunc(stats.mtimeMs)}`;
}

export const REGRESSIONS_WORKFLOW = "pulse-checker-regressions.yml";
export const BUILD_WORKFLOW = "pulse-checker-build.yml";

export type PulseWorkflow = "regressions" | "build";

export interface PulseRun {
  readonly id: number;
  readonly attempt: number;
  readonly status: string;
  readonly conclusion: string;
  readonly createdAt: string;
  readonly headBranch: string;
  readonly workflow: PulseWorkflow;
}

/** Shape of `gh run list --json databaseId,attempt,status,conclusion,createdAt,headBranch`. */
export interface GhRun {
  databaseId: number;
  attempt: number;
  status: string;
  conclusion: string;
  createdAt: string;
  headBranch: string;
}

export function reportKey(run: Pick<PulseRun, "id" | "attempt" | "workflow">): string {
  return `${run.workflow === "build" ? "pulse-build" : "pulse-run"}:${run.id}-${run.attempt}`;
}

export function fromGhRuns(rows: readonly GhRun[], workflow: PulseWorkflow): PulseRun[] {
  return rows.map((row) => ({
    id: row.databaseId,
    attempt: row.attempt,
    status: row.status,
    conclusion: row.conclusion,
    createdAt: row.createdAt,
    headBranch: row.headBranch,
    workflow,
  }));
}

export async function listPulseRuns(
  runner: CommandRunner,
  options: { repo: string; limit: number; branch?: string; signal?: AbortSignal },
): Promise<PulseRun[]> {
  const runs: PulseRun[] = [];
  for (const [file, workflow] of [[REGRESSIONS_WORKFLOW, "regressions"], [BUILD_WORKFLOW, "build"]] as const) {
    const output = await runChecked(runner, [
      "gh", "run", "list", "--repo", options.repo, "--workflow", file, "--limit", String(options.limit),
      "--json", "databaseId,attempt,status,conclusion,createdAt,headBranch",
      ...(options.branch ? ["--branch", options.branch] : []),
    ], { timeoutMs: 60_000, signal: options.signal });
    runs.push(...fromGhRuns(output === "" ? [] : (JSON.parse(output) as GhRun[]), workflow));
  }
  return runs;
}

/**
 * Runs that publish reports worth processing: completed regression runs (success or failure —
 * PARTIAL is coverage debt even on success) and failed or timed-out checker builds. Skipped and
 * approval-gated runs carry no reports.
 */
export function reportingRuns(runs: readonly PulseRun[]): PulseRun[] {
  return runs.filter((run) => run.status === "completed" && (
    run.workflow === "regressions"
      ? run.conclusion === "success" || run.conclusion === "failure"
      : run.conclusion === "failure" || run.conclusion === "timed_out"
  ));
}

export function artifactNames(run: Pick<PulseRun, "id" | "attempt" | "workflow">): string[] {
  return run.workflow === "build"
    ? ["pulse-checker-build-report"]
    : [`pulse-checker-report-${run.id}-${run.attempt}`, `pulse-checker-cherry-report-${run.id}-${run.attempt}`];
}

export interface DownloadedReport {
  readonly key: string;
  readonly directory: string;
  readonly artifacts: string[];
  readonly missing: string[];
  readonly cached: boolean;
}

/** Download a run's report artifacts once into `cacheDir/<key>`; later calls reuse the cache. */
export async function downloadRunReports(
  runner: CommandRunner,
  run: PulseRun,
  options: { repo: string; cacheDir: string; signal?: AbortSignal },
): Promise<DownloadedReport> {
  const key = reportKey(run);
  const directory = join(options.cacheDir, key.replace(":", "-"));
  const marker = join(directory, ".complete.json");
  if (existsSync(marker)) {
    const recorded = JSON.parse(readFileSync(marker, "utf8")) as { artifacts: string[]; missing: string[] };
    return { key, directory, ...recorded, cached: true };
  }
  const staging = `${directory}.partial-${process.pid}`;
  rmSync(staging, { recursive: true, force: true });
  mkdirSync(staging, { recursive: true });
  const artifacts: string[] = [];
  const missing: string[] = [];
  for (const name of artifactNames(run)) {
    const result = await runner(["gh", "run", "download", String(run.id), "--repo", options.repo, "--name", name, "--dir", join(staging, name)], {
      timeoutMs: 10 * 60_000,
      signal: options.signal,
    });
    if (result.code === 0) artifacts.push(name);
    else if (/no (?:valid )?artifacts?|not found|expired/i.test(`${result.stderr}${result.stdout}`)) missing.push(name);
    else throw new Error(`gh run download ${run.id} --name ${name} failed: ${(result.error ?? result.stderr).trim()}`);
  }
  writeFileSync(join(staging, ".complete.json"), JSON.stringify({ run, artifacts, missing }, null, 2));
  rmSync(directory, { recursive: true, force: true });
  renameSync(staging, directory);
  return { key, directory, artifacts, missing, cached: false };
}

/** Sorted `.smt2` files below a directory. */
export function listSmt2(root: string): string[] {
  const files: string[] = [];
  const visit = (directory: string) => {
    for (const entry of readdirSync(directory, { withFileTypes: true }).sort((left, right) => (left.name < right.name ? -1 : left.name > right.name ? 1 : 0))) {
      const path = join(directory, entry.name);
      const isDirectory = entry.isDirectory() || (entry.isSymbolicLink() && statSync(path).isDirectory());
      if (isDirectory) visit(path);
      else if (entry.name.endsWith(".smt2")) files.push(path);
    }
  };
  if (existsSync(root)) visit(root);
  return files;
}

/** Rotate through a corpus across runs: take `limit` files starting at `offset`, wrapping around. */
export function selectWindow<T>(items: readonly T[], offset: number, limit: number): { selected: T[]; nextOffset: number } {
  if (items.length === 0 || limit <= 0) return { selected: [], nextOffset: 0 };
  const start = offset % items.length;
  const count = Math.min(limit, items.length);
  const selected = Array.from({ length: count }, (_, index) => items[(start + index) % items.length] as T);
  return { selected, nextOffset: (start + count) % items.length };
}

/** `.smt2` files of a batch corpus grouped by top-level directory (one per logic; files at the top level form group `.`). */
export function listSmt2ByGroup(root: string): Array<[string, string[]]> {
  const groups = new Map<string, string[]>();
  for (const file of listSmt2(root)) {
    const [first, ...rest] = relative(root, file).split(/[\\/]/);
    const group = rest.length > 0 && first !== undefined ? first : ".";
    const members = groups.get(group);
    if (members) members.push(file);
    else groups.set(group, [file]);
  }
  return [...groups.entries()];
}

/**
 * Rotate through a corpus with one directory per logic: `limit` cases are shared evenly between
 * the groups, so a run with `limit` ≥ the number of groups reaches every group. Each group keeps
 * its own rotating offset; `offset` is where the share of the remainder (`limit` mod groups)
 * starts, so smaller limits rotate through the groups across runs.
 */
export function selectStratifiedWindow(
  groups: ReadonlyArray<readonly [string, readonly string[]]>,
  position: { readonly offset?: number; readonly groupOffsets?: Readonly<Record<string, number>> } | undefined,
  limit: number,
): { selected: string[]; nextOffset: number; groupOffsets: Record<string, number> } {
  const groupOffsets = { ...(position?.groupOffsets ?? {}) };
  const nonEmpty = groups.filter(([, files]) => files.length > 0);
  if (nonEmpty.length === 0 || limit <= 0) return { selected: [], nextOffset: position?.offset ?? 0, groupOffsets };
  const start = (position?.offset ?? 0) % nonEmpty.length;
  const share = Math.floor(limit / nonEmpty.length);
  const extra = limit % nonEmpty.length;
  const selected: string[] = [];
  for (let index = 0; index < nonEmpty.length; index += 1) {
    const [group, files] = nonEmpty[(start + index) % nonEmpty.length] as readonly [string, readonly string[]];
    const window = selectWindow(files, groupOffsets[group] ?? 0, share + (index < extra ? 1 : 0));
    if (window.selected.length === 0) continue;
    selected.push(...window.selected);
    groupOffsets[group] = window.nextOffset;
  }
  return { selected, nextOffset: (start + extra) % nonEmpty.length, groupOffsets };
}

/** Copy the selected inputs below `stageRoot`, keeping their paths relative to `corpus` (the harness rejects symlinks). */
export function stageFiles(corpus: string, files: readonly string[], stageRoot: string): string {
  rmSync(stageRoot, { recursive: true, force: true });
  for (const file of files) {
    const target = join(stageRoot, relative(corpus, file));
    mkdirSync(dirname(target), { recursive: true });
    copyFileSync(file, target);
  }
  return stageRoot;
}

export interface InteractiveCase {
  readonly verdicts: string[];
  readonly obligations: Array<{ rule: string; count: number; first_index: number; fingerprint: string }>;
}

/**
 * Parse an interactive checker session: `; proof-check ACCEPT|PARTIAL n|REJECT` comments on
 * stdout and `obligation\t<rule>\t<count>\t<first>\t<fingerprint>` diagnostics on stderr.
 */
export function parseInteractiveSession(stdout: string, stderr: string): InteractiveCase {
  const verdicts = [...stdout.matchAll(/^; proof-check (ACCEPT|PARTIAL \d+|REJECT)\s*$/gm)].map((match) => match[1] as string);
  const obligations = stderr.split(/\r?\n/).flatMap((line) => {
    const fields = line.split("\t");
    return fields[0] === "obligation" && fields.length === 5
      ? [{ rule: fields[1] as string, count: Number(fields[2]), first_index: Number(fields[3]), fingerprint: fields[4] as string }]
      : [];
  });
  return { verdicts, obligations };
}

/** Session exit status: 2 command/checker error, 1 any rejection, 3 any partial, 0 otherwise. */
function interactiveOutcome(code: number | null, error: string | undefined, session: InteractiveCase): string | undefined {
  if (error?.startsWith("timed out")) return "TIMEOUT";
  if (code === null || code < 0 || code > 3) return "CRASH";
  if (code === 2) return "ERROR";
  if (code === 1) return "REJECT";
  if (code === 3) return "PARTIAL";
  return session.verdicts.length > 0 ? "ACCEPT" : undefined;
}

export interface CorpusScanOptions {
  /** Checker command (in the build environment, e.g. `wsl -d Ubuntu -e /path/checker`). */
  readonly checkerArgv: readonly string[];
  readonly corpus: string;
  readonly files: readonly string[];
  readonly outputDir: string;
  readonly caseTimeoutMs: number;
  readonly solverTimeoutMs: number;
  readonly concurrency: number;
  readonly signal?: AbortSignal;
}

/**
 * Run the checker's `--interactive` mode on each file and write `results.jsonl` and
 * `diagnostics.jsonl` in the regression-harness format so the normal report normalizer applies.
 */
export async function scanInteractiveCorpus(runner: CommandRunner, options: CorpusScanOptions): Promise<{ cases: number; outcomes: Record<string, number> }> {
  mkdirSync(options.outputDir, { recursive: true });
  const results: string[] = new Array(options.files.length);
  const diagnostics: string[] = new Array(options.files.length);
  const outcomes: Record<string, number> = {};
  let next = 0;
  const work = async () => {
    for (let index = next++; index < options.files.length; index = next++) {
      const file = options.files[index] as string;
      const path = relative(options.corpus, file).replaceAll("\\", "/");
      const started = Date.now();
      const result = await runner(
        [...options.checkerArgv, "--interactive", "--stats", "--diagnostics", "--timeout-ms", String(options.solverTimeoutMs)],
        { input: readFileSync(file, "utf8"), timeoutMs: options.caseTimeoutMs, signal: options.signal },
      );
      const session = parseInteractiveSession(result.stdout, result.stderr);
      const outcome = interactiveOutcome(result.code, result.error, session) ?? "NOT_CHECKED";
      outcomes[outcome] = (outcomes[outcome] ?? 0) + 1;
      const row = { path, returncode: result.code, outcome, verdict: session.verdicts.join("; "), wall_seconds: (Date.now() - started) / 1000, mode: "interactive" };
      results[index] = JSON.stringify(row);
      diagnostics[index] = outcome === "PARTIAL" || outcome === "REJECT"
        ? JSON.stringify({ ...row, matches_original: true, diagnostics: { obligations: session.obligations } })
        : "";
    }
  };
  await Promise.all(Array.from({ length: Math.max(1, options.concurrency) }, work));
  writeFileSync(join(options.outputDir, "results.jsonl"), results.filter(Boolean).map((line) => `${line}\n`).join(""));
  writeFileSync(join(options.outputDir, "diagnostics.jsonl"), diagnostics.filter(Boolean).map((line) => `${line}\n`).join(""));
  return { cases: options.files.length, outcomes };
}

/**
 * Batch-mode scan through the existing regression harness (`run`, `diagnose`, `report`). The
 * harness runs in the build environment; `toEnvironment` translates host paths for it.
 */
export async function scanBatchCorpus(
  runner: CommandRunner,
  options: {
    pythonArgv: readonly string[]; toEnvironment: (path: string) => string; repoRoot: string; checker: string; corpus: string;
    maxCases: number; outputDir: string; totalTimeoutSeconds: number; signal?: AbortSignal;
  },
): Promise<void> {
  const harness = options.toEnvironment(join(options.repoRoot, "fstar", "tools", "run_checker_regressions.py"));
  const output = options.toEnvironment(options.outputDir);
  const common = { cwd: options.repoRoot, timeoutMs: (options.totalTimeoutSeconds * 2 + 300) * 1000, signal: options.signal };
  const parent = options.toEnvironment(dirname(options.corpus));
  mkdirSync(options.outputDir, { recursive: true });
  // `run` and `diagnose` exit 1 when cases crash or error; those cases are findings, not harness failures.
  const run = await runner([
    ...options.pythonArgv, harness, "run", "--checker", options.checker, "--corpus", parent, "--corpus-path", basename(options.corpus),
    "--corpus-commit", "local-unversioned", "--max-cases", String(options.maxCases),
    "--total-timeout-seconds", String(options.totalTimeoutSeconds), "--output", output,
  ], common);
  if (run.code !== 0 && run.code !== 1) throw new Error(`run_checker_regressions.py run failed: ${run.error ?? run.stderr}`);
  const diagnose = await runner([
    ...options.pythonArgv, harness, "diagnose", "--checker", options.checker, "--corpus", parent, "--output", output,
    "--total-timeout-seconds", String(options.totalTimeoutSeconds),
  ], common);
  if (diagnose.code !== 0 && diagnose.code !== 1) throw new Error(`diagnose failed: ${diagnose.error ?? diagnose.stderr}`);
  await runChecked(runner, [...options.pythonArgv, harness, "report", "--output", output], common);
}

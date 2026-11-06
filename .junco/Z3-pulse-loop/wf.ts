/**
 * Pulse/F* proof-checker development loop for elefthei/z3 (wf.yml is one iteration).
 *
 * Forever: reset a dedicated worktree to origin/master, build the native checker and run the z3test
 * proof corpora (cached per SHA), analyze pending obligations, assign the next work-queue item to the
 * Developer agent, rebuild and re-run on its changes, and open `loop/junco-N` as a PR when the
 * deterministic judge accepts. Every iteration is one Opik trace; every run's analytics are Grafana
 * probes (`junco_probe_value`, node Analytics = before, node Verify = after) and one line of
 * `<state>/analytics.jsonl`. The queue lives in `<state>/queue.json`.
 *
 * Run: `bun run wf.ts` (see README.md) (Ctrl-C stops after the current step). Environment:
 *   Z3_PULSE_LOOP_REPO (~/git/z3)  Z3_PULSE_LOOP_STATE (/btrfs/Z3-pulse-loop; must be on a btrfs mount with
 *   user_subvol_rm_allowed because agent tools run in a btrfs seed: the worktree is a subvolume)
 *   (opam's default switch is used; it must be OCaml 5.3.0 + ocamlfind + zarith)
 *   FSTAR_EXE (/opt/fstar-v2026.09.27/bin/fstar.exe: the CI pin of
 *   .github/workflows/pulse-checker-regressions.yml; the 2026-11-05 nightly rejects Z3PulseLraChecker.fst)
 *   Z3_PULSE_LOOP_MAX_CASES (0 = whole corpora; CI's max_cases)
 *   GRAFANA_URL (http://localhost:8000)  OPIK_URL_OVERRIDE / OPIK_PROJECT_NAME (SDK defaults)
 * Prerequisites: pwsh, cmake/g++/libgmp-dev, an opam switch with OCaml 5.3.0 + ocamlfind + zarith,
 * python3, btrfs-progs, gh authenticated for elefthei/z3, a saved github-copilot Pi login.
 */
import { execFileSync } from "node:child_process";
import { closeSync, existsSync, openSync } from "node:fs";
import { appendFile, mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import { cpus, homedir } from "node:os";
import { join } from "node:path";
import { contentText } from "@earendil-works/pi-ai";
import { ModelRuntime } from "@earendil-works/pi-coding-agent";
import { OpikTracer } from "dataflow-engine-opik";
import { agent, graph, JuncoGraph, schedules, syntax, tools, tracer } from "junco";
import { Opik } from "opik";
import type { TSchema } from "typebox";
import source from "./wf.yml" with { type: "text" };

// Verified 2026-11-05: refreshed Pi catalog (aborted=false, no provider errors), saved github-copilot
// OAuth login, claude-opus-5.5 supports "high". https://github.blog/changelog/2026-09-22-claude-opus-5-5-is-now-available-in-github-copilot/
// and https://docs.github.com/copilot/reference/ai-models/supported-models list it as GA.
const DEVELOPER = { model: "github-copilot/claude-opus-5.5", thinking: "high" } as const;
export const ladder: schedules.Ladder = { smol: DEVELOPER, low: DEVELOPER, med: DEVELOPER, high: DEVELOPER, xhigh: DEVELOPER };
export const document = syntax.parse(source);
schedules.validateLadder(ladder);

const PR_REPO = "elefthei/z3";
/** gh login used for the push and the PR: the repo owner (this machine's active gh account differs). */
const PR_USER = PR_REPO.split("/")[0]!;
const BASE = "master";
/** The two corpora of .github/workflows/pulse-checker-regressions.yml, with its default budgets. */
const CORPORA = [
  { name: "proofs", path: "regressions/proofs", total: 1800, memory: 2048, manifest: false },
  { name: "smtlib-sample", path: "regressions/smtlib-sample", total: 3600, memory: 4096, manifest: true },
] as const;
const ERRORS = new Set(["ERROR", "CRASH", "PROTOCOL_ERROR"]);
/** Harness budgets (run_checker_regressions.py arguments in `regress`); cases already at ≥80% of one are run-to-run noise. */
const SOLVER_BUDGET_MS = 10_000, CASE_BUDGET_S = 60;
const atBudget = (b: CaseStat) => b.wall >= 0.8 * CASE_BUDGET_S || (b.solveMs ?? 0) >= 0.8 * SOLVER_BUDGET_MS;
const KIND_RANK = { crash: 0, reject: 1, obligation: 2, timeout: 3, slow: 4 } as const;
/** Pause after an idle iteration (empty queue) or an unbuildable master so the loop does not spin. */
const PAUSE_MS = 10 * 60_000;

export type Paths = {
  repo: string; state: string; worktree: string; corpus: string; fstarExe: string; opamSwitch: string;
  z3Build: string; z3Install: string; fstarCache: string; checkerDir: string; checker: string; maxCases: number;
};
export function paths(env: NodeJS.ProcessEnv = process.env): Paths {
  const state = env.Z3_PULSE_LOOP_STATE ?? "/btrfs/Z3-pulse-loop";
  const maxCases = Number(env.Z3_PULSE_LOOP_MAX_CASES ?? 0);
  if (!Number.isInteger(maxCases) || maxCases < 0) throw new Error("Z3_PULSE_LOOP_MAX_CASES must be a non-negative integer");
  return {
    repo: env.Z3_PULSE_LOOP_REPO ?? join(homedir(), "git", "z3"), state, worktree: join(state, "worktree"),
    corpus: join(state, "z3test"), fstarExe: env.FSTAR_EXE ?? "/opt/fstar-v2026.09.27/bin/fstar.exe",
    opamSwitch: execFileSync("opam", ["switch", "show"], { encoding: "utf8" }).trim(),
    z3Build: join(state, "z3-build"), z3Install: join(state, "z3-install"),
    fstarCache: join(state, "fstar-cache"), checkerDir: join(state, "checker"), checker: join(state, "checker", "checker"), maxCases,
  };
}

export type CaseStat = { outcome: string; wall: number; solveMs?: number; checkMs?: number; proofNodes?: number; pending?: number; stage?: string };
export type Family = { rule: string; shape: string; pending: number; cases: { path: string; count: number; first: string }[] };
export type Analysis = {
  sha: string; buildOk: boolean; tested: number; counts: Record<string, number>;
  pending: number; proofNodes: number; checkMs: number; solveMs: number;
  families: Family[]; cases: Record<string, CaseStat>; lemmas: number; assumed: number;
};
export type Item = {
  id: string; kind: keyof typeof KIND_RANK; title: string; detail: string; cases: string[]; weight: number;
  attempts: number; status: "open" | "pr"; pr?: string; notes: string[];
};
export type Queue = { items: Item[] };
/** Shared cycle state: Regress advances `iteration`/`sha` at the start of each cycle; the chain is strictly sequential, so later nodes read the current cycle's values. */
export type Loop = { iteration: number; sha: string; paths: Paths };
type Edge = graph.Edge<TSchema, unknown>;

const log = (message: string) => console.error(`[Z3-pulse-loop ${new Date().toISOString()}] ${message}`);
const familyId = (rule: string, shape: string) => `obligation:${rule}|${shape}`;

/** Run `cmd`; with `log`, both streams append in order to that file (one shared descriptor), else they are captured. */
async function sh(cmd: string[], options: { cwd: string; log?: string; env?: Record<string, string>; signal?: AbortSignal; timeoutMs?: number }): Promise<{ code: number; stdout: string; stderr: string }> {
  const fd = options.log === undefined ? undefined : openSync(options.log, "w");
  try {
    const proc = Bun.spawn(cmd, { cwd: options.cwd, stdout: fd ?? "pipe", stderr: fd ?? "pipe", stdin: "ignore", env: { ...process.env, ...options.env }, signal: options.signal, timeout: options.timeoutMs, killSignal: "SIGKILL" });
    const [stdout, stderr] = fd === undefined ? await Promise.all([new Response(proc.stdout as ReadableStream).text(), new Response(proc.stderr as ReadableStream).text()]) : ["", ""];
    const code = await proc.exited;
    options.signal?.throwIfAborted();
    return { code, stdout, stderr };
  } finally {
    if (fd !== undefined) closeSync(fd);
  }
}
async function must(cmd: string[], options: Parameters<typeof sh>[1]): Promise<string> {
  const result = await sh(cmd, options);
  if (result.code !== 0) throw new Error(`${cmd.join(" ")} failed (${result.code}): ${result.stderr.trim() || result.stdout.trim()}`);
  return result.stdout;
}
/** The build script's shell: the opam switch's environment, as the CI job runs it. */
const withOpam = (p: Paths, cmd: string[]) => ["bash", "-c", 'eval "$(opam env --switch="$0" --set-switch)" && exec "$@"', p.opamSwitch, ...cmd];

async function pool<T, R>(items: readonly T[], width: number, fn: (item: T) => Promise<R>): Promise<R[]> {
  const results: R[] = new Array(items.length);
  let next = 0;
  await Promise.all(Array.from({ length: Math.min(width, items.length) }, async () => {
    for (let i = next++; i < items.length; i = next++) results[i] = await fn(items[i]!);
  }));
  return results;
}

/** Build the checker in the worktree and run both corpora into `out/<corpus>/`; `build.json` as in CI. */
export async function regress(p: Paths, out: string, signal?: AbortSignal): Promise<boolean> {
  await mkdir(out, { recursive: true });
  const start = Date.now();
  const build = await sh(withOpam(p, ["pwsh", "-NoProfile", "-File", "fstar/tools/build_ocaml_checker.ps1", "-FstarExe", p.fstarExe,
    "-Z3WindowsBuildDir", p.z3Build, "-Z3InstallDir", p.z3Install, "-CacheDir", p.fstarCache, "-WslBuildDir", p.checkerDir,
    "-OpamSwitch", p.opamSwitch, "-BuildJobs", String(Math.min(64, cpus().length)), "-RunTests"]), { cwd: p.worktree, log: join(out, "build.log"), signal });
  await writeFile(join(out, "build.json"), `${JSON.stringify({ wall_seconds: Math.round((Date.now() - start) / 1000), exit_code: build.code, fstar_exe: p.fstarExe })}\n`);
  if (build.code !== 0) return false;
  const commit = (await must(["git", "rev-parse", "HEAD"], { cwd: p.corpus })).trim();
  for (const c of CORPORA) {
    const dir = join(out, c.name);
    const manifest = c.manifest && p.maxCases === 0 ? ["--manifest", join(p.corpus, c.path, "manifest.json"), "--expected-cases", "225"] : [];
    const run = await sh(["python3", "fstar/tools/run_checker_regressions.py", "run", "--checker", p.checker, "--corpus", p.corpus, "--corpus-path", c.path,
      "--corpus-commit", commit, "--max-cases", String(p.maxCases), "--solver-timeout-ms", "10000", "--case-timeout-seconds", "60",
      "--total-timeout-seconds", String(c.total), "--memory-limit-mb", String(c.memory), ...manifest, "--output", dir], { cwd: p.worktree, log: join(out, `${c.name}.log`), signal });
    await must(["python3", "fstar/tools/run_checker_regressions.py", "report", "--output", dir], { cwd: p.worktree, signal, env: { BUILD_OUTCOME: "success", RUNNER_OUTCOME: run.code === 0 ? "success" : "failure" } });
  }
  return true;
}

const STATS = /solve_ms=([\d.]+) marshal_ms=([\d.]+) check_ms=([\d.]+) expressions=\d+ declarations=\d+ proof_nodes=(\d+)/;

/** Parse a run (both corpora), re-check PARTIAL/REJECT cases with --diagnostics (cached), count F* markers. */
export async function analyze(p: Paths, out: string, sha: string, signal?: AbortSignal): Promise<Analysis> {
  const build = JSON.parse(await readFile(join(out, "build.json"), "utf8")) as { exit_code: number };
  const a: Analysis = { sha, buildOk: build.exit_code === 0, tested: 0, counts: {}, pending: 0, proofNodes: 0, checkMs: 0, solveMs: 0, families: [], cases: {}, lemmas: 0, assumed: 0 };
  const diagPath = join(out, "diagnostics.json");
  const diagnostics: Record<string, { stage?: string; families: [string, string, number, string][] }> = existsSync(diagPath) ? JSON.parse(await readFile(diagPath, "utf8")) : {};
  const toDiagnose: string[] = [];
  for (const c of CORPORA) {
    const file = join(out, c.name, "results.jsonl");
    if (!existsSync(file)) continue;
    for (const line of (await readFile(file, "utf8")).split("\n").filter(Boolean)) {
      const row = JSON.parse(line) as { path: string; outcome: string; wall_seconds?: number; stderr?: string };
      if (row.outcome === "NOT_RUN") continue;
      const stat: CaseStat = { outcome: row.outcome, wall: row.wall_seconds ?? 0 };
      const match = row.stderr ? STATS.exec(await readFile(join(out, c.name, row.stderr), "utf8").catch(() => "")) : null;
      if (match) { stat.solveMs = Number(match[1]); stat.checkMs = Number(match[3]); stat.proofNodes = Number(match[4]); a.solveMs += stat.solveMs; a.checkMs += stat.checkMs; a.proofNodes += stat.proofNodes; }
      a.cases[row.path] = stat;
      a.tested++;
      a.counts[row.outcome] = (a.counts[row.outcome] ?? 0) + 1;
      if ((row.outcome === "PARTIAL" || row.outcome === "REJECT") && !(row.path in diagnostics)) toDiagnose.push(row.path);
    }
  }
  if (toDiagnose.length) {
    await pool(toDiagnose, Math.min(32, cpus().length), async (path) => {
      const { stderr } = await sh([p.checker, "--diagnostics", "--timeout-ms", "10000", join(p.corpus, path)], { cwd: p.worktree, signal, timeoutMs: 120_000 });
      const entry: (typeof diagnostics)[string] = { families: [] };
      for (const line of stderr.split("\n")) {
        const f = line.split("\t");
        if (f[0] === "obligation" && f.length >= 5) entry.families.push([f[1]!, f[4]!, Number(f[2]), f[3]!]);
        else if (f[0] === "diagnostic" && f[1] === "rejected") entry.stage = f.slice(2).join(" ");
      }
      diagnostics[path] = entry;
    });
    await writeFile(diagPath, JSON.stringify(diagnostics));
  }
  const families = new Map<string, Family>();
  for (const [path, stat] of Object.entries(a.cases)) {
    const d = diagnostics[path];
    if (!d) continue;
    if (d.stage) stat.stage = d.stage;
    stat.pending = 0;
    for (const [rule, shape, count, first] of d.families) {
      stat.pending += count;
      const family = families.get(familyId(rule, shape)) ?? { rule, shape, pending: 0, cases: [] };
      family.pending += count;
      family.cases.push({ path, count, first });
      families.set(familyId(rule, shape), family);
    }
    a.pending += stat.pending;
  }
  a.families = [...families.values()].sort((x, y) => y.pending - x.pending || x.rule.localeCompare(y.rule));
  for (const family of a.families) family.cases.sort((x, y) => y.count - x.count);
  const fstar = join(p.worktree, "fstar");
  for (const name of await readdir(fstar)) {
    if (!/\.fsti?$/.test(name)) continue;
    for (const line of (await readFile(join(fstar, name), "utf8")).split("\n")) {
      const code = line.replace(/\/\/.*$/, "");
      if (/\bLemma\b/.test(code)) a.lemmas++;
      if (/^\s*assume\b/.test(code) || /\badmit\s*\(/.test(code)) a.assumed++;
    }
  }
  return a;
}

/** The probe series of one analysis: what the Z3 authors track per run. */
export function metrics(a: Analysis): Record<string, number> {
  return {
    build_ok: a.buildOk ? 1 : 0, tested: a.tested, accept: a.counts.ACCEPT ?? 0, partial: a.counts.PARTIAL ?? 0, reject: a.counts.REJECT ?? 0,
    timeout: a.counts.TIMEOUT ?? 0, errors: [...ERRORS].reduce((n, k) => n + (a.counts[k] ?? 0), 0),
    proof_steps_total: a.proofNodes, proof_steps_pending: a.pending, proof_steps_checked: a.proofNodes - a.pending,
    obligation_families: a.families.length, check_ms_total: Math.round(a.checkMs), solve_ms_total: Math.round(a.solveMs),
    fstar_lemmas: a.lemmas, fstar_assumed: a.assumed,
  };
}

/** Rebuild the queue from an analysis, keeping attempts/notes/PR state of items that still exist. */
export function refreshQueue(queue: Queue, a: Analysis): Queue {
  const previous = new Map(queue.items.map((item) => [item.id, item]));
  const fresh: Item[] = [];
  const add = (item: Omit<Item, "attempts" | "status" | "notes">) => {
    const old = previous.get(item.id);
    fresh.push({ attempts: 0, status: "open", notes: [], ...old, ...item });
  };
  const rejects = new Map<string, string[]>();
  for (const [path, stat] of Object.entries(a.cases)) {
    if (ERRORS.has(stat.outcome)) add({ id: `crash:${path}`, kind: "crash", title: `Fix ${stat.outcome} on ${path}`, detail: `The checker exits with ${stat.outcome} (see the run's stderr log).`, cases: [path], weight: 1 });
    else if (stat.outcome === "TIMEOUT") add({ id: `timeout:${path}`, kind: "timeout", title: `Finish ${path} within the 60 s case budget`, detail: "The case times out (10 s solver budget, 60 s total).", cases: [path], weight: 1 });
    else if (stat.outcome === "REJECT") { const key = stat.stage ?? "unknown"; rejects.set(key, [...(rejects.get(key) ?? []), path]); }
  }
  for (const [stage, cases] of rejects) add({ id: `reject:${stage}`, kind: "reject", title: `Resolve REJECT (${stage}) on ${cases.length} case(s)`, detail: `The checker rejects z3's proof; either the proof hint is wrong/insufficient (fix proof logging in src/) or the checker's rule is too strict. Diagnostic: ${stage}.`, cases, weight: cases.length });
  for (const f of a.families) add({ id: familyId(f.rule, f.shape), kind: "obligation", title: `Cover ${f.rule} (${f.shape}) obligations: ${f.pending} pending in ${f.cases.length} case(s)`, detail: `Pending proof steps of rule ${f.rule}, shape ${f.shape}; first indices: ${f.cases.slice(0, 5).map((c) => `${c.path}#${c.first} (${c.count})`).join(", ")}.`, cases: f.cases.map((c) => c.path), weight: f.pending });
  const slow = Object.entries(a.cases).filter(([, s]) => s.checkMs !== undefined && (s.outcome === "ACCEPT" || s.outcome === "PARTIAL")).sort((x, y) => y[1].checkMs! - x[1].checkMs!).slice(0, 5);
  for (const [path, stat] of slow) add({ id: `slow:${path}`, kind: "slow", title: `Reduce check time of ${path} (${Math.round(stat.checkMs!)} ms)`, detail: `check_ms=${Math.round(stat.checkMs!)} for ${stat.proofNodes} proof nodes; verdict must not change.`, cases: [path], weight: stat.checkMs! });
  return { items: fresh };
}

/** Least-attempted first so failures rotate through the queue, then crash > reject > obligation > timeout > slow, then weight. */
export function pickItem(queue: Queue): Item | undefined {
  return queue.items.filter((i) => i.status === "open").sort((x, y) => x.attempts - y.attempts || KIND_RANK[x.kind] - KIND_RANK[y.kind] || y.weight - x.weight)[0];
}

/**
 * The Developer's tool collection: every shell command gets a 30 CPU-minute per-process ceiling (observed: a runaway proof-analysis
 * script stalled an iteration for hours). No recorder: per-command memory accounting needs delegated cgroup v2 controllers, which a plain
 * user process (login shell, no systemd scope) does not have; the graph recorder still gets node probes.
 */
const openCollection = (p: Paths) => tools.ToolCollection.create(p.worktree, { bash: { commandPrefix: "ulimit -t 1800" } });

/**
 * Accept only when nothing regressed, no soundness marker was added, and the item (or the corpus) improved.
 * A case that was already at a solver/case budget and now reports TIMEOUT or UNKNOWN is noise, not a regression.
 */
export function judge(item: Item, before: Analysis, after: Analysis): { ok: boolean; reasons: string[] } {
  const reasons: string[] = [], noise: string[] = [];
  if (!after.buildOk) return { ok: false, reasons: ["the checker build or its F*/Pulse regressions failed"] };
  if (after.assumed > before.assumed) reasons.push(`F* assume/admit markers increased ${before.assumed} -> ${after.assumed}`);
  for (const [path, b] of Object.entries(before.cases)) {
    const x = after.cases[path];
    if (!x) { reasons.push(`${path} was not run`); continue; }
    const worse = b.outcome === "ACCEPT" ? x.outcome !== "ACCEPT"
      : b.outcome === "PARTIAL" && (x.outcome === "PARTIAL" ? (x.pending ?? 0) > (b.pending ?? 0) : x.outcome !== "ACCEPT");
    if (!worse) continue;
    const change = `${path} ${b.outcome} ${b.pending ?? ""} -> ${x.outcome} ${x.pending ?? ""}`.replace(/\s+/g, " ").trim();
    if ((x.outcome === "TIMEOUT" || x.outcome === "UNKNOWN") && atBudget(b)) noise.push(`${change} (was at ${Math.round(b.wall)} s wall / ${Math.round(b.solveMs ?? 0)} ms solve)`);
    else reasons.push(`${change} regressed`);
  }
  if (reasons.length) return { ok: false, reasons: [...reasons, ...noise.map((n) => `budget-edge noise ignored: ${n}`)] };
  if (noise.length) reasons.push(`budget-edge noise ignored: ${noise.join(", ")}`);
  const pending = (a: Analysis) => a.families.find((f) => familyId(f.rule, f.shape) === item.id)?.pending ?? 0;
  const outcomes = item.cases.map((path) => after.cases[path]?.outcome);
  const targeted = {
    obligation: () => pending(after) < pending(before),
    reject: () => outcomes.some((o) => o === "ACCEPT" || o === "PARTIAL"),
    crash: () => outcomes.some((o) => o !== undefined && !ERRORS.has(o) && o !== "TIMEOUT"),
    timeout: () => outcomes.some((o) => o !== undefined && o !== "TIMEOUT"),
    // shortcut: a fixed 20% check-time threshold; calibrate against run-to-run noise once slow items get picked.
    slow: () => item.cases.some((path) => (after.cases[path]?.checkMs ?? Infinity) <= 0.8 * (before.cases[path]?.checkMs ?? 0)),
  }[item.kind]();
  const global = after.pending < before.pending || (after.counts.ACCEPT ?? 0) > (before.counts.ACCEPT ?? 0);
  if (targeted) reasons.push(`the targeted item improved`);
  if (global) reasons.push(`corpus improved: pending ${before.pending} -> ${after.pending}, ACCEPT ${before.counts.ACCEPT ?? 0} -> ${after.counts.ACCEPT ?? 0}`);
  if (!targeted && !global) reasons.push("neither the targeted item nor the corpus improved");
  return { ok: targeted || global, reasons };
}

export function analyticsMarkdown(before: Analysis, after?: Analysis): string {
  const m = metrics(before), n = after ? metrics(after) : undefined;
  const rows = Object.keys(m).map((k) => `| ${k} | ${m[k]} |${n ? ` ${n[k]} |` : ""}`);
  const top = (after ?? before).families.slice(0, 10).map((f) => `- ${f.rule} (${f.shape}): ${f.pending} pending in ${f.cases.length} case(s)`);
  return [`| metric | before |${n ? " after |" : ""}`, `|---|---|${n ? "---|" : ""}`, ...rows, "", "Largest remaining obligation families:", ...top].join("\n");
}

const probeAll = (c: syntax.CodeContext<Loop>, values: Record<string, number>) => {
  const view = c.recorder?.add_context(c.recorderNodeId ?? c.node);
  for (const [edgeId, value] of Object.entries({ iteration: c.context.iteration, ...values })) view?.record({ resource: "probe", kind: "probe", edgeId, value });
};
const readJson = async <T>(path: string, fallback: T): Promise<T> => existsSync(path) ? JSON.parse(await readFile(path, "utf8")) as T : fallback;
const payloads = <T>(inputs: graph.ParentView<TSchema, unknown>, edge: string): T[] => (inputs.messages.get(graph.EdgeId.create(edge)) ?? []) as unknown as T[];
const pause = async (signal?: AbortSignal) => {
  const { promise, resolve } = Promise.withResolvers<void>();
  const timer = setTimeout(resolve, PAUSE_MS);
  signal?.addEventListener("abort", () => { clearTimeout(timer); resolve(); }, { once: true });
  await promise;
};

export const Regress: syntax.DeterministicNode<Loop> = (c) => ({
  state: new graph.nodes.Deterministic<TSchema, unknown>(async function* (signal) {
    const p = c.context.paths;
    const counter = join(p.state, "iteration");
    c.context.iteration = existsSync(counter) ? Number(await readFile(counter, "utf8")) : 0;
    let inputs = yield [];
    while (true) {
      const [summary] = payloads<unknown>(inputs, "Publish~>Regress");
      if (summary !== undefined) log(`iteration ${c.context.iteration}: ${JSON.stringify(summary)}`);
      signal.throwIfAborted();
      c.context.iteration++;
      await writeFile(counter, String(c.context.iteration));
      let out: string;
      while (true) {
        const sha = c.context.sha = await prepare(p, signal);
        log(`iteration ${c.context.iteration}: origin/${BASE} ${sha}`);
        out = join(p.state, "baseline", sha);
        if (existsSync(join(out, CORPORA[0].name, "summary.json"))) { log(`Regress: baseline for ${sha} cached at ${out}`); break; }
        log(`Regress: building and running the corpora for ${sha}`);
        if (await regress(p, out, signal)) break;
        log(`Regress: origin/${BASE} ${sha} does not build (see ${join(out, "build.log")}); retrying in ${PAUSE_MS / 60_000} min`);
        await pause(signal);
        signal.throwIfAborted();
      }
      inputs = yield [graph.Message.create(c.edges.get("Regress~>Analytics") as Edge, { sha: c.context.sha, out } as unknown as TSchema)];
    }
  }, c.policy),
});

export const Analytics: syntax.DeterministicNode<Loop> = (c) => ({
  state: new graph.nodes.Deterministic<TSchema, unknown>(async function* (signal) {
    let inputs = yield [];
    while (true) {
      const [{ sha, out }] = payloads<{ sha: string; out: string }>(inputs, "Regress~>Analytics");
      const { paths: p, iteration } = c.context;
      const before = await analyze(p, out, sha, signal);
      const queueFile = join(p.state, "queue.json");
      const queue = refreshQueue(await readJson<Queue>(queueFile, { items: [] }), before);
      await writeFile(queueFile, JSON.stringify(queue, null, 2));
      const item = pickItem(queue);
      const m = metrics(before);
      probeAll(c, { ...m, queue_open: queue.items.filter((i) => i.status === "open").length, queue_pr: queue.items.filter((i) => i.status === "pr").length });
      await appendFile(join(p.state, "analytics.jsonl"), `${JSON.stringify({ at: new Date().toISOString(), iteration, phase: "before", sha, item: item?.id ?? null, ...m })}\n`);
      log(`Analytics: ${JSON.stringify(m)}; next item: ${item?.id ?? "none (queue empty)"}`);
      const toPublish = graph.Message.create(c.edges.get("Analytics~>Publish") as Edge, { before, item: item ?? null } as unknown as TSchema);
      if (!item) { inputs = yield [toPublish, graph.Message.create(c.edges.get("Analytics~>Verify") as Edge, { idle: true } as unknown as TSchema)]; continue; }
      const z3 = join(p.z3Install, "bin", "z3");
      const version = /Z3 version (\S+)/.exec(await must([z3, "-version"], { cwd: p.worktree, signal }))?.[1] ?? "unknown";
      const text = [
        `Work item ${item.id} [${item.kind}]: ${item.title}`, item.detail,
        `Cases (under ${p.corpus}): ${item.cases.slice(0, 10).join(", ")}${item.cases.length > 10 ? ` and ${item.cases.length - 10} more` : ""}`,
        item.notes.length ? `Earlier attempts on this item failed:\n${item.notes.map((n) => `- ${n}`).join("\n")}` : "This item has not been attempted before.",
        "", `Checkout (your cwd): ${p.worktree} at origin/${BASE} ${sha}. Build artifacts live outside it:`,
        `- F* cache: ${p.fstarCache}; Z3 built from this checkout: ${z3} (--z3version ${version}); F*: ${p.fstarExe}`,
        `- Native checker binary from the baseline build: ${p.checker} (rebuild before trusting it after your edits)`,
        `- Full rebuild (several minutes with warm caches): cd ${p.worktree} && eval "$(opam env --switch=${p.opamSwitch} --set-switch)" && pwsh -NoProfile -File fstar/tools/build_ocaml_checker.ps1 -FstarExe ${p.fstarExe} -Z3WindowsBuildDir ${p.z3Build} -Z3InstallDir ${p.z3Install} -CacheDir ${p.fstarCache} -WslBuildDir ${p.checkerDir} -OpamSwitch ${p.opamSwitch} -BuildJobs 32`,
        `- Baseline run logs (stdout/stderr per case, results.jsonl, diagnostics.json): ${out}`,
        "", "Baseline analytics:", analyticsMarkdown(before),
      ].join("\n");
      inputs = yield [toPublish, graph.Message.create(c.edges.get("Analytics~>Developer") as Edge, { kind: "prompt", text } as unknown as TSchema)];
    }
  }, c.policy),
});

const DEVELOPER_NODE = graph.NodeId.create("Developer"), ASSIGNMENT = graph.EdgeId.create("Analytics~>Developer"), REPORT = graph.EdgeId.create("Developer->Verify");

/**
 * One Developer session runs once per assignment: the `Developer->Developer` value edge re-arms the returned node and this
 * hook stages the queued assignment as its next prompt (the same mechanism as `schedules.ralph`).
 */
export const available: syntax.FromYamlOptions["available"] = {
  Developer: ({ graph: g }) => (view, triggered) => {
    const node = g.getNode(DEVELOPER_NODE);
    if (node === undefined) throw new Error("Developer node missing");
    if (node.status === "running") return true;
    if (!triggered || !(view.messages.get(ASSIGNMENT)?.length)) return false;
    const developer = node.state;
    if (!(developer instanceof agent.JuncoAgent)) throw new TypeError("Developer must be an agent node");
    if (developer.status === "idle") developer.stagePrompt((inputs) => payloads<{ text: string }>(inputs, "Analytics~>Developer")[0]!.text);
    return developer.status === "ready";
  },
};

export const Verify: syntax.DeterministicNode<Loop> = (c) => {
  /** The Developer report already verified: a value edge stays resolved, so a stale report must not re-trigger this node. */
  let consumed: unknown;
  return {
    state: new graph.nodes.Deterministic<TSchema, unknown>(async function* (signal) {
      let inputs = yield [];
      while (true) {
        const { paths: p, iteration, sha } = c.context;
        const out = join(p.state, "runs", String(iteration), "after");
        let after: Analysis | undefined, changed = "", report: { stopReason: string; text: string } | undefined;
        if (payloads(inputs, "Analytics~>Verify").length) log("Verify: idle cycle (queue empty)");
        else {
          const message = inputs.values.get(REPORT) as { stopReason: string; content: Parameters<typeof contentText>[0] } | undefined;
          consumed = message;
          if (message === undefined) throw new Error("Verify triggered without a Developer report");
          report = { stopReason: message.stopReason, text: message.stopReason === "stop" ? contentText(message.content).trim() : "" };
          changed = (await must(["git", "status", "--porcelain"], { cwd: p.worktree, signal })).trim();
          if (report.stopReason !== "stop") log(`Verify: Developer did not finish normally (${report.stopReason}); skipping the run`);
          else if (!changed) log("Verify: the Developer changed nothing; skipping the run");
          else {
            log(`Verify: rebuilding and re-running the corpora on the modified tree -> ${out}`);
            await regress(p, out, signal);
            after = await analyze(p, out, sha, signal);
            const m = metrics(after);
            probeAll(c, m);
            await appendFile(join(p.state, "analytics.jsonl"), `${JSON.stringify({ at: new Date().toISOString(), iteration, phase: "after", sha, ...m })}\n`);
            log(`Verify: ${JSON.stringify(m)}`);
          }
        }
        inputs = yield [graph.Message.create(c.edges.get("Verify~>Publish") as Edge, { after: after ?? null, changed: Boolean(changed), report: report ?? null } as unknown as TSchema)];
      }
    }, c.policy),
    is_available: (view, triggered) => triggered && (view.values.get(REPORT) !== consumed || (view.messages.get(graph.EdgeId.create("Analytics~>Verify"))?.length ?? 0) > 0),
  };
};

export const Publish: syntax.DeterministicNode<Loop> = (c) => ({
  state: new graph.nodes.Deterministic<TSchema, unknown>(async function* (signal) {
    let inputs = yield [];
    while (true) {
      const [{ before, item }] = payloads<{ before: Analysis; item: Item | null }>(inputs, "Analytics~>Publish");
      const [{ after, changed, report }] = payloads<{ after: Analysis | null; changed: boolean; report: { stopReason: string; text: string } | null }>(inputs, "Verify~>Publish");
      const { paths: p, iteration } = c.context;
      const next = (summary: unknown) => [graph.Message.create(c.edges.get("Publish~>Regress") as Edge, summary as TSchema)];
      if (!item) {
        log(`Publish: idle (queue empty); next cycle in ${PAUSE_MS / 60_000} min`);
        await pause(signal);
        inputs = yield next({ iteration, item: null });
        continue;
      }
      const text = report?.text ?? "";
      const title = /^Title:\s*(.+)$/m.exec(text)?.[1]?.trim() || item.title;
      const body = text.replace(/^Title:.*\n?/m, "").trim();
      const runDir = join(p.state, "runs", String(iteration));
      await mkdir(runDir, { recursive: true });
      const patch = join(runDir, "attempt.patch");
      if (changed) {
        // Keep the attempt: prepare() wipes the worktree, and a rejected attempt is the next try's starting point.
        await must(["git", "add", "-A"], { cwd: p.worktree, signal });
        await writeFile(patch, await must(["git", "diff", "--cached", "--binary"], { cwd: p.worktree, signal }));
      }
      const verdict = !changed ? { ok: false, reasons: [`the Developer left no changes (${report?.stopReason ?? "no report"})`] }
        : !after ? { ok: false, reasons: ["no verification run"] } : judge(item, before, after);
      const queueFile = join(p.state, "queue.json");
      const queue = await readJson<Queue>(queueFile, { items: [] });
      const entry = queue.items.find((i) => i.id === item.id) ?? item;
      let pr: string | undefined;
      if (verdict.ok) {
        const heads = await must(["git", "ls-remote", "--heads", "origin", "loop/junco-*"], { cwd: p.worktree, signal });
        const n = 1 + Math.max(0, ...[...heads.matchAll(/loop\/junco-(\d+)/g)].map((m) => Number(m[1])));
        const branch = `loop/junco-${n}`;
        const prBody = `${body}\n\n## Checker analytics (Z3-pulse-loop iteration ${iteration}, origin/${BASE} ${before.sha.slice(0, 9)})\n\nWork item: ${item.id}. Judge: ${verdict.reasons.join("; ")}.\n\n${analyticsMarkdown(before, after!)}\n`;
        await writeFile(join(runDir, "pr.md"), `# ${title}\n\n${prBody}`);
        await must(["git", "checkout", "-q", "-B", branch], { cwd: p.worktree, signal });
        await must(["git", "commit", "-q", "-m", title, "-m", `Z3-pulse-loop iteration ${iteration}; work item ${item.id}.`], { cwd: p.worktree, signal });
        if ((await must(["gh", "api", "user", "--jq", ".login"], { cwd: p.worktree, signal })).trim() !== PR_USER)
          throw new Error(`Publication requires an active ${PR_USER} login`);
        await must(["git", "-c", "credential.helper=", "-c", "credential.https://github.com.helper=!gh auth git-credential", "push", "-q", "-u", "origin", `${branch}:refs/heads/${branch}`], { cwd: p.worktree, signal });
        pr = (await must(["gh", "pr", "create", "-R", PR_REPO, "--base", BASE, "--head", branch, "--title", title, "--body-file", join(runDir, "pr.md")], { cwd: p.worktree, signal })).trim();
        Object.assign(entry, { status: "pr", pr, attempts: entry.attempts + 1 });
        log(`Publish: opened ${pr}`);
      } else {
        entry.attempts++;
        entry.notes.push(`iteration ${iteration}: ${verdict.reasons.join("; ")}${changed ? `. Patch of that attempt (apply with \`git apply ${patch}\` if it is a good starting point): ${patch}` : ""}${text ? `. Developer report: ${text.slice(0, 600).replace(/\s+/g, " ")}` : ""}`);
        log(`Publish: no PR for ${item.id}: ${verdict.reasons.join("; ")}`);
      }
      if (!queue.items.includes(entry)) queue.items.push(entry);
      await writeFile(queueFile, JSON.stringify(queue, null, 2));
      probeAll(c, { pr_opened: pr ? 1 : 0 });
      inputs = yield next({ iteration, item: item.id, title, ok: verdict.ok, reasons: verdict.reasons, pr: pr ?? null });
    }
  }, c.policy),
});

/** Reset the loop's worktree (a btrfs subvolume under the state dir) to origin/master and return its SHA; clone the corpus on first use. */
async function prepare(p: Paths, signal?: AbortSignal): Promise<string> {
  await mkdir(p.state, { recursive: true });
  if (!existsSync(p.corpus)) await must(["git", "clone", "-q", "--depth", "1", "https://github.com/Z3Prover/z3test", p.corpus], { cwd: p.state, signal });
  await must(["git", "fetch", "-q", "origin"], { cwd: p.repo, signal });
  if (!existsSync(p.worktree)) await must(["btrfs", "subvolume", "create", p.worktree], { cwd: p.state, signal });
  if (!existsSync(join(p.worktree, ".git"))) await must(["git", "worktree", "add", "--detach", p.worktree, `origin/${BASE}`], { cwd: p.repo, signal });
  await must(["git", "checkout", "-q", "--detach", `origin/${BASE}`], { cwd: p.worktree, signal });
  await must(["git", "reset", "-q", "--hard"], { cwd: p.worktree, signal });
  await must(["git", "clean", "-fdq"], { cwd: p.worktree, signal });
  return (await must(["git", "rev-parse", "HEAD"], { cwd: p.worktree, signal })).trim();
}

if (import.meta.main) {
  const controller = new AbortController();
  for (const name of ["SIGINT", "SIGTERM"] as const) process.once(name, () => controller.abort(new Error(`Z3-pulse-loop interrupted by ${name}`)));
  const { signal } = controller;
  const p = paths();
  const models = await ModelRuntime.create({ allowModelNetwork: true, refreshOnCreate: false, signal });
  const refreshed = await models.refresh({ allowNetwork: true, signal });
  if (refreshed.aborted || refreshed.errors.size) throw new Error(`model catalog refresh failed: ${[...refreshed.errors].map(([k, e]) => `${k}: ${e.message}`).join("; ") || "aborted"}`);
  if (!(await models.listCredentials({ signal })).some(({ providerId }) => providerId === "github-copilot")) throw new Error("A saved github-copilot Pi login is required");
  const opik = new Opik({ apiUrl: process.env.OPIK_URL_OVERRIDE ?? "http://localhost:5173/api", projectName: process.env.OPIK_PROJECT_NAME ?? "Z3-pulse-loop" });
  const recorder = await tracer.GrafanaRecorder.create({ url: process.env.GRAFANA_URL ?? "http://localhost:8000", dashboard: "Z3-pulse-loop" });
  log(`grafana: ${recorder.dashboardUrl}`);
  try {
    // prepare() runs inside Regress each cycle; the worktree must exist before the tool collection opens on it.
    await prepare(p, signal);
    const collection = await openCollection(p);
    try {
      const execution = await JuncoGraph.fromYaml(document, {
        cwd: p.worktree, scheduler: () => schedules.parallel(), ladder: new schedules.ModelLadder(models, ladder), collection, signal, recorder, available,
        tracer: new OpikTracer(opik, `Z3-pulse-loop ${new Date().toISOString()}`), code: { Regress, Analytics, Verify, Publish }, context: { iteration: 0, sha: "", paths: p } satisfies Loop,
      });
      try {
        // Never resolves: the graph cycles until a node fails or the signal aborts. A failure may have poisoned the
        // native tool runtime (observed: tokio worker panics after a thread-spawn EAGAIN), so exit and let `bun run loop` restart.
        await execution.run();
      } finally {
        await execution.graph.close();
      }
    } finally {
      await collection.close();
    }
  } catch (error) {
    if (!signal.aborted) {
      const describe = (e: unknown): string => e instanceof Error ? `${e.stack ?? e.message}${e.cause === undefined ? "" : `\n  caused by: ${describe(e.cause)}`}` : String(e);
      log(`failed: ${describe(error)}`);
      process.exitCode = 1;
    }
  } finally {
    await recorder.close();
    await opik.flush();
  }
  log("stopped");
}

import { createHash } from "node:crypto";
import { closeSync, openSync } from "node:fs";
import { lstat, mkdir, mkdtemp, readFile, readdir, realpath, rename, writeFile } from "node:fs/promises";
import { cpus, homedir } from "node:os";
import { join, resolve } from "node:path";
import type { Paths } from "./state.ts";

const PIN = "b188ff772b94fd5ac51ca97efffdd368e64df151";
const CORPUS_PIN = "91c60596fd6a43de189a1ccba8080a3b48797537";
const MANIFEST = "ea0349ec8af0fe55353ade9258e82c6c0ef8198b9d487c0cf306de4556c7483e";
const HARNESS = "fstar/tools/run_checker_regressions.py", BUILD = "fstar/tools/build_ocaml_checker.ps1";
const HARNESS_HASH = "28c23a82d911a98354aee6a7a6b0524637113c415bec1aa50c36f570a51a6a4a";
export const CORPORA = [
  { name: "proofs", path: "regressions/proofs", total: 1800, memory: 2048, manifest: false, size: 17 },
  { name: "smtlib-sample", path: "regressions/smtlib-sample", total: 3600, memory: 4096, manifest: true, size: 225 },
] as const;
const ERRORS = new Set(["ERROR", "CRASH", "PROTOCOL_ERROR"]);
const SOLVER_BUDGET_MS = 10_000, CASE_BUDGET_S = 60;
const atBudget = (b: CaseStat) => b.wall >= 0.8 * CASE_BUDGET_S || (b.solveMs ?? 0) >= 0.8 * SOLVER_BUDGET_MS;
const KIND_RANK = { crash: 0, reject: 1, obligation: 2, timeout: 3, slow: 4 } as const;
const familyId = (rule: string, shape: string) => `obligation:${rule}|${shape}`;
export type CaseStat = { outcome: string; wall: number; solveMs?: number; checkMs?: number; proofNodes?: number; pending?: number; stage?: string };
export type Family = { rule: string; shape: string; pending: number; cases: { path: string; count: number; first: string }[] };
export type Analysis = {
  sha: string; tree: string; evaluator: string; buildOk: boolean; ciPass: boolean; statsCases: number; tested: number; counts: Record<string, number>;
  pending: number; proofNodes: number; checkMs: number; solveMs: number; families: Family[]; cases: Record<string, CaseStat>; lemmas: number; assumed: number;
};
export type Item = { id: string; kind: keyof typeof KIND_RANK; title: string; detail: string; cases: string[]; weight: number; attempts: number; status: "open"; notes: string[] };
export type Queue = { items: Item[] };
type Result = { code: number; stdout: string; stderr: string };
export type Run = (cmd: string[], o: { cwd: string; log?: string; env?: Record<string, string>; signal?: AbortSignal; timeoutMs?: number }) => Promise<Result>;
const PATH = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin";
const env = () => ({ PATH, HOME: homedir(), LC_ALL: "C", OPAMROOT: process.env.OPAMROOT ?? join(homedir(), ".opam"), GIT_CONFIG_NOSYSTEM: "1", GIT_CONFIG_GLOBAL: "/dev/null", GIT_NO_REPLACE_OBJECTS: "1", GIT_TERMINAL_PROMPT: "0" });
export const sh: Run = async (cmd, o) => {
  o.signal?.throwIfAborted();
  const fd = o.log === undefined ? undefined : openSync(o.log, "wx", 0o600);
  try {
    const child = Bun.spawn(cmd, { cwd: o.cwd, detached: true, stdin: "ignore", stdout: fd ?? "pipe", stderr: fd ?? "pipe", env: { ...env(), ...o.env } });
    const kill = () => { try { process.kill(-child.pid, "SIGKILL"); } catch (e) { if ((e as NodeJS.ErrnoException).code !== "ESRCH") throw e; } };
    o.signal?.addEventListener("abort", kill, { once: true });
    if (o.signal?.aborted) kill();
    const timer = o.timeoutMs === undefined ? undefined : setTimeout(kill, o.timeoutMs);
    try {
      const [code, stdout, stderr] = await Promise.all([child.exited, fd === undefined ? new Response(child.stdout as ReadableStream).text() : "", fd === undefined ? new Response(child.stderr as ReadableStream).text() : ""]);
      o.signal?.throwIfAborted();
      return { code, stdout, stderr };
    } finally { clearTimeout(timer); o.signal?.removeEventListener("abort", kill); }
  } finally { if (fd !== undefined) closeSync(fd); }
};
export async function must(cmd: string[], o: Parameters<Run>[1]) {
  const r = await sh(cmd, o);
  if (r.code !== 0) throw new Error(`${cmd.join(" ")} failed (${r.code}): ${r.stderr.trim() || r.stdout.trim()}`);
  return r.stdout;
}
const git = (cwd: string, ...args: string[]) => must(["/usr/bin/git", "--no-optional-locks", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false", ...args], { cwd });
const nul = (s: string) => s === "" ? [] : s.slice(0, -1).split("\0");
const hash = (b: Buffer | string) => createHash("sha256").update(b).digest("hex");
const fileHash = async (path: string) => hash(await readFile(path));
function requireThat(ok: unknown, message: string): asserts ok { if (!ok) throw new Error(message); }
const json = async (path: string) => JSON.parse(await readFile(path, "utf8"));
const save = (path: string, obj: unknown) => writeFile(path, JSON.stringify(obj, null, 2) + "\n", { flag: "wx", mode: 0o600 });
const exists = async (path: string) => lstat(path).then(() => true, (e: NodeJS.ErrnoException) => { if (e.code !== "ENOENT") throw e; return false; });
const regular = async (path: string) => requireThat((await lstat(path)).isFile() && await realpath(path) === resolve(path), `not a regular non-symlink file: ${path}`);
const cleanCmd = (cmd: string[], extra: Record<string, string> = {}) => ["/usr/bin/env", "-i", ...Object.entries({ ...env(), ...extra }).map(([k,v]) => `${k}=${v}`), ...cmd];
const opam = (p: Paths, ...cmd: string[]) => ["/usr/bin/opam", "exec", `--switch=${p.opamSwitch}`, "--", ...cmd];
const jobs = () => Math.min(64, cpus().length);
const expectedPaths = (actual: string[], wanted: string[]) => requireThat(Array.isArray(actual) && new Set(actual).size === wanted.length && actual.length === wanted.length && actual.every((path, i) => wanted[i] === path), "missing, repeated or out-of-order corpus case");

// Compare the PowerShell program outside the three literal arrays byte-for-byte. Inside,
// only insert quoted names of real new verified modules; never interpret PowerShell here.
const listNames = ["modules", "testModules", "order"] as const;
function moduleLists(script: string) {
  const lists = {} as Record<typeof listNames[number], string[]>;
  for (const name of listNames) {
    const pattern = new RegExp(`^( +\\$${name} = @\\()(.*?)(^ +\\))`, "ms");
    const m = pattern.exec(script);
    requireThat(m && /^\s*"[A-Za-z_][A-Za-z0-9_]*\.(?:fst|fsti|ml)"(?:\s*,\s*"[A-Za-z_][A-Za-z0-9_]*\.(?:fst|fsti|ml)")*\s*$/.test(m[2]!), `invalid build ${name} literals`);
    lists[name] = [...m[2]!.matchAll(/"([^"]+)"/g)].map(m => m[1]!);
    requireThat(new Set(lists[name]).size === lists[name].length, `duplicate build ${name}`);
    script = script.slice(0, m.index) + m[1] + "\n" + m[3] + script.slice(m.index + m[0].length);
  }
  return { script, lists };
}
function validateBuildScript(before: string, after: string, addedFiles: Set<string>) {
  const a = moduleLists(before), b = moduleLists(after);
  requireThat(a.script === b.script, "protected build command or flag changed");
  const added = {} as Record<typeof listNames[number], string[]>;
  for (const key of listNames) {
    const original = new Set(a.lists[key]);
    requireThat(b.lists[key].filter(x => original.has(x)).join() === a.lists[key].join(), `protected build ${key} removed/reordered`);
    added[key] = b.lists[key].filter(x => !original.has(x));
  }
  for (const name of [...added.modules, ...added.testModules]) requireThat(/^Z3[A-Za-z0-9_]+\.fst$/.test(name) && addedFiles.has(`fstar/${name}`), `unverified new build module: ${name}`);
  requireThat(!b.lists.modules.some(x => b.lists.testModules.includes(x)), "test module also appears in production list");
  requireThat(JSON.stringify(added.modules.map(n => n.replace(/\.fst$/, ".ml")).sort()) === JSON.stringify([...added.order].sort()), "new linked objects must match the new verified modules exactly");
  return b.lists;
}
const lsTree = async (cwd: string, rev: string, ...paths: string[]) => new Map(nul(await git(cwd, "ls-tree", "-rz", rev, "--", ...paths)).map(entry => {
  const i = entry.indexOf("\t"); return [entry.slice(i + 1), entry.slice(0, i)] as const;
}));
const protectedTest = (path: string) => /^fstar\/Z3\w*Tests\.fst$/.test(path) || path === "fstar/tools/test_native_bridge.ml";
const guardedPath = (path: string) => /^fstar\/(?:tools\/|ocaml_runtime\/)/.test(path) || protectedTest(path) || path.endsWith(".fsti");
const blob = (cwd: string, rev: string, path: string) => git(cwd, "cat-file", "blob", `${rev}:${path}`);
const unsafeLine = /\b(?:admit(?:1|_t)?|assume|admitted|magic|unsafe_coerce|unchecked_cast|unsafe_cast|believe_me|Obj\.magic|admit_lemma|expect_failure)\b|--(?:lax|admit|already_cached|load|unsafe|no_check|verify_module|warn_error)(?:\b|_)/i;
function appendedTest(file: string, original: string, candidate: string) {
  // A prefix alone permits continuing the last assertion with a weaker expression.
  const suffix = candidate.slice(original.length);
  return candidate.startsWith(original) && (file.endsWith(".ml") ? /^\s*;;\s+let\b/.test(suffix) : /^\s*\nlet\s+\w/.test(suffix));
}

async function checkProtected(p: Paths, root: string, tree: string, base: string) {
  const pinned = await lsTree(p.repo, PIN, "fstar"), candidate = await lsTree(root, tree, "fstar"), prior = await lsTree(root, base, "fstar");
  const script = await blob(root, tree, BUILD);
  const lists = validateBuildScript(await blob(p.repo, PIN, BUILD), script, new Set([...candidate.keys()].filter(n => !pinned.has(n))));
  validateBuildScript(await blob(root, base, BUILD), script, new Set([...candidate.keys()].filter(n => !prior.has(n))));
  for (const name of candidate.keys()) {
    if (!pinned.has(name) && /^fstar\/(?:tools|ocaml_runtime)\//.test(name)) throw new Error(`unverified evaluator/runtime file: ${name}`);
  }
  for (const mod of [...lists.modules,...lists.testModules]) {
    if (!pinned.has(`fstar/${mod}`)) requireThat(!candidate.has(`fstar/ocaml_runtime/${mod.replace(/\.fst$/, ".ml")}`), `verified module shadows a foreign implementation: ${mod}`);
  }
  for (const [file, entry] of pinned) {
    if (file === BUILD || !guardedPath(file) || candidate.get(file) === entry) continue;
    requireThat(protectedTest(file) && candidate.get(file)?.startsWith("100644 blob ") && appendedTest(file, await blob(p.repo, PIN, file), await blob(root, tree, file)), `pinned evaluator or original test changed: ${file}`);
  }
  return lists;
}
export async function validatePatch(p: Paths, base: string, verifiedCheckout: string): Promise<void> {
  const root = verifiedCheckout;
  requireThat(/^[0-9a-f]{40}$/.test(base) && (await git(root, "rev-parse", "HEAD")).trim() === base, "wrong captured base");
  await git(root, "diff", "--quiet", "--no-ext-diff", "--no-textconv", "--");
  requireThat(!(await git(root, "ls-files", "--others", "-z")), "unexpected unstaged/ignored file in captured checkout");
  const tree = (await git(root, "write-tree")).trim(), lists = await checkProtected(p, root, tree, base);
  const entries = nul(await git(root, "diff-tree", "-r", "--no-renames", "--raw", "-z", base, tree));
  for (let i = 0; i < entries.length; i += 2) {
    const [oldMode, newMode,,,status] = entries[i]!.slice(1).split(" "), file = entries[i+1]!;
    requireThat((status === "A" || status === "M") && newMode === "100644" && (status === "A" || newMode === oldMode), `forbidden file removal/mode: ${file}`);
    if (file === BUILD) continue;
    if (/^src\/(?!test\/)[\w./-]+\.(?:cpp|h)$/.test(file)) continue;
    if (protectedTest(file) && status === "M") {
      requireThat((file.endsWith(".ml") || lists.testModules.includes(file.slice(6))) && appendedTest(file, await blob(root, base, file), await blob(root, tree, file)), `original assertions must remain intact: ${file}`);
    } else {
      const module = file.slice("fstar/".length);
      requireThat(/^fstar\/Z3[A-Za-z0-9_]+\.fst$/.test(file) && [...lists.modules, ...lists.testModules].includes(module), `protected evaluator or non-verified source: ${file}`);
    }
    const diff = await git(root, "diff", "--no-ext-diff", "--no-textconv", "-U0", base, tree, "--", file);
    for (const line of diff.split("\n")) if (line.startsWith("+") && !line.startsWith("+++")) requireThat(!unsafeLine.test(line), `new unsafe proof marker or flag in ${file}: ${line}`);
  }
}

type CorpusInput = { paths: string[]; sha256: Record<string,string> };
type Inputs = { sha: string; tree: string; evaluator: string; harness: string; corpora: CorpusInput[]; identity: object };
export class EvaluationConfigError extends Error {}
function configurationFailure(error: unknown): never {
  if (error instanceof EvaluationConfigError) throw error;
  throw new EvaluationConfigError(error instanceof Error ? error.message : String(error), { cause: error });
}
function requireConfig(ok: unknown, message: string): asserts ok {
  if (!ok) throw new EvaluationConfigError(message);
}
function inputs(p: Paths, signal?: AbortSignal): Promise<Inputs> {
  return readInputs(p, signal).catch(error => { signal?.throwIfAborted(); return configurationFailure(error); });
}
async function readInputs(p: Paths, signal?: AbortSignal): Promise<Inputs> {
  signal?.throwIfAborted();
  requireThat(p.maxCases === 0, "complete Pulse CI evaluation requires --max-cases 0");
  requireThat(/^[A-Za-z0-9_.-]+$/.test(p.opamSwitch), "invalid opam switch name");
  requireThat(await realpath(p.corpus) === resolve(p.corpus) && (await git(p.corpus, "rev-parse", "HEAD")).trim() === CORPUS_PIN && !(await git(p.corpus, "status", "--porcelain", "--untracked-files=all")), "corpus must be the clean pinned z3test checkout");
  const sha = (await git(p.worktree, "rev-parse", "HEAD")).trim(), tree = (await git(p.worktree, "write-tree")).trim();
  await git(p.worktree, "diff", "--quiet", "--no-ext-diff", "--no-textconv", "--");
  requireThat(!(await git(p.worktree, "ls-files", "--others", "--exclude-standard", "-z")), "source has untracked build inputs");
  const harness = await blob(p.repo, PIN, HARNESS);
  requireThat(hash(harness) === HARNESS_HASH, "protected regression harness digest mismatch");
  const manifestFile = join(p.corpus, CORPORA[1].path, "manifest.json");
  await regular(manifestFile);
  const manifestBytes = await readFile(manifestFile);
  requireThat(hash(manifestBytes) === MANIFEST, "pinned manifest digest mismatch");
  const manifest = JSON.parse(manifestBytes.toString()) as { cases: { path: string; sha256: string }[] };
  const corpora: CorpusInput[] = [];
  for (const c of CORPORA) {
    const files = await lsTree(p.corpus, CORPUS_PIN, c.path);
    // pathlib compares POSIX path components, not slash-delimited strings.
    const paths = [...files.keys()].filter(n => n.endsWith(".smt2")).sort((a,b) => { const x = a.split("/"), y = b.split("/"); for (let i=0; i<Math.min(x.length,y.length); i++) if (x[i] !== y[i]) return x[i]! < y[i]! ? -1 : 1; return x.length - y.length; });
    requireThat(paths.length === c.size, `wrong pinned ${c.name} case count`);
    const sha256: Record<string,string> = {};
    for (const name of paths) {
      const path = join(p.corpus, name); await regular(path);
      const bytes = await readFile(path);
      const object = createHash("sha1").update(`blob ${bytes.length}\0`).update(bytes).digest("hex");
      requireThat(files.get(name) === `100644 blob ${object}`, `wrong pinned corpus input: ${name}`);
      sha256[name] = hash(bytes);
    }
    if (c.manifest) {
      requireThat(manifest.cases.length === paths.length && new Set(manifest.cases.map(e => e.path)).size === paths.length, "wrong manifest membership");
      for (const e of manifest.cases) requireThat(sha256[`${c.path}/${e.path}`] === e.sha256, `manifest input mismatch: ${e.path}`);
    }
    corpora.push({ paths, sha256 });
  }
  const cwd = p.state;
  // Hash actual selected binaries and Zarith objects, not mtimes or merely tool names.
  const toolchain = await must(opam(p, "/bin/sh", "-ec", 'for n in ocamlc ocamlopt ocamlfind cc c++ cmake make pwsh python3 opam; do sha256sum "$(command -v "$n")"; done; d=$(ocamlfind query zarith); sha256sum "$d/zarith.a" "$d/zarith.cmxa"; test "$(ocamlc -version)" = 5.3.0; opam list --installed --short --columns=name,version --color=never'), { cwd, signal });
  const fstar = await must([p.fstarExe, "--version"], { cwd, signal });
  requireThat(/^F\* 2026\.09\.27$/m.test(fstar) && /^commit=7deb38a27c86990664c6b41e4b6093597acdebd4$/m.test(fstar), "wrong pinned F* compiler");
  const identity = {
    protectedCommit: PIN, harnessSha256: HARNESS_HASH, evaluationSha256: await fileHash(import.meta.path),
    corpusCommit: CORPUS_PIN, manifestSha256: MANIFEST, suites: CORPORA, corpora, maxCases: p.maxCases,
    solverTimeoutMs: SOLVER_BUDGET_MS, caseTimeoutS: CASE_BUDGET_S, buildJobs: jobs(),
    fstar, fstarSha256: await fileHash(p.fstarExe), opamSwitch: p.opamSwitch, toolchain,
  };
  return { sha, tree, evaluator: hash(JSON.stringify(identity)), harness, corpora, identity };
}

async function execute(p: Paths, out: string, input: Inputs, signal: AbortSignal | undefined, run: Run) {
  await mkdir(out, { recursive: true, mode: 0o700 });
  requireThat(!(await readdir(out)).length && await realpath(out) === resolve(out), `refusing nonempty or aliased evidence directory: ${out}`);
  await checkProtected(p, p.worktree, input.tree, input.sha).catch(configurationFailure);
  const start = Date.now(), harness = join(out, "run_checker_regressions.py");
  await writeFile(harness, input.harness, { flag: "wx", mode: 0o400 });
  await save(join(out, "evaluator.json"), input.identity);
  const build = await run(cleanCmd(opam(p, "pwsh", "-NoProfile", "-File", BUILD, "-FstarExe", p.fstarExe,
    "-Z3WindowsBuildDir", p.z3Build, "-Z3InstallDir", p.z3Install, "-CacheDir", p.fstarCache, "-WslBuildDir", p.checkerDir,
    "-OpamSwitch", p.opamSwitch, "-BuildJobs", String(jobs()), "-RunTests")), { cwd: p.worktree, log: join(out, "build.log"), signal });
  signal?.throwIfAborted();
  requireThat(Number.isInteger(build.code) && build.code >= 0 && build.code < 128, `build was interrupted: ${build.code}`);
  const metadata = { sha: input.sha, tree: input.tree, evaluator: input.evaluator, wall_seconds: (Date.now() - start) / 1000, exit_code: build.code, fstar_exe: p.fstarExe };
  if (build.code !== 0) { await save(join(out, "build.json"), metadata); return false; }
  const checker_version = (await must([p.checker, "--version"], { cwd: out, signal })).trim();
  requireThat(checker_version.length > 0, "built checker has no producer version");
  await save(join(out, "build.json"), { ...metadata, checker_version, checker_sha256: await fileHash(p.checker), z3_sha256: await fileHash(join(p.z3Install, "bin/z3")) });
  for (const c of CORPORA) {
    const dir = join(out, c.name);
    const manifest = c.manifest ? ["--manifest", join(p.corpus, c.path, "manifest.json")] : [];
    const r = await run(cleanCmd(["python3", "-I", "-B", harness, "run", "--checker", p.checker, "--corpus", p.corpus, "--corpus-path", c.path,
      "--corpus-commit", CORPUS_PIN, "--max-cases", "0", "--expected-cases", String(c.size), "--solver-timeout-ms", String(SOLVER_BUDGET_MS),
      "--case-timeout-seconds", String(CASE_BUDGET_S), "--total-timeout-seconds", String(c.total), "--memory-limit-mb", String(c.memory),
      ...manifest, "--output", dir], { GITHUB_SHA: input.sha }), { cwd: out, log: join(out, `${c.name}.log`), signal });
    signal?.throwIfAborted();
    await save(join(out, `${c.name}.exit.json`), { exit_code: r.code });
    const report = await sh(["python3", "-I", "-B", harness, "report", "--output", dir], {
      cwd: out, log: join(out, `${c.name}.report.log`), signal, env: { BUILD_OUTCOME: "success", CORPUS_OUTCOME: "success", RUNNER_OUTCOME: r.code === 0 ? "success" : "failure" },
    });
    requireThat(report.code === 0, `regression report failed for ${c.name} (${report.code}); see ${dir}`);
  }
  return true;
}

export async function regress(p: Paths, out: string, signal?: AbortSignal, run: Run = sh): Promise<boolean> {
  return execute(p, out, await inputs(p, signal), signal, run);
}

type Diagnostic = { stage?: string; families: [string, string, number, string][] };
function parseDiagnostic(verdict: string, r: Result): Diagnostic {
  const partial = /^PARTIAL ([1-9]\d*)$/.exec(verdict);
  requireThat((partial || verdict === "REJECT") && r.code === (partial ? 3 : 1) && r.stdout.trim() === verdict, `diagnostic disagrees with ${verdict}: code ${r.code}, stdout ${r.stdout.trim()}`);
  const lines = r.stderr.split(/\r?\n/);
  const headers = lines.filter(l => l.startsWith("diagnostic\t")), rows = lines.filter(l => l.startsWith("obligation\t"));
  requireThat(headers.length === 1, `missing/repeated diagnostic header: ${verdict}`);
  if (!partial) {
    const m = /^diagnostic\trejected\t(stage=[^\s]+)\t(index=(?:-|\d+))(?:\t([^\t]+))?$/.exec(headers[0]!);
    requireThat(m && rows.length === 0, "incomplete rejected diagnostic");
    return { stage: m.slice(1).filter(Boolean).join(" "), families: [] };
  }
  const m = /^diagnostic\tchecked\tpending=([1-9]\d*)\tfamilies=([1-9]\d*)$/.exec(headers[0]!);
  requireThat(m && m[1] === partial[1] && Number(m[2]) === rows.length, `incomplete diagnostic header/families: ${verdict}`);
  const families: Diagnostic["families"] = [], seen = new Set<string>();
  let sum = 0;
  for (const row of rows) {
    const f = /^obligation\t([^\t]+)\t([1-9]\d*)\t(\d+)\t([^\t]+)$/.exec(row);
    requireThat(f, `malformed obligation: ${row}`);
    const key = JSON.stringify([f[1],f[4]]), count = Number(f[2]);
    requireThat(!seen.has(key) && Number.isSafeInteger(count), `invalid or repeated obligation: ${row}`);
    seen.add(key); sum += count; families.push([f[1]!, f[4]!, count, f[3]!]);
  }
  requireThat(Number.isSafeInteger(sum) && sum === Number(partial[1]), `incomplete diagnostic sum: ${sum} for ${verdict}`);
  return { families };
}

const STATS = /solve_ms=([\d.]+) marshal_ms=([\d.]+) check_ms=([\d.]+) expressions=\d+ declarations=\d+ proof_nodes=(\d+)/;
const VERDICTS: Record<number, [string, RegExp]> = { 0: ["ACCEPT", /^ACCEPT$/], 1: ["REJECT", /^REJECT$/], 3: ["PARTIAL", /^PARTIAL [1-9]\d*$/], 4: ["SAT", /^SAT$/], 5: ["UNKNOWN", /^UNKNOWN .+$/] };
function retainedOutcome(code: number | null, text: string) {
  if (code === null) return "TIMEOUT";
  requireThat(Number.isInteger(code), "missing case return code");
  if (code === 2) return "ERROR";
  const v = VERDICTS[code];
  return v ? v[1].test(text) ? v[0] : "PROTOCOL_ERROR" : "CRASH";
}

async function inspect(p: Paths, out: string, input: Inputs, signal?: AbortSignal): Promise<Analysis> {
  const build = await json(join(out, "build.json"));
  requireConfig(hash(JSON.stringify(await json(join(out, "evaluator.json")))) === input.evaluator, "wrong retained evaluator/toolchain inputs");
  requireConfig(build.sha === input.sha && build.tree === input.tree && build.evaluator === input.evaluator && Number.isInteger(build.exit_code), "stale build/evaluator identity");
  await regular(join(out, "build.log"));
  requireConfig(await fileHash(join(out, "run_checker_regressions.py")) === HARNESS_HASH, "retained protected harness changed");
  const a: Analysis = { sha: input.sha, tree: input.tree, evaluator: input.evaluator, buildOk: build.exit_code === 0, ciPass: build.exit_code === 0, statsCases: 0, tested: 0, counts: {}, pending: 0, proofNodes: 0, checkMs: 0, solveMs: 0, families: [], cases: {}, lemmas: 0, assumed: 0 };
  if (!a.buildOk) return a;
  requireConfig(build.checker_sha256 === await fileHash(p.checker) && build.z3_sha256 === await fileHash(join(p.z3Install, "bin/z3")), "built checker or checkout solver changed");
  const need: { path: string; verdict: string; memory: number }[] = [];
  for (const [n,c] of CORPORA.entries()) {
    const dir = join(out, c.name), pinned = input.corpora[n]!;
    const selected = await json(join(dir, "selection.json")), summary = await json(join(dir, "summary.json"));
    const code = (await json(join(out, `${c.name}.exit.json`))).exit_code;
    requireThat(selected.corpus_path === c.path && selected.corpus_commit === CORPUS_PIN && selected.z3_commit === input.sha && selected.checker_version === build.checker_version &&
      selected.solver_timeout_ms === SOLVER_BUDGET_MS && selected.case_timeout_seconds === CASE_BUDGET_S && selected.total_timeout_seconds === c.total && selected.memory_limit_mb === c.memory &&
      selected.discovered === c.size && JSON.stringify(summary.selection) === JSON.stringify(selected), `wrong revision, selection or budget: ${dir}`);
    expectedPaths(selected.paths, pinned.paths);
    if (c.manifest) requireThat(selected.manifest?.sha256 === MANIFEST && await fileHash(join(dir, "input-manifest.json")) === MANIFEST, "wrong recorded corpus manifest");
    requireThat(summary.selected === c.size && summary.tested === c.size && Array.isArray(summary.warnings) && !summary.warnings.length &&
      summary.build_outcome === "success" && summary.runner_outcome === (code === 0 ? "success" : "failure"), `incomplete report at ${dir}: ${JSON.stringify(summary.warnings)}`);
    const raw = await readFile(join(dir, "results.jsonl"), "utf8");
    requireThat(raw.endsWith("\n"), `truncated results at ${dir}`);
    const rows = raw.slice(0,-1).split("\n").map(l => JSON.parse(l));
    expectedPaths(rows.map(r => r.path), pinned.paths);
    const counts: Record<string,number> = {};
    for (const [i,r] of rows.entries()) {
      signal?.throwIfAborted();
      const path = pinned.paths[i]!, stem = `logs/${String(i).padStart(6, "0")}`;
      requireThat(r.stdout === `${stem}.stdout` && r.stderr === `${stem}.stderr` && Number.isFinite(r.wall_seconds) && r.wall_seconds >= 0, `missing per-case logs/timing: ${path}`);
      if (c.manifest) requireThat(r.input_sha256 === pinned.sha256[path] && selected.input_sha256?.[path] === pinned.sha256[path], `case digest mismatch: ${path}`);
      const stdoutPath = join(dir, r.stdout), stderrPath = join(dir, r.stderr);
      await regular(stdoutPath); await regular(stderrPath);
      const stdout = (await readFile(stdoutPath, "utf8")).trim(), stderr = await readFile(stderrPath, "utf8");
      requireThat(r.verdict === stdout && r.outcome === retainedOutcome(r.returncode, stdout), `truncated/invalid case verdict: ${path}`);
      const stat: CaseStat = { outcome: r.outcome, wall: r.wall_seconds };
      const stats = stderr.split("\n").filter(line => line.startsWith("solve_ms="));
      requireThat(stats.length <= 1, `ambiguous timing: ${path}`);
      if (stats.length) {
        const m = STATS.exec(stats[0]!);
        requireThat(m && / semantics=(?:legacy|sorted-datatype)$/.test(stats[0]!) && m.slice(1).every(v => Number.isFinite(Number(v))), `truncated phase statistics: ${path}`);
        stat.solveMs = Number(m[1]); stat.checkMs = Number(m[3]); stat.proofNodes = Number(m[4]);
        a.solveMs += stat.solveMs; a.checkMs += stat.checkMs; a.proofNodes += stat.proofNodes; a.statsCases++;
      } else requireThat(!["ACCEPT","REJECT","PARTIAL"].includes(r.outcome), `completed proof missing checker --stats stderr: ${path}`);
      a.cases[path] = stat; a.tested++; counts[r.outcome] = (counts[r.outcome] ?? 0) + 1; a.counts[r.outcome] = (a.counts[r.outcome] ?? 0) + 1;
      if (r.outcome === "PARTIAL" || r.outcome === "REJECT") need.push({ path, verdict: stdout, memory: c.memory });
    }
    for (const outcome of new Set([...Object.keys(summary.counts), ...Object.keys(counts)])) requireThat(summary.counts[outcome] === (counts[outcome] ?? 0), `inconsistent ${outcome} count: ${dir}`);
    requireThat(code === Number(Object.keys(counts).some(k => ERRORS.has(k))), `runner failed independently of recorded formula outcomes: ${dir} (${code})`);
    if (code !== 0) a.ciPass = false;
  }
  const diagPath = join(out, "diagnostics.json"), cached = await exists(diagPath);
  const diagnostics: Record<string, Result> = cached ? await json(diagPath) : {};
  if (!cached) {
    // Keep raw stderr/return codes even when a replay disagrees; never cache a partial scan.
    let next = 0;
    const stop = new AbortController(), childSignal = signal ? AbortSignal.any([signal, stop.signal]) : stop.signal;
    const workers = Array.from({length: Math.min(32, cpus().length, need.length)}, async () => {
      try {
        for (let i = next++; i < need.length; i = next++) {
          const d = need[i]!;
          diagnostics[d.path] = await sh(["/usr/bin/prlimit", `--as=${d.memory * 1024**2}`, "--", p.checker, "--diagnostics", "--timeout-ms", String(SOLVER_BUDGET_MS), join(p.corpus, d.path)], { cwd: out, signal: childSignal, timeoutMs: CASE_BUDGET_S * 1000 });
        }
      } catch (e) { stop.abort(e); throw e; }
    });
    const results = await Promise.allSettled(workers);
    await save(diagPath, diagnostics);
    const failed = results.find(r => r.status === "rejected");
    if (failed?.status === "rejected") throw failed.reason;
  }
  requireThat(Object.keys(diagnostics).length === need.length, "incomplete or stale diagnostics");
  const families = new Map<string, Family>();
  for (const {path, verdict} of need) {
    requireThat(Object.hasOwn(diagnostics, path), `missing diagnostics for ${path}`);
    let d: Diagnostic;
    try { d = parseDiagnostic(verdict, diagnostics[path]!); } catch (cause) { throw new Error(`invalid diagnostics for ${path}: ${String(cause)}`, { cause }); }
    const stat = a.cases[path]!;
    if (d.stage) stat.stage = d.stage;
    stat.pending = 0;
    for (const [rule, shape, count, first] of d.families) {
      stat.pending += count;
      const key = familyId(rule, shape), family: Family = families.get(key) ?? { rule, shape, pending: 0, cases: [] };
      family.pending += count; family.cases.push({ path, count, first }); families.set(key, family);
    }
    a.pending += stat.pending;
  }
  a.families = [...families.values()].sort((x, y) => y.pending - x.pending || x.rule.localeCompare(y.rule));
  for (const family of a.families) family.cases.sort((x,y) => y.count-x.count);
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

export async function analyze(p: Paths, out: string, sha: string, signal?: AbortSignal): Promise<Analysis> {
  const input = await inputs(p, signal);
  requireConfig(input.sha === sha, "source changed after regression");
  return inspect(p, out, input, signal);
}
export async function baseline(p: Paths, sha: string, signal?: AbortSignal, run: Run = sh): Promise<{sha:string; out:string}> {
  const input = await inputs(p, signal);
  requireConfig(input.sha === sha && input.tree === (await git(p.worktree, "rev-parse", `${sha}^{tree}`)).trim(), "baseline requires the clean local tip");
  const root = join(p.state, "baseline", sha, input.evaluator), marker = join(root, "complete.json");
  await mkdir(root, {recursive: true, mode: 0o700});
  if (await exists(marker)) {
    try {
      const { name, digest } = await json(marker);
      requireConfig(typeof name === "string" && /^attempt-[A-Za-z0-9]+$/.test(name), "invalid baseline completion marker");
      const out = join(root, name);
      await regular(join(out, "diagnostics.json"));
      const a = await inspect(p, out, input, signal);
      requireConfig(a.buildOk && hash(JSON.stringify(a)) === digest, "cached baseline differs from completed evaluation");
      return { sha, out };
    } catch (error) { signal?.throwIfAborted(); return configurationFailure(error); }
  }
  const out = await mkdtemp(join(root,"attempt-"));
  if (await execute(p, out, input, signal, run)) {
    const a = await analyze(p, out, sha, signal).catch(error => { signal?.throwIfAborted(); return configurationFailure(error); });
    requireConfig(a.buildOk && a.tree === input.tree && a.evaluator === input.evaluator, "baseline changed during evaluation");
    const tmp = join(out, "completion.tmp");
    await save(tmp, { name: out.slice(root.length+1), digest: hash(JSON.stringify(a)) }); await rename(tmp, marker);
  }
  return { sha, out };
}

/** The totals are for the actual stderr stats that were present, not extrapolations. */
export function metrics(a: Analysis): Record<string, number> {
  return {
    build_ok: a.buildOk ? 1 : 0, ci_pass: a.ciPass ? 1 : 0, tested: a.tested, accept: a.counts.ACCEPT ?? 0, partial: a.counts.PARTIAL ?? 0, reject: a.counts.REJECT ?? 0,
    timeout: a.counts.TIMEOUT ?? 0, errors: [...ERRORS].reduce((n, k) => n + (a.counts[k] ?? 0), 0),
    proof_steps_total: a.proofNodes, proof_steps_pending: a.pending, proof_steps_checked: a.proofNodes - a.pending,
    obligation_families: a.families.length, stats_cases: a.statsCases, check_ms_total: Math.round(a.checkMs), solve_ms_total: Math.round(a.solveMs),
    fstar_lemmas: a.lemmas, fstar_assumed: a.assumed,
  };
}

/** Rebuild from the measured cases; keep the history only for surviving work items. */
export function refreshQueue(queue: Queue, a: Analysis): Queue {
  const previous = new Map(queue.items.map((item) => [item.id, item]));
  const fresh: Item[] = [];
  const add = (item: Omit<Item, "attempts" | "status" | "notes">) => {
    const old = previous.get(item.id);
    fresh.push({ attempts: old?.attempts ?? 0, status: "open", notes: old?.notes ?? [], ...item });
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

export function pickItem(queue: Queue): Item | undefined {
  return queue.items.filter((i) => i.status === "open").sort((x, y) => x.attempts - y.attempts || KIND_RANK[x.kind] - KIND_RANK[y.kind] || y.weight - x.weight)[0];
}

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

export { expectedPaths, parseDiagnostic, validateBuildScript };

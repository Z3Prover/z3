import { createHash } from "node:crypto";
import { closeSync, createReadStream, openSync } from "node:fs";
import { lstat, mkdir, mkdtemp, readFile, readdir, realpath, rename, writeFile } from "node:fs/promises";
import { cpus, homedir } from "node:os";
import { join, resolve } from "node:path";
import type { Paths } from "./state.ts";

const PIN = "b188ff772b94fd5ac51ca97efffdd368e64df151";
const CORPUS_PIN = "91c60596fd6a43de189a1ccba8080a3b48797537";
const MANIFEST = "ea0349ec8af0fe55353ade9258e82c6c0ef8198b9d487c0cf306de4556c7483e";
const HARNESS = "fstar/tools/run_checker_regressions.py", BUILD = "fstar/tools/build_ocaml_checker.ps1";
const HARNESS_HASH = "28c23a82d911a98354aee6a7a6b0524637113c415bec1aa50c36f570a51a6a4a";
const REVIEW = "803df8055301cf5e65a3a05a2402a5da678652dd";
const PR_HARNESS = "da9f7dd490044153ce00d56f16509899fe9b8de6";
const PR_HARNESS_HASH = "4856282b9643a034b8fedc5bc7cb56441aa747102ed2f4efb9607efd2031d937";
const PR_FSTAR_HASH = "360741f618a1882b3bb6273afc98e7d564b76448c7a96b00d60c71c0d3abb46a";
const SCOPE = "fstar/tools/checker_scope.py", MODULES = "fstar/tools/checker_modules.json";
const OID = /^[0-9a-f]{40}$/;
export const CORPORA = [
  { name: "proofs", path: "regressions/proofs", total: 1800, memory: 2048, manifest: false, size: 17 },
  { name: "smtlib-sample", path: "regressions/smtlib-sample", total: 3600, memory: 4096, manifest: true, size: 225 },
] as const;
const ERRORS = new Set(["ERROR", "CRASH", "PROTOCOL_ERROR"]);
const SOLVER_BUDGET_MS = 10_000, CASE_BUDGET_S = 60;
const DIAGNOSTIC_BUDGET_S = 30 * 60;
const atBudget = (b: CaseStat) => b.wall >= 0.8 * CASE_BUDGET_S || (b.solveMs ?? 0) >= 0.8 * SOLVER_BUDGET_MS;
const KIND_RANK = { crash: 0, reject: 1, obligation: 2, timeout: 3, slow: 4 } as const;
const familyId = (rule: string, shape: string) => `obligation:${rule}|${shape}`;
export type CaseStat = { outcome: string; wall: number; solveMs?: number; checkMs?: number; proofNodes?: number; pending?: number; stage?: string };
export type Family = { rule: string; shape: string; pending: number; cases: { path: string; count: number; first: string }[] };
export type Analysis = {
  evidenceSha256?: string;
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
async function fileHash(path: string) {
  const digest = createHash("sha256");
  for await (const chunk of createReadStream(path)) digest.update(chunk);
  return digest.digest("hex");
}
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
function moduleLists<K extends string>(script: string, names: readonly K[]) {
  const lists = {} as Record<K, string[]>;
  for (const name of names) {
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
  const a = moduleLists(before, listNames), b = moduleLists(after, listNames);
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

function scopeManifest(text: string) {
  const value = JSON.parse(text);
  // JSON.parse silently takes the last duplicate key; never let two readers disagree.
  requireThat(!text.includes("\\") && (text.match(/"[^"]*"\s*:/g) ?? []).length === 3 &&
    Object.keys(value).sort().join() === "cherry_modules,modules,tests", "invalid checker manifest keys");
  for (const key of ["modules", "tests", "cherry_modules"]) {
    requireThat(Array.isArray(value[key]) && value[key].every((v: unknown) => typeof v === "string" && /^Z3[A-Za-z0-9_.-]+\.fsti?$/.test(v)), `invalid manifest ${key}`);
  }
  const names: string[] = [...value.modules, ...value.tests, ...value.cherry_modules];
  requireThat(new Set(names.map(n => n.toLowerCase())).size === names.length, "duplicate checker registration");
  return value as { modules: string[]; tests: string[]; cherry_modules: string[] };
}
function insertions(original: string[], updated: string[], label: string) {
  const old = new Set(original);
  requireThat(updated.filter(x => old.has(x)).join() === original.join(), `${label} removed/reordered`);
  return updated.filter(x => !old.has(x));
}
function validateRegistration(before: string, after: string, oldScript: string, newScript: string, added: Set<string>) {
  const a = scopeManifest(before), b = scopeManifest(after);
  requireThat(a.cherry_modules.join() === b.cherry_modules.join(), "protected cherry_modules changed");
  const mods = insertions(a.modules, b.modules, "production modules"), tests = insertions(a.tests, b.tests, "tests");
  for (const n of [...mods, ...tests]) requireThat(/^Z3[A-Za-z0-9_]+\.fst$/.test(n) && added.has(`fstar/${n}`), `unverified registration: ${n}`);
  requireThat(!mods.some(n => /Tests\.fst$/.test(n)), "regression test registered as production");
  const x = moduleLists(oldScript, ["order"] as const), y = moduleLists(newScript, ["order"] as const);
  requireThat(x.script === y.script, "protected build commands changed");
  const linked = insertions(x.lists.order, y.lists.order, "native link order");
  // Ghost-only modules need no linked object. Any newly linked implementation must be extracted.
  for (const n of linked) requireThat(n.endsWith(".ml") && mods.includes(n.slice(0, -3) + ".fst"), `unverified linked object: ${n}`);
  return { modules: b.modules, testModules: b.tests, order: y.lists.order };
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

async function prProtected(p: Paths, root: string, tree: string, base: string, upstream: string) {
  requireThat(OID.test(upstream) && OID.test(base), "invalid protected upstream/feature parent");
  await git(p.repo, "merge-base", "--is-ancestor", REVIEW, upstream);
  await git(p.repo, "merge-base", "--is-ancestor", upstream, base);
  const immutableTools = [SCOPE, HARNESS, ".github/scripts/install-pulse-checker-toolchains.sh", ".github/workflows/pulse-checker-build.yml"];
  await git(p.repo, "diff", "--quiet", "--no-ext-diff", "--no-textconv", REVIEW, upstream, "--", ...immutableTools);
  const candidate = await lsTree(root, tree, "fstar");
  const script = await blob(root, tree, BUILD), manifest = await blob(root, tree, MODULES);
  // Inspect the authenticated upstream build language before accepting it as a reference.
  const official = await lsTree(p.repo, upstream, "fstar"), reviewed = await lsTree(p.repo, REVIEW, "fstar");
  validateRegistration(await blob(p.repo, REVIEW, MODULES), await blob(p.repo, upstream, MODULES),
    await blob(p.repo, REVIEW, BUILD), await blob(p.repo, upstream, BUILD), new Set([...official.keys()].filter(k => !reviewed.has(k))));
  async function compare(repo: string, rev: string, ref: Map<string,string>) {
    const added = new Set([...candidate.keys()].filter(k => !ref.has(k)));
    const original = await blob(repo, rev, MODULES);
    const lists = validateRegistration(original, manifest, await blob(repo, rev, BUILD), script, added);
    const tests = new Set(scopeManifest(original).tests.map(n => `fstar/${n}`));
    const registered = new Set([...lists.modules, ...lists.testModules].map(n => `fstar/${n}`));
    for (const file of registered) requireThat(candidate.get(file)?.startsWith("100644 blob "), `missing or non-regular registered module: ${file}`);
    for (const file of added) {
      requireThat(!guardedPath(file) || registered.has(file), `unverified evaluator/runtime file: ${file}`);
      if (!/^fstar\/Z3[^/]*\.fst$/i.test(file)) continue;
      const name = file.slice(6, -4).toLowerCase();
      requireThat(registered.has(file) && ![...candidate.keys()].some(k => k !== file &&
        [file.toLowerCase(), `fstar/${name}.fsti`, `fstar/ocaml_runtime/${name}.ml`].includes(k.toLowerCase())), `unregistered or shadowing module: ${file}`);
    }
    for (const [file, entry] of ref) {
      if ((!guardedPath(file) && !tests.has(file)) || candidate.get(file) === entry) continue;
      requireThat(entry.startsWith("100644 blob ") && candidate.get(file)?.startsWith("100644 blob "), `protected file removed or mode changed: ${file}`);
      if (file === MODULES || file === BUILD) continue;
      requireThat((tests.has(file) || protectedTest(file)) && appendedTest(file, await blob(repo, rev, file), await blob(root, tree, file)), `protected evaluator or original test changed: ${file}`);
    }
    return lists;
  }
  await compare(p.repo, upstream, official);
  return compare(root, base, await lsTree(root, base, "fstar"));
}

async function checkProtected(p: Paths, root: string, tree: string, base: string) {
  if (p.reviewedUpstream !== undefined) return prProtected(p, root, tree, base, p.reviewedUpstream);
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
    if (file === BUILD || (p.reviewedUpstream !== undefined && file === MODULES)) continue;
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
type Inputs = { sha: string; tree: string; evaluator: string; harness: string; corpora: CorpusInput[]; identity: { fstar: string; harnessSha256: string } };
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
export async function evaluatorIdentity(p: Paths, signal?: AbortSignal): Promise<string> {
  return (await inputs(p, signal)).evaluator;
}
async function readInputs(p: Paths, signal?: AbortSignal): Promise<Inputs> {
  signal?.throwIfAborted();
  requireThat(p.maxCases === 0, "complete Pulse CI evaluation requires --max-cases 0");
  requireThat(/^[A-Za-z0-9_.-]+$/.test(p.opamSwitch), "invalid opam switch name");
  requireThat(await realpath(p.corpus) === resolve(p.corpus) && (await git(p.corpus, "rev-parse", "HEAD")).trim() === CORPUS_PIN && !(await git(p.corpus, "status", "--porcelain", "--untracked-files=all")), "corpus must be the clean pinned z3test checkout");
  const sha = (await git(p.worktree, "rev-parse", "HEAD")).trim(), tree = (await git(p.worktree, "write-tree")).trim();
  await git(p.worktree, "diff", "--quiet", "--no-ext-diff", "--no-textconv", "--");
  requireThat(!(await git(p.worktree, "ls-files", "--others", "--exclude-standard", "-z")), "source has untracked build inputs");
  const pr = p.reviewedUpstream !== undefined, reference = pr ? REVIEW : PIN;
  if (pr) requireThat(OID.test(p.reviewedUpstream!) && (await git(p.repo, "rev-parse", `${reference}:${HARNESS}`)).trim() === PR_HARNESS, "wrong reviewed PR harness blob");
  const harness = await blob(p.repo, reference, HARNESS), harnessSha256 = pr ? PR_HARNESS_HASH : HARNESS_HASH;
  requireThat(hash(harness) === harnessSha256, "protected regression harness digest mismatch");
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
  const fstarSha256 = await fileHash(p.fstarExe);
  if (pr) requireThat(fstarSha256 === PR_FSTAR_HASH, "wrong v2026.10.25 Linux x86_64 F* executable");
  const fstar = await must([p.fstarExe, "--version"], { cwd, signal });
  requireThat(pr ? /^F\* 2026\.10\.25$/m.test(fstar) && /^commit=362e792b3aa882f1766b95c7450e3fe63081163d$/m.test(fstar)
    : /^F\* 2026\.09\.27$/m.test(fstar) && /^commit=7deb38a27c86990664c6b41e4b6093597acdebd4$/m.test(fstar), "wrong pinned F* compiler");
  const identity = {
    ...(pr && { policy: "upstream-pr-v1", upstream: p.reviewedUpstream, parent: sha, harnessBlob: PR_HARNESS,
      upstreamBuild: (await git(p.repo, "rev-parse", `${p.reviewedUpstream}:${BUILD}`)).trim(),
      upstreamScope: (await git(p.repo, "rev-parse", `${p.reviewedUpstream}:${SCOPE}`)).trim(),
      parentManifest: (await git(p.worktree, "rev-parse", `${sha}:${MODULES}`)).trim(),
      parentBuild: (await git(p.worktree, "rev-parse", `${sha}:${BUILD}`)).trim() }),
    protectedCommit: reference, harnessSha256, evaluationSha256: await fileHash(import.meta.path),
    corpusCommit: CORPUS_PIN, manifestSha256: MANIFEST, suites: CORPORA, corpora, maxCases: p.maxCases,
    solverTimeoutMs: SOLVER_BUDGET_MS, caseTimeoutS: CASE_BUDGET_S, diagnosticTimeoutS: DIAGNOSTIC_BUDGET_S, buildJobs: jobs(),
    fstar, fstarSha256, opamSwitch: p.opamSwitch, toolchain,
  };
  return { sha, tree, evaluator: hash(JSON.stringify(identity)), harness, corpora, identity };
}

/** PR evidence keeps its own source, build products and checked modules, including cached baselines. */
export function evaluationPaths(p: Paths, out: string): Paths {
  return p.reviewedUpstream === undefined ? p : { ...p, worktree: join(out, "source"), z3Build: join(out, "z3-build"),
    z3Install: join(out, "z3-install"), fstarCache: join(out, "fstar-cache"), checkerDir: join(out, "checker"), checker: join(out, "checker", "checker") };
}
async function checkoutTestedTree(p: Paths, out: string, input: Pick<Inputs, "sha"|"tree">) {
  const root = evaluationPaths(p, out).worktree;
  await mkdir(root, {mode: 0o700});
  await git(root, "init", "--template=", "--quiet");
  await git(root, "-c", "protocol.allow=never", "-c", "protocol.file.allow=always", "fetch", "--depth=1", "--no-tags", "--no-recurse-submodules", "--", resolve(p.worktree), input.sha);
  await git(root, "switch", "--no-overwrite-ignore", "--detach", input.sha);
  if ((await git(root, "write-tree")).trim() === input.tree) return input.sha;
  // The upstream report and harness name HEAD. Give a staged tree its own real, local-only identity.
  const patch = join(out, "source.patch");
  await git(p.worktree, "diff", "--binary", "--no-renames", "--no-ext-diff", "--no-textconv", "--full-index", `--output=${patch}`, input.sha, input.tree, "--");
  await git(root, "apply", "--binary", "--index", "--whitespace=nowarn", "--", patch);
  requireThat((await git(root, "write-tree")).trim() === input.tree, "independent build checkout differs from staged tree");
  const commit = (await git(root, "-c", "user.name=Pulse verifier", "-c", "user.email=verifier@localhost", "commit-tree", input.tree, "-p", input.sha, "-m", "Local verifier input")).trim();
  await git(root, "switch", "--no-overwrite-ignore", "--detach", commit);
  return commit;
}
function validateScope(report: Record<string, unknown>, modules: string[], tests: string[], source: string, fstar: string) {
  const selected = [...modules, ...tests];
  requireThat(report.source_sha === source && report.backend === "ocaml" && report.mode === "full" && report.native_tests === true &&
    report.fstar === fstar.trim() && report.selected_count === selected.length &&
    JSON.stringify(report.selected_modules) === JSON.stringify(selected) && JSON.stringify(report.registered_not_selected) === "[]", "wrong source, compiler or incomplete native verification scope");
}
async function scopeEvidence(p: Paths, out: string, tree: string, source: string, fstar: string) {
  const path = join(out, "scope-ocaml.json");
  await regular(path);
  const {modules, tests} = scopeManifest(await blob(p.worktree, tree, MODULES));
  validateScope(await json(path), modules, tests, source, fstar);
  return { scope_sha256: await fileHash(path), native_tests_sha256: await fileHash(join(p.checkerDir, "native-tests")) };
}

async function execute(p: Paths, out: string, input: Inputs, signal: AbortSignal | undefined, run: Run) {
  await mkdir(out, { recursive: true, mode: 0o700 });
  requireThat(!(await readdir(out)).length && await realpath(out) === resolve(out), `refusing nonempty or aliased evidence directory: ${out}`);
  const pr = p.reviewedUpstream !== undefined;
  if (pr && input.tree !== (await git(p.worktree, "rev-parse", `${input.sha}^{tree}`)).trim()) await validatePatch(p, input.sha, p.worktree);
  else await checkProtected(p, p.worktree, input.tree, input.sha).catch(configurationFailure);
  const source = pr ? await checkoutTestedTree(p, out, input) : input.sha;
  p = evaluationPaths(p, out);
  const start = Date.now(), harness = join(out, "run_checker_regressions.py");
  await writeFile(harness, input.harness, { flag: "wx", mode: 0o400 });
  await save(join(out, "evaluator.json"), input.identity);
  const build = await run(cleanCmd(opam(p, "pwsh", "-NoProfile", "-File", BUILD, "-FstarExe", p.fstarExe,
    "-Z3WindowsBuildDir", p.z3Build, "-Z3InstallDir", p.z3Install, "-CacheDir", p.fstarCache, "-WslBuildDir", p.checkerDir,
    "-OpamSwitch", p.opamSwitch, "-BuildJobs", String(jobs()), "-RunTests", ...(pr ? ["-ReportDir", out] : []))), { cwd: p.worktree, log: join(out, "build.log"), signal });
  signal?.throwIfAborted();
  requireThat(Number.isInteger(build.code) && build.code >= 0 && build.code < 128, `build was interrupted: ${build.code}`);
  const metadata = { sha: input.sha, tree: input.tree, evaluator: input.evaluator, wall_seconds: (Date.now() - start) / 1000, exit_code: build.code, fstar_exe: p.fstarExe,
    ...(pr && { source_sha: source, build_log_sha256: await fileHash(join(out, "build.log")) }) };
  if (build.code !== 0) { await save(join(out, "build.json"), metadata); return false; }
  const checker_version = (await must([p.checker, "--version"], { cwd: out, signal })).trim();
  requireThat(checker_version.length > 0, "built checker has no producer version");
  await save(join(out, "build.json"), { ...metadata, ...(pr && await scopeEvidence(p, out, input.tree, source, input.identity.fstar)),
    checker_version, checker_sha256: await fileHash(p.checker), z3_sha256: await fileHash(join(p.z3Install, "bin/z3")) });
  for (const c of CORPORA) {
    const dir = join(out, c.name);
    const manifest = c.manifest ? ["--manifest", join(p.corpus, c.path, "manifest.json")] : [];
    const r = await run(cleanCmd(["python3", "-I", "-B", harness, "run", "--checker", p.checker, "--corpus", p.corpus, "--corpus-path", c.path,
      "--corpus-commit", CORPUS_PIN, "--max-cases", "0", "--expected-cases", String(c.size), "--solver-timeout-ms", String(SOLVER_BUDGET_MS),
      "--case-timeout-seconds", String(CASE_BUDGET_S), "--total-timeout-seconds", String(c.total), "--memory-limit-mb", String(c.memory),
      ...manifest, "--output", dir], pr ? { SOURCE_SHA: source } : { GITHUB_SHA: source }), { cwd: out, log: join(out, `${c.name}.log`), signal });
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
const PR_STATS = /^solve_ms=([\d.]+) marshal_ms=([\d.]+) check_ms=([\d.]+) expressions=(\d+) declarations=(\d+) proof_nodes=(\d+) semantics=(legacy|sorted-datatype|sorted-core)$/;
function checkStatistics(line: string, stats?: Record<string,unknown>) {
  const m = PR_STATS.exec(line);
  const fields = ["solve_ms", "marshal_ms", "check_ms", "expressions", "declarations", "proof_nodes"];
  requireThat(m && stats && stats.semantics === m[7] && fields.every((k,i) => Number.isFinite(Number(m[i+1])) && Number(m[i+1]) === stats[k]), "truncated or contradictory native statistics");
}
const VERDICTS: Record<number, [string, RegExp]> = { 0: ["ACCEPT", /^ACCEPT$/], 1: ["REJECT", /^REJECT$/], 3: ["PARTIAL", /^PARTIAL [1-9]\d*$/], 4: ["SAT", /^SAT$/], 5: ["UNKNOWN", /^UNKNOWN .+$/] };
function retainedOutcome(code: number | null, text: string) {
  if (code === null) return "TIMEOUT";
  requireThat(Number.isInteger(code), "missing case return code");
  if (code === 2) return "ERROR";
  const v = VERDICTS[code];
  return v ? v[1].test(text) ? v[0] : "PROTOCOL_ERROR" : "CRASH";
}

async function inspect(p: Paths, out: string, input: Inputs, signal?: AbortSignal): Promise<Analysis> {
  const pr = p.reviewedUpstream !== undefined;
  p = evaluationPaths(p, out);
  const build = await json(join(out, "build.json"));
  requireConfig(hash(JSON.stringify(await json(join(out, "evaluator.json")))) === input.evaluator, "wrong retained evaluator/toolchain inputs");
  requireConfig(build.sha === input.sha && build.tree === input.tree && build.evaluator === input.evaluator && Number.isInteger(build.exit_code), "stale build/evaluator identity");
  await regular(join(out, "build.log"));
  if (pr) await regular(join(out, "run_checker_regressions.py"));
  requireConfig(await fileHash(join(out, "run_checker_regressions.py")) === input.identity.harnessSha256, "retained protected harness changed");
  const source = pr ? build.source_sha : input.sha;
  if (pr) {
    requireConfig(OID.test(source) && (await git(p.worktree, "rev-parse", "HEAD")).trim() === source &&
      (await git(p.worktree, "rev-parse", "HEAD^{tree}")).trim() === input.tree &&
      (source === input.sha || (await git(p.worktree, "rev-parse", "HEAD^")).trim() === input.sha) &&
      !(await git(p.worktree, "status", "--porcelain", "-uno")), "wrong tested parent/tree or modified verification checkout");
    requireConfig(build.build_log_sha256 === await fileHash(join(out, "build.log")), "retained build log changed");
  }
  const a: Analysis = { sha: input.sha, tree: input.tree, evaluator: input.evaluator, buildOk: build.exit_code === 0, ciPass: build.exit_code === 0, statsCases: 0, tested: 0, counts: {}, pending: 0, proofNodes: 0, checkMs: 0, solveMs: 0, families: [], cases: {}, lemmas: 0, assumed: 0 };
  if (!a.buildOk) return a;
  if (pr) {
    for (const path of [p.checker, join(p.checkerDir, "native-tests"), join(p.z3Install, "bin/z3")]) await regular(path);
    const scope = await scopeEvidence(p, out, input.tree, source, input.identity.fstar);
    requireConfig(scope.scope_sha256 === build.scope_sha256 && scope.native_tests_sha256 === build.native_tests_sha256, "retained native scope or tests changed");
  }
  requireConfig(build.checker_sha256 === await fileHash(p.checker) && build.z3_sha256 === await fileHash(join(p.z3Install, "bin/z3")), "built checker or checkout solver changed");
  const need: { path: string; verdict: string; memory: number }[] = [];
  const artifacts: Record<string,string> = pr ? {
    "build.log": build.build_log_sha256, "checker/checker": build.checker_sha256, "checker/native-tests": build.native_tests_sha256,
    "z3-install/bin/z3": build.z3_sha256, "run_checker_regressions.py": input.identity.harnessSha256,
  } : {};
  for (const [n,c] of CORPORA.entries()) {
    const dir = join(out, c.name), pinned = input.corpora[n]!;
    const selected = await json(join(dir, "selection.json")), summary = await json(join(dir, "summary.json"));
    const code = (await json(join(out, `${c.name}.exit.json`))).exit_code;
    requireThat(selected.corpus_path === c.path && selected.corpus_commit === CORPUS_PIN && selected.z3_commit === source && selected.checker_version === build.checker_version &&
      selected.solver_timeout_ms === SOLVER_BUDGET_MS && selected.case_timeout_seconds === CASE_BUDGET_S && selected.total_timeout_seconds === c.total && selected.memory_limit_mb === c.memory &&
      selected.discovered === c.size && JSON.stringify(summary.selection) === JSON.stringify(selected), `wrong revision, selection or budget: ${dir}`);
    expectedPaths(selected.paths, pinned.paths);
    if (pr) requireThat(summary.corpus_outcome === "success" && (!c.manifest || Object.keys(selected.input_sha256 ?? {}).length === c.size), "incomplete retained corpus selection");
    if (c.manifest) {
      const name = `${c.name}/input-manifest.json`, path = join(out, name);
      if (pr) await regular(path);
      requireThat(selected.manifest?.sha256 === MANIFEST && await fileHash(path) === MANIFEST, "wrong recorded corpus manifest");
      if (pr) artifacts[name] = MANIFEST;
    }
    requireThat(summary.selected === c.size && summary.tested === c.size && Array.isArray(summary.warnings) && !summary.warnings.length &&
      summary.build_outcome === "success" && summary.runner_outcome === (code === 0 ? "success" : "failure"), `incomplete report at ${dir}: ${JSON.stringify(summary.warnings)}`);
    const raw = await readFile(join(dir, "results.jsonl"), "utf8");
    requireThat(raw.endsWith("\n"), `truncated results at ${dir}`);
    const rows = raw.slice(0,-1).split("\n").map(l => JSON.parse(l));
    expectedPaths(rows.map(r => r.path), pinned.paths);
    if (pr) {
      for (const name of [`${c.name}.log`, `${c.name}.report.log`, `${c.name}.exit.json`, `${c.name}/selection.json`, `${c.name}/summary.json`]) artifacts[name] = await fileHash(join(out, name));
      artifacts[`${c.name}/results.jsonl`] = hash(raw);
    }
    const counts: Record<string,number> = {};
    for (const [i,r] of rows.entries()) {
      signal?.throwIfAborted();
      const path = pinned.paths[i]!, stem = `logs/${String(i).padStart(6, "0")}`;
      requireThat(r.stdout === `${stem}.stdout` && r.stderr === `${stem}.stderr` && Number.isFinite(r.wall_seconds) && r.wall_seconds >= 0, `missing per-case logs/timing: ${path}`);
      if (c.manifest) requireThat(r.input_sha256 === pinned.sha256[path] && selected.input_sha256?.[path] === pinned.sha256[path], `case digest mismatch: ${path}`);
      const stdoutPath = join(dir, r.stdout), stderrPath = join(dir, r.stderr);
      await regular(stdoutPath); await regular(stderrPath);
      const stdoutBytes = await readFile(stdoutPath), stderrBytes = await readFile(stderrPath);
      const stdout = stdoutBytes.toString().trim(), stderr = stderrBytes.toString();
      if (pr) {
        artifacts[`${c.name}/${r.stdout}`] = hash(stdoutBytes);
        artifacts[`${c.name}/${r.stderr}`] = hash(stderrBytes);
      }
      requireThat(r.verdict === stdout && r.outcome === retainedOutcome(r.returncode, stdout), `truncated/invalid case verdict: ${path}`);
      const stat: CaseStat = { outcome: r.outcome, wall: r.wall_seconds };
      const stats = stderr.split("\n").filter(line => line.startsWith("solve_ms="));
      requireThat(stats.length <= 1, `ambiguous timing: ${path}`);
      if (pr) requireThat(Boolean(stats.length) === (r.statistics !== undefined), `scored statistics disagree with native log: ${path}`);
      if (stats.length) {
        const m = STATS.exec(stats[0]!);
        if (pr) checkStatistics(stats[0]!, r.statistics);
        requireThat(m && (pr || / semantics=(?:legacy|sorted-datatype)$/.test(stats[0]!)) && m.slice(1).every(v => Number.isFinite(Number(v))), `truncated phase statistics: ${path}`);
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
          diagnostics[d.path] = await sh(["/usr/bin/prlimit", `--as=${d.memory * 1024**2}`, "--", p.checker, "--diagnostics", "--timeout-ms", String(SOLVER_BUDGET_MS), join(p.corpus, d.path)], { cwd: out, signal: childSignal, timeoutMs: DIAGNOSTIC_BUDGET_S * 1000 });
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
  if (pr) {
    for (const name of (await readdir(p.fstarCache)).filter(n => n.endsWith(".checked")).sort()) {
      const file = join(p.fstarCache, name); await regular(file);
      artifacts[`fstar-cache/${name}`] = await fileHash(file);
    }
    for (const name of ["build.json", "diagnostics.json", "scope-ocaml.json", "evaluator.json"]) artifacts[name] = await fileHash(join(out, name));
    const path = join(out, "evidence.json");
    if (await exists(path)) requireConfig(JSON.stringify(await json(path)) === JSON.stringify(artifacts), "retained native evidence changed");
    else await save(path, artifacts);
    a.evidenceSha256 = await fileHash(path);
  }
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

/** inspect() establishes pinned input identity and per-case native evidence, not aggregate counts alone. */
export function prCandidateFailure(a: Analysis): string | null {
  if (!a.buildOk || !a.ciPass) return "candidate build or corpus CI failed";
  const total = CORPORA.reduce((n,c) => n + c.size, 0), cases = Object.values(a.cases);
  if (a.tested !== total || cases.length !== total) return `candidate did not attempt all ${total} pinned cases`;
  const counts: Record<string,number> = {};
  for (const {outcome} of cases) {
    if (!["ACCEPT","PARTIAL","REJECT","SAT","UNKNOWN","TIMEOUT"].includes(outcome)) return `candidate contains ${outcome} case`;
    counts[outcome] = (counts[outcome] ?? 0) + 1;
  }
  if ([...new Set([...Object.keys(counts), ...Object.keys(a.counts)])].some(k => (counts[k] ?? 0) !== (a.counts[k] ?? 0))) return "candidate case counts disagree";
  return null;
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
      if (p.reviewedUpstream !== undefined) await regular(join(out, "evidence.json"));
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

export { expectedPaths, parseDiagnostic, validateBuildScript, validateRegistration, validateScope, checkStatistics, checkoutTestedTree };

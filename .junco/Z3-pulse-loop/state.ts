import { execFile, execFileSync } from "node:child_process";
import { createHash, randomUUID } from "node:crypto";
import { closeSync, constants, fstatSync, fsyncSync, linkSync, lstatSync, mkdirSync, openSync, readFileSync, readdirSync, realpathSync, renameSync, statfsSync, unlinkSync, writeFileSync } from "node:fs";
import { homedir } from "node:os";
import { basename, dirname, isAbsolute, join, resolve } from "node:path";
import { isDeepStrictEqual } from "node:util";
import { judge, metrics, pickItem, prCandidateFailure, validatePatch, type Analysis, type Item, type Queue } from "./evaluation.ts";

const LEGACY = "/btrfs/Z3-pulse-loop", BRANCH = "loop/pulse-local", MARKER = ".pulse-local.json";
const REF = `refs/heads/${BRANCH}`, MOVE = ".pr-parent-move.json";
const OID = /^[0-9a-f]{40}$/;
const digest = (b: Buffer) => createHash("sha256").update(b).digest("hex");
const gitEnv = {
  PATH: "/usr/bin:/bin", HOME: "/nonexistent", LC_ALL: "C", GIT_CONFIG_NOSYSTEM: "1", GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_ATTR_NOSYSTEM: "1", GIT_ALLOW_PROTOCOL: "file", GIT_TERMINAL_PROMPT: "0", GIT_NO_REPLACE_OBJECTS: "1", GIT_OPTIONAL_LOCKS: "0",
  GIT_AUTHOR_NAME: "Z3 Pulse local", GIT_AUTHOR_EMAIL: "pulse@localhost", GIT_COMMITTER_NAME: "Z3 Pulse local", GIT_COMMITTER_EMAIL: "pulse@localhost",
};
const gitArgs = ["/usr/bin/git", "-c", "core.hooksPath=/dev/null", "-c", "core.fsmonitor=false", "-c", "gc.auto=0", "-c", "commit.gpgSign=false", "-c", "credential.helper="];

export type Paths = {
  repo: string; state: string; worktree: string; corpus: string; fstarExe: string; opamSwitch: string; maxCases: number; base?: string; reviewedUpstream?: string;
  z3Build: string; z3Install: string; fstarCache: string; checkerDir: string; checker: string;
};
const outputs = (dir: string) => ({ z3Build: join(dir, "z3-build"), z3Install: join(dir, "z3-install"), fstarCache: join(dir, "fstar-cache"), checkerDir: join(dir, "checker"), checker: join(dir, "checker", "checker") });
export function paths(env: NodeJS.ProcessEnv = process.env): Paths {
  const state = env.Z3_PULSE_LOOP_STATE ?? "/btrfs/Z3-pulse-loop-local", base = env.Z3_PULSE_LOOP_BASE;
  const maxCases = Number(env.Z3_PULSE_LOOP_MAX_CASES ?? 0);
  if (!Number.isSafeInteger(maxCases) || maxCases < 0) throw new StateConflict("invalid nonnegative case limit");
  if (base !== undefined && !OID.test(base)) throw new StateConflict("Z3_PULSE_LOOP_BASE must be an immutable full commit SHA");
  return { repo: env.Z3_PULSE_LOOP_REPO ?? join(homedir(), "git", "z3"), state, worktree: join(state, "worktree"),
    corpus: env.Z3_PULSE_LOOP_CORPUS ?? join(LEGACY, "z3test"), fstarExe: env.FSTAR_EXE ?? "/opt/fstar-v2026.09.27/bin/fstar.exe",
    opamSwitch: env.OPAMSWITCH ?? "aeneas", maxCases, base, ...outputs(state) };
}
export class StateConflict extends Error { override name = "StateConflict"; }
function need(ok: unknown, message: string): asserts ok { if (!ok) throw new StateConflict(message); }
function conflict(error: unknown): never {
  if (error instanceof StateConflict || (error instanceof Error && error.name === "AbortError")) throw error;
  throw new StateConflict(String(error), { cause: error });
}
const exists = (p: string) => lstatSync(p, { throwIfNoEntry: false }) !== undefined;
const below = (path: string, parent: string) => path === parent || path.startsWith(parent.endsWith("/") ? parent : `${parent}/`);
function directory(path: string, owned = false) {
  const s = lstatSync(path);
  need(s.isDirectory() && realpathSync.native(path) === path && (!owned || s.uid === process.getuid!()), `unexpected directory or ownership: ${path}`);
  return s;
}
function file(path: string): Buffer {
  directory(dirname(path));
  const fd = openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW | constants.O_NONBLOCK);
  try {
    const s = fstatSync(fd); need(s.isFile() && s.uid === process.getuid!() && s.nlink === 1, `unexpected private file: ${path}`);
    return readFileSync(fd);
  } finally { closeSync(fd); }
}
function save(path: string, data: string | Buffer, exclusive = false) {
  const parent = dirname(path); directory(parent, true);
  const tmp = join(parent, `.pulse-write-${randomUUID()}`), fd = openSync(tmp, "wx", exclusive ? 0o400 : 0o600);
  try { writeFileSync(fd, data); fsyncSync(fd); } finally { closeSync(fd); }
  if (exclusive) { linkSync(tmp, path); unlinkSync(tmp); }
  else { if (exists(path)) need(lstatSync(path).isFile() && lstatSync(path).nlink === 1, `refusing to replace ${path}`); renameSync(tmp, path); }
  const d = openSync(parent, constants.O_RDONLY | constants.O_DIRECTORY | constants.O_NOFOLLOW);
  try { fsyncSync(d); } finally { closeSync(d); }
}
const json = (value: unknown) => `${JSON.stringify(value, null, 2)}\n`;
function command(cwd: string, argv: string[], signal?: AbortSignal, input?: Buffer): Promise<Buffer> {
  signal?.throwIfAborted();
  const { promise, resolve: done, reject } = Promise.withResolvers<Buffer>();
  const child = execFile(argv[0]!, argv.slice(1), { cwd, env: gitEnv, encoding: "buffer", signal, maxBuffer: 256 * 1024 * 1024 },
    (err, out) => err ? reject(err) : done(out));
  child.stdin!.on("error", (err: NodeJS.ErrnoException) => { if (err.code !== "EPIPE") reject(err); });
  child.stdin!.end(input);
  return promise;
}
const git = (cwd: string, args: string[], signal?: AbortSignal, input?: Buffer) => command(cwd, [...gitArgs, ...args], signal, input);
const text = async (cwd: string, args: string[], s?: AbortSignal) => (await git(cwd, args, s)).toString().trimEnd();

function boundPr(p: Paths): { pr: number; head: string; iteration: number } | undefined {
  const match = /^Z3-pulse-loop-pr-([1-9]\d*)$/.exec(basename(p.state));
  if (p.reviewedUpstream === undefined) {
    need(!match, "PR state requires the reviewed publication policy");
    return undefined;
  }
  const pr = Number(match?.[1]);
  need(Number.isSafeInteger(pr) && basename(p.repo) === `pr-${pr}-publisher` && !below(p.state, "/btrfs/Z3-pulse-loop-local"), "not a bound PR campaign path");
  need(p.base && OID.test(p.base) && OID.test(p.reviewedUpstream), "PR state requires immutable seed and official upstream commits");
  need(!(directory(p.repo, true).mode & 0o077), "PR publisher checkout must be private");
  const binding = JSON.parse(file(join(p.repo, ".git", "pulse-binding.json")).toString());
  need(binding.version === 1 && binding.pr === pr && binding.state === p.state && binding.seed === p.base && OID.test(binding.head) && OID.test(binding.upstream), "PR publisher/seed binding mismatch");
  need(Number.isSafeInteger(binding.iteration) && binding.iteration >= 0, "invalid acknowledged PR iteration");
  return binding;
}

export type Attempt = Readonly<{ iteration: number; base: string; tree: string; patch: string; hash: string }>;
type Lock = { fd: number; attempt?: Attempt; validated?: Attempt };
const locks = new Map<string, Lock>();
function held(p: Paths) {
  const lock = locks.get(p.state); need(lock, `state ownership required: ${p.state}`);
  const s = directory(p.state, true), open = fstatSync(lock.fd);
  need(s.dev === open.dev && s.ino === open.ino && !(s.mode & 0o077) && p.worktree === join(p.state, "worktree"), `state directory changed: ${p.state}`);
  return lock;
}
/** flock(1) locks the inherited open file description. Only the owner closes its directory FD. */
export function acquire(p: Paths): () => void {
  let fd: number | undefined;
  try {
    need(!locks.has(p.state) && isAbsolute(p.state) && p.state === resolve(p.state), `state already owned or noncanonical: ${p.state}`);
    directory(p.repo); directory(p.corpus); directory(dirname(p.state));
    boundPr(p);
    for (const other of [p.repo, p.corpus, LEGACY]) need(!below(p.state, other) && !below(other, p.state), `state overlaps protected path: ${other}`);
    if (!exists(p.state)) {
      need(statfsSync(dirname(p.state)).type === 0x9123683e, `state parent must be on Btrfs: ${dirname(p.state)}`);
      mkdirSync(p.state, { mode: 0o700 });
    }
    const s = directory(p.state, true);
    need(!(s.mode & 0o077) && statfsSync(p.state).type === 0x9123683e, `state must be private and on Btrfs: ${p.state}`);
    fd = openSync(p.state, constants.O_RDONLY | constants.O_DIRECTORY | constants.O_NOFOLLOW);
    const open = fstatSync(fd); need(open.dev === s.dev && open.ino === s.ino, `state replaced at open: ${p.state}`);
    execFileSync("/usr/bin/flock", ["-n", "3"], { env: gitEnv, stdio: ["ignore", "ignore", "pipe", fd] });
    need(exists(join(p.state, MARKER)) || readdirSync(p.state).length === 0, `refusing nonempty uninitialized state: ${p.state}`);
    const lock: Lock = { fd }; locks.set(p.state, lock);
    return () => { if (locks.get(p.state) === lock) { locks.delete(p.state); closeSync(lock.fd); } };
  } catch (e) { if (fd !== undefined) closeSync(fd); conflict(e); }
}

type Marker = { version: 1; repo: string; base: string; tip: string; config: string; pr?: number };
function marker(p: Paths): Marker {
  held(p);
  const m = JSON.parse(file(join(p.state, MARKER)).toString()) as Marker;
  need(m.version === 1 && m.pr === boundPr(p)?.pr && m.repo === p.repo && OID.test(m.base) && OID.test(m.tip) && (!p.base || p.base === m.base), `unexpected private seed identity in ${p.state}`);
  return m;
}
function subvolume(p: Paths) {
  const s = directory(p.worktree, true);
  need(s.ino === 256 && statfsSync(p.worktree).type === 0x9123683e, `not an owned Btrfs seed subvolume: ${p.worktree}`);
}
async function checkout(p: Paths, signal?: AbortSignal) {
  const m = marker(p), w = p.worktree, d = join(w, ".git"); subvolume(p); directory(d, true);
  for (const dir of ["objects", "objects/info", "objects/pack", "refs", "refs/heads"]) directory(join(d, dir), true);
  if (exists(join(d, "refs/heads/loop"))) directory(join(d, "refs/heads/loop"), true);
  for (const name of ["HEAD", "index", ...[`refs/heads/${BRANCH}`, "packed-refs"].filter(n => exists(join(d, n)))]) {
    const s = lstatSync(join(d, name)); need(s.isFile() && s.nlink === 1 && s.uid === process.getuid!(), `foreign Git file: ${join(d, name)}`);
  }
  for (const name of ["commondir", "gitdir", "objects/info/alternates", "info/grafts", "info/attributes", "info/exclude", "info/sparse-checkout", "worktrees", "modules", "MERGE_HEAD", "rebase-merge", "rebase-apply", "CHERRY_PICK_HEAD", "REVERT_HEAD"]) need(!exists(join(d, name)), `foreign Git metadata: ${join(d, name)}`);
  need(digest(file(join(d, "config"))) === m.config, `private repository configuration changed: ${d}`);
  const info = await text(w, ["rev-parse", "--show-toplevel", "--absolute-git-dir", "--path-format=absolute", "--git-common-dir", "HEAD"], signal);
  const head = info.split("\n").at(-1)!;
  need(OID.test(head) && info === [w, d, d, head].join("\n") && !await text(w, ["remote"], signal), `foreign checkout, Git directory or remote: ${w}`);
  const refs = await text(w, ["for-each-ref", "--format=%(refname) %(objectname)"], signal), ref = refs.slice(-40);
  need(OID.test(ref) && refs === `${REF} ${ref}`, `unexpected private refs: ${w}`);
  const field = file(join(d, "HEAD")).toString(), attached = field === `ref: ${REF}\n`;
  need(attached ? head === ref : field === `${head}\n`, `foreign HEAD: ${w}`);
  return { m, head, ref, attached };
}
async function authority(p: Paths, expected?: string, signal?: AbortSignal) {
  const { m, head, attached } = await checkout(p, signal);
  need(attached && head === m.tip && (expected === undefined || head === expected), `private HEAD changed (expected ${expected ?? m.tip}): ${p.worktree}`);
  return m;
}
async function checkIndex(w: string, s?: AbortSignal) {
  const flags = (await git(w, ["ls-files", "-v", "-z"], s)).toString().split("\0");
  need(flags.every(v => !v || v.startsWith("H ")), `unexpected skip-worktree/assume-unchanged/unmerged index entry: ${w}`);
}
async function clean(w: string, s?: AbortSignal) {
  await checkIndex(w, s);
  need(!(await git(w, ["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none"], s)).length, `dirty checkout; preserving ${w}`);
}
async function init(w: string, signal?: AbortSignal) {
  await git(w, ["init", "-q", "--template=", "--initial-branch=bootstrap"], signal);
  await git(w, ["config", "core.hooksPath", "/dev/null"], signal);
  await git(w, ["config", "push.default", "nothing"], signal);
}
export async function prepare(p: Paths, signal?: AbortSignal): Promise<string> {
  try {
    held(p);
    const binding = boundPr(p);
    if (!exists(join(p.state, MARKER))) {
      need(!binding?.iteration, "missing state for a previously acknowledged publication");
      need(!readdirSync(p.state).length, `refusing partial initial state: ${p.state}`);
      need(await text(p.repo, ["rev-parse", "--show-toplevel"], signal) === p.repo, `source is not an exact checkout: ${p.repo}`);
      const base = await text(p.repo, ["rev-parse", "--verify", `${p.base ?? "refs/remotes/origin/master"}^{commit}`], signal);
      need(OID.test(base) && (!p.base || p.base === base), "invalid source base");
      await command(p.state, ["/usr/bin/btrfs", "subvolume", "create", p.worktree], signal);
      subvolume(p); await init(p.worktree, signal);
      await git(p.worktree, ["fetch", "--no-tags", "--no-recurse-submodules", "--", p.repo, base], signal);
      await git(p.worktree, ["switch", "--no-track", "-c", BRANCH, "FETCH_HEAD"], signal);
      mkdirSync(join(p.state, "runs"), { mode: 0o700 });
      save(join(p.state, "iteration"), "0\n"); save(join(p.state, "queue.json"), json({ items: [] }));
      const m: Marker = { version: 1, repo: p.repo, base, tip: base, config: digest(file(join(p.worktree, ".git", "config"))), pr: binding?.pr };
      save(join(p.state, MARKER), json(m));
    }
    if (exists(join(p.state, MOVE))) await finishMove(p, signal);
    const m = await authority(p, undefined, signal); await clean(p.worktree, signal);
    return m.tip;
  } catch (e) { conflict(e); }
}

export function current(p: Paths): number {
  try {
    marker(p); const raw = file(join(p.state, "iteration")).toString().trim(); const n = Number(raw);
    need(/^(0|[1-9]\d*)$/.test(raw) && Number.isSafeInteger(n), "invalid private iteration counter"); return n;
  } catch (e) { conflict(e); }
}
function checkLastDecision(p: Paths, n = current(p)) {
  if (!n) return;
  const dir = join(p.state, "runs", String(n)); directory(dir, true);
  const result = join(dir, "result.json");
  if (p.reviewedUpstream === undefined && exists(result)) return;
  need(!readdirSync(dir).some(f => f.startsWith(".result.") || f.startsWith(".pulse-write-") || (f === "attempt.patch" && !exists(result))), `unfinished archive for iteration ${n}; preserving evidence`);
  if (p.reviewedUpstream !== undefined && exists(result)) {
    const r = JSON.parse(file(result).toString());
    need(r.iteration === n && typeof r.ok === "boolean" && r.ok === (r.commit !== null) && r.accepted_change === Number(r.ok), `invalid decision for iteration ${n}`);
    if (r.ok) {
      const path = join(dir, "publication", "receipt.json");
      need(boundPr(p)?.iteration === n && OID.test(r.commit) && exists(path) && file(path).length, `unacknowledged publication for iteration ${n}`);
    }
  }
}

type ParentMove = { old: string; new: string; iteration: number; head: string; upstream: string };
async function retained(p: Paths, oid: string, signal?: AbortSignal) {
  need(await text(p.repo, ["for-each-ref", "--contains", oid, "--count=1", "--format=%(refname)"], signal), `publisher did not retain ${oid}`);
}
async function preparedParent(p: Paths, head: string, upstream: string, parent: string, signal?: AbortSignal) {
  need(OID.test(head) && OID.test(upstream) && await text(p.repo, ["rev-parse", "--verify", `refs/pulse/parents/${head}/${upstream}`], signal) === parent, "PR parent does not match the bound fork head and official upstream");
}
async function cleanTree(w: string, sha: string, signal?: AbortSignal) {
  await clean(w, signal);
  need(await text(w, ["write-tree"], signal) === await text(w, ["rev-parse", `${sha}^{tree}`], signal), `index does not match ${sha}: ${w}`);
}
async function finishMove(p: Paths, signal?: AbortSignal) {
  const path = join(p.state, MOVE), move: ParentMove = JSON.parse(file(path).toString());
  need(boundPr(p) && OID.test(move.old) && OID.test(move.new) && move.old !== move.new && move.iteration === current(p), "invalid PR parent-move journal");
  checkLastDecision(p, move.iteration); readQueue(p);
  const w = p.worktree, { m, head, ref, attached } = await checkout(p, signal);
  // The four checkpoints are attached old, detached new/old ref, detached new/new ref, attached new.
  const atOld = attached && head === move.old, atNew = attached && head === move.new;
  need((m.tip === move.old && (atOld || atNew || (!attached && head === move.new && (ref === move.old || ref === move.new)))) ||
    (m.tip === move.new && atNew), "private checkout diverged from PR parent-move journal");
  await cleanTree(w, head, signal);
  await retained(p, move.old, signal); await preparedParent(p, move.head, move.upstream, move.new, signal);
  if (atOld) await git(w, ["switch", "--no-overwrite-ignore", "--detach", move.new], signal);
  if (ref === move.old) await git(w, ["update-ref", REF, move.new, move.old], signal);
  if (!atNew) await git(w, ["switch", "--no-overwrite-ignore", "--no-guess", BRANCH], signal);
  if (m.tip !== move.new) {
    saveQueue(p, { items: [] });
    save(join(p.state, MARKER), json({ ...m, tip: move.new }));
  }
  await authority(p, move.new, signal); await cleanTree(w, move.new, signal);
  need(!readQueue(p).items.length, "PR parent changed without invalidating its queue");
  unlinkSync(path); fsyncSync(held(p).fd);
}

/** The publisher retains both objects under its own refs. Never add a remote or a recovery branch here. */
export async function adoptPrParent(p: Paths, expectedTip: string, parent: string, signal?: AbortSignal): Promise<void> {
  try {
    held(p);
    const binding = boundPr(p);
    need(binding && OID.test(expectedTip) && OID.test(parent), "parent adoption requires a bound PR state and immutable commits");
    const path = join(p.state, MOVE);
    if (exists(path)) {
      const move: ParentMove = JSON.parse(file(path).toString());
      need(move.old === expectedTip && move.new === parent, "conflicting unfinished PR parent move");
      await finishMove(p, signal); return;
    }
    await authority(p, expectedTip, signal); await cleanTree(p.worktree, expectedTip, signal);
    checkLastDecision(p);
    await preparedParent(p, binding.head, p.reviewedUpstream!, parent, signal);
    if (parent === expectedTip) return;
    await retained(p, expectedTip, signal);
    await git(p.repo, ["merge-base", "--is-ancestor", p.reviewedUpstream!, parent], signal);
    await git(p.worktree, ["fetch", "--no-tags", "--no-recurse-submodules", "--no-write-fetch-head", "--", p.repo, parent], signal);
    need(await text(p.worktree, ["rev-parse", "--verify", `${parent}^{commit}`], signal) === parent, "fetched object is not the prepared PR parent");
    save(path, json({ old: expectedTip, new: parent, iteration: current(p), head: binding.head, upstream: p.reviewedUpstream! } satisfies ParentMove));
    await finishMove(p, signal);
  } catch (e) { conflict(e); }
}

export function next(p: Paths): number {
  try {
    const n = current(p), dir = join(p.state, "runs"); directory(dir, true);
    need(!exists(join(p.state, MOVE)), "unfinished PR parent move; prepare state before advancing");
    checkLastDecision(p, n);
    need(Number.isSafeInteger(n + 1), "iteration counter overflow");
    mkdirSync(join(dir, String(n + 1)), { mode: 0o700 }); save(join(p.state, "iteration"), `${n + 1}\n`);
    const lock = held(p); delete lock.attempt; delete lock.validated; return n + 1;
  } catch (e) { conflict(e); }
}
export function readQueue(p: Paths): Queue {
  try {
    marker(p); const q = JSON.parse(file(join(p.state, "queue.json")).toString()) as Queue;
    need(Array.isArray(q.items) && new Set(q.items.map(i => i.id)).size === q.items.length && q.items.every(i => i.status === "open" && Number.isSafeInteger(i.attempts) && i.attempts >= 0 && Array.isArray(i.notes)), "invalid private queue"); return q;
  } catch (e) { conflict(e); }
}
export function saveQueue(p: Paths, q: Queue): void {
  try { marker(p); save(join(p.state, "queue.json"), json(q)); } catch (e) { conflict(e); }
}
function runDir(p: Paths, iteration: number) {
  need(!exists(join(p.state, MOVE)), "cannot record or capture during a PR parent move");
  need(iteration > 0 && iteration === current(p), `stale iteration ${iteration}`);
  const dir = join(p.state, "runs", String(iteration)); directory(dir, true);
  need(!exists(join(dir, "result.json")) && !exists(join(dir, ".result.pending.json")), `iteration ${iteration} already recorded or interrupted`); return dir;
}
const diff = (p: Paths, base: string, s?: AbortSignal) => git(p.worktree, ["diff", "--cached", "--binary", "--full-index", "--no-ext-diff", "--no-textconv", base, "--"], s);
async function indexMatchesWorktree(w: string, s?: AbortSignal) {
  await checkIndex(w, s);
  const status = (await git(w, ["status", "--porcelain=v1", "-z", "--no-renames", "--untracked-files=all", "--ignore-submodules=none"], s)).toString().split("\0");
  need(status.every(row => !row || row[1] === " "), `worktree changed after staging; preserving ${w}`);
}
async function archived(p: Paths, a: Attempt, signal?: AbortSignal) {
  await authority(p, a.base, signal);
  need(held(p).attempt === a && current(p) === a.iteration && a.patch === join(p.state, "runs", String(a.iteration), "attempt.patch"), "foreign or stale capture");
  const bytes = file(a.patch);
  need(digest(bytes) === a.hash && bytes.equals(await diff(p, a.base, signal)) && await text(p.worktree, ["write-tree"], signal) === a.tree, "archive or staged tree changed; preserving attempt");
  await indexMatchesWorktree(p.worktree, signal); return bytes;
}
export async function capture(p: Paths, iteration: number, sha: string, signal?: AbortSignal): Promise<Attempt | null> {
  try {
    const dir = runDir(p, iteration), lock = held(p), w = p.worktree;
    need(!lock.attempt && !exists(join(dir, "attempt.patch")), "attempt already archived");
    await authority(p, sha, signal); await checkIndex(w, signal);
    need(await text(w, ["write-tree"], signal) === await text(w, ["rev-parse", `${sha}^{tree}`], signal), "private index changed before capture; refusing to restage it");
    await git(w, ["add", "-A", "--", "."], signal);
    const bytes = await diff(p, sha, signal); await indexMatchesWorktree(w, signal);
    if (!bytes.length) return null;
    const patch = join(dir, "attempt.patch"), tree = await text(w, ["write-tree"], signal);
    save(patch, bytes, true);
    const a = lock.attempt = Object.freeze({ iteration, base: sha, tree, patch, hash: digest(bytes) });
    save(join(dir, "attempt.sha256"), `${a.hash}  attempt.patch\n`, true);
    await archived(p, a, signal); return a;
  } catch (e) { conflict(e); }
}
async function checkedTree(w: string, a: Attempt, signal?: AbortSignal) {
  need(await text(w, ["rev-parse", "HEAD"], signal) === a.base && await text(w, ["write-tree"], signal) === a.tree, "independent checkout differs from captured base or tree");
  await indexMatchesWorktree(w, signal);
}
export async function verificationPaths(p: Paths, a: Attempt, signal?: AbortSignal): Promise<Paths> {
  let result: Paths;
  try {
    const bytes = await archived(p, a, signal), dir = join(runDir(p, a.iteration), "verification"), w = join(dir, "worktree");
    mkdirSync(dir, { mode: 0o700 }); mkdirSync(w, { mode: 0o700 });
    await init(w, signal); await git(w, ["fetch", "--depth=1", "--no-tags", "--no-recurse-submodules", "--", p.worktree, a.base], signal);
    await git(w, ["switch", "--detach", "FETCH_HEAD"], signal);
    await git(w, ["apply", "--index", "--binary", "--whitespace=nowarn", "-"], signal, bytes);
    await checkedTree(w, a, signal);
    result = { ...p, worktree: w, ...outputs(dir) };
  } catch (e) { conflict(e); }
  await validatePatch(p, a.base, result.worktree);
  held(p).validated = a; return result;
}

export type Report = { text: string; stopReason: string } | null;
export type LocalResult = { iteration: number; base: string; item: string | null; before: Record<string, number>; after: Record<string, number> | null; title: string | null; report: Report; patch: string | null; commit: string | null; reasons: string[]; ok: boolean; ciPass: boolean; queue_open: number; accepted_change: number };
export type RecordInput = { iteration: number; before: Analysis; item: Item | null; attempt: Attempt | null; after: Analysis | null; report: Report; reasons?: string[] };
export async function record(p: Paths, input: RecordInput, signal?: AbortSignal): Promise<LocalResult> {
  try {
    const { iteration, before, item, attempt: a, after, report } = input, w = p.worktree;
    const dir = runDir(p, iteration), m = await authority(p, before.sha, signal), lock = held(p);
    need((lock.attempt ?? null) === a && (!a || a.iteration === iteration && a.base === before.sha), "wrong captured attempt");
    const q = readQueue(p), selected = pickItem(q) ?? null;
    need((!before.buildOk && !item) || isDeepStrictEqual(selected, item), "selected work item no longer matches the queue");
    const baseTree = await text(w, ["rev-parse", `${m.tip}^{tree}`], signal);
    need(!before.buildOk || before.tree === baseTree, "baseline belongs to another tree");
    if (!a) await clean(w, signal); else await archived(p, a, signal);
    if (a && after && lock.validated === a) await checkedTree(join(dir, "verification", "worktree"), a, signal);
    let reasons = [...(input.reasons ?? [])], ok = false, commit: string | null = null;
    const title = item ? /^Title:[ \t]*(\S[^\r\n]*)/mi.exec(report?.text ?? "")?.[1]?.trim() || item.title : null;
    if (!item) {
      need(!a && !after && !report, "idle cycle has unexpected work");
      if (!reasons.length) reasons.push(before.buildOk ? "idle: queue empty" : "idle: base build failed");
    } else {
      if (report?.stopReason !== "stop" || !report.text.trim()) reasons.push("missing, blank or nonterminal Developer report");
      if (!a) reasons.push("the Developer left no changes");
      if (!before.buildOk || !after?.buildOk || !a || lock.validated !== a) reasons.push("missing complete, policy-checked verification");
      if (after && a && (after.sha !== m.tip || after.tree !== a.tree || !before.evaluator || after.evaluator !== before.evaluator)) reasons.push("verification belongs to another base, patch or evaluator");
      if (after) {
        if (p.reviewedUpstream !== undefined) {
          const failure = prCandidateFailure(after);
          if (failure && !reasons.includes(failure)) reasons.push(failure);
        }
        const keys = Object.keys(before.cases);
        if (!keys.length || before.tested !== keys.length || after.tested !== keys.length || Object.keys(after.cases).length !== keys.length || keys.some(k => !Object.hasOwn(after.cases, k) || [before.cases[k]!.outcome, after.cases[k]!.outcome].includes("NOT_RUN"))) reasons.push("before/after case identities or coverage differ");
      }
      if (!reasons.length && after) ({ ok, reasons } = judge(item, before, after));
      if (ok && a) {
        // Bind both tree and parent explicitly: never commit a newer index. update-ref below is compare-and-swap.
        commit = await text(w, ["commit-tree", a.tree, "-p", a.base, "-m", title!, "-m", `Z3-pulse-loop iteration ${iteration}; ${item.id}.`], signal);
        need(OID.test(commit), "invalid local commit object"); q.items = q.items.filter(i => i.id !== item.id);
      } else {
        selected!.attempts++; selected!.notes.push(`iteration ${iteration}: ${reasons.join("; ")}${a ? `. Patch: ${a.patch}` : ""}${report?.text ? `. Developer report: ${report.text.slice(0, 600).replace(/\s+/g, " ")}` : ""}`);
      }
    }
    const result: LocalResult = { iteration, base: m.tip, item: item?.id ?? null, before: metrics(before), after: after ? metrics(after) : null,
      title, report, patch: a?.patch ?? null, commit, reasons, ok, ciPass: after?.ciPass ?? false, queue_open: q.items.length, accepted_change: commit ? 1 : 0 };
    // Persist intent before changing refs or undoing bytes. Failure leaves the patch and pending decision for inspection.
    const pending = join(dir, ".result.pending.json"); save(pending, json(result), true);
    const bytes = a ? await archived(p, a, signal) : undefined;
    if (commit) {
      await git(w, ["update-ref", `refs/heads/${BRANCH}`, commit, m.tip], signal);
      save(join(p.state, MARKER), json({ ...m, tip: commit }));
    } else if (bytes) await git(w, ["apply", "--reverse", "--index", "--binary", "--whitespace=nowarn", "-"], signal, bytes);
    await authority(p, commit ?? m.tip, signal); await clean(w, signal);
    if (item) saveQueue(p, q);
    linkSync(pending, join(dir, "result.json")); unlinkSync(pending); return result;
  } catch (e) { conflict(e); }
}

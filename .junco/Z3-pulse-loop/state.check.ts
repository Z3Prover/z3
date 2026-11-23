import assert from "node:assert/strict";
import { execFileSync, spawnSync } from "node:child_process";
import { appendFileSync, existsSync, lstatSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import type { Analysis, Item } from "./evaluation.ts";
import { acquire, capture, current, next, paths, prepare, readQueue, record, saveQueue, StateConflict, verificationPaths } from "./state.ts";

const env = { PATH: "/usr/bin:/bin", HOME: "/nonexistent", LC_ALL: "C", GIT_CONFIG_NOSYSTEM: "1", GIT_CONFIG_GLOBAL: "/dev/null", GIT_ALLOW_PROTOCOL: "file", GIT_OPTIONAL_LOCKS: "0",
  GIT_AUTHOR_NAME: "fixture", GIT_AUTHOR_EMAIL: "fixture@localhost", GIT_COMMITTER_NAME: "fixture", GIT_COMMITTER_EMAIL: "fixture@localhost" };
const git = (cwd: string, ...args: string[]) => execFileSync("/usr/bin/git", ["-c", "core.hooksPath=/dev/null", "-c", "gc.auto=0", ...args], { cwd, env, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"] }).trimEnd();
const PIN = "b188ff772b94fd5ac51ca97efffdd368e64df151";
const example = "regressions/proofs/example.smt2", target = "src/pulse_state_fixture.cpp", protectedFile = "fstar/tools/run_checker_regressions.py";
const item: Item = { id: "reject:fixture", kind: "reject", title: "Fixture rejection", detail: "A recorded failing formula", cases: [example], attempts: 0, weight: 1, status: "open", notes: [] };
function measured(sha: string, tree: string, outcome: "REJECT" | "ACCEPT"): Analysis {
  return { sha, tree, evaluator: "pinned-fixture", buildOk: true, ciPass: true, statsCases: 1, tested: 1, counts: { [outcome]: 1 },
    families: [], pending: 0, proofNodes: 1, solveMs: 1, checkMs: 1, cases: { [example]: { outcome, wall: 1 } }, lemmas: 1, assumed: 0 };
}

/** No model, build, corpus execution, or live Git writes: use real local refs, a Btrfs seed, and the real recording path. */
export async function checkState(root: string): Promise<void> {
  const r = lstatSync(root); assert.ok(r.isDirectory() && r.uid === process.getuid!() && !(r.mode & 0o077) && realpathSync.native(root) === root);
  const fixture = mkdtempSync(join(root, "state-check-")), original = lstatSync(fixture);
  const repo = join(fixture, "source"), corpus = join(fixture, "corpus"), state = join(fixture, "state");
  const src = paths().repo, p = paths({ Z3_PULSE_LOOP_REPO: repo, Z3_PULSE_LOOP_CORPUS: corpus, Z3_PULSE_LOOP_STATE: state });
  let release: (() => void) | undefined;
  try {
    mkdirSync(repo); mkdirSync(corpus);
    git(repo, "init", "--template=", "--initial-branch=fixture");
    // Reuse only immutable objects. The synthetic root has the canonical checker files but no history to transport.
    writeFileSync(join(repo, ".git/objects/info/alternates"), `${git(src, "rev-parse", "--path-format=absolute", "--git-path", "objects")}\n`, { flag: "wx" });
    const base = git(repo, "commit-tree", git(repo, "rev-parse", `${PIN}^{tree}`), "-m", "offline fixture root");
    git(repo, "update-ref", "refs/remotes/origin/master", base);
    const foreign = join(fixture, "foreign"); mkdirSync(foreign, { mode: 0o700 }); writeFileSync(join(foreign, "sentinel"), "preserve me");
    assert.throws(() => acquire({ ...p, state: foreign, worktree: join(foreign, "worktree") }), StateConflict);
    assert.equal(readFileSync(join(foreign, "sentinel"), "utf8"), "preserve me");
    symlinkSync(foreign, join(fixture, "link"));
    assert.throws(() => acquire({ ...p, state: join(fixture, "link"), worktree: join(fixture, "link/worktree") }), StateConflict);

    release = acquire(p); assert.throws(() => acquire(p), StateConflict);
    assert.equal(spawnSync("/usr/bin/flock", ["-n", state, "/usr/bin/true"], { env }).status, 1, "another process cannot own the directory lock");
    assert.equal(await prepare(p), base); assert.equal(current(p), 0); assert.deepEqual(readQueue(p), { items: [] });
    const w = p.worktree, metadata = join(w, ".git");
    assert.ok(lstatSync(metadata).isDirectory()); assert.equal(git(w, "rev-parse", "--absolute-git-dir"), metadata);
    assert.equal(git(w, "remote"), ""); assert.equal(git(w, "config", "core.hooksPath"), "/dev/null"); assert.equal(git(w, "branch", "--show-current"), "loop/pulse-local");
    const before = measured(base, git(w, "rev-parse", "HEAD^{tree}"), "REJECT");
    const idle = await record(p, { iteration: next(p), before, item: null, attempt: null, after: null, report: null });
    assert.equal(idle.item, null); assert.equal(idle.patch, null); assert.equal(idle.commit, null); assert.equal(idle.accepted_change, 0);
    saveQueue(p, { items: [item] });
    const iteration = next(p), report = { text: "Title: Verify a fixture change\nPositive and negative case evidence.", stopReason: "stop" };
    writeFileSync(join(w, target), "// fixture one\n", { flag: "wx" });
    const a = await capture(p, iteration, base); assert.ok(a); assert.match(readFileSync(a.patch, "utf8"), /new file mode 100644/);
    const verified = await verificationPaths(p, a); assert.notEqual(verified.worktree, w); assert.notEqual(verified.checkerDir, p.checkerDir);
    assert.equal(git(verified.worktree, "rev-parse", "HEAD"), base); assert.equal(git(verified.worktree, "write-tree"), a.tree);
    assert.equal(readFileSync(join(verified.worktree, target), "utf8"), "// fixture one\n");
    const accepted = await record(p, { iteration, before, item, attempt: a, after: measured(base, a.tree, "ACCEPT"), report });
    assert.equal(accepted.ok, true); assert.equal(accepted.title, "Verify a fixture change"); assert.deepEqual(accepted.report, report); assert.ok(accepted.commit);
    assert.equal(accepted.commit, git(w, "rev-parse", "HEAD")); assert.equal(git(w, "rev-parse", "HEAD^"), base); assert.equal(git(w, "rev-parse", "HEAD^{tree}"), a.tree);
    assert.deepEqual(accepted, JSON.parse(readFileSync(join(state, "runs", String(iteration), "result.json"), "utf8")));
    assert.deepEqual(readQueue(p).items, []); assert.equal(git(w, "status", "--porcelain"), "");
    assert.equal(git(repo, "rev-parse", "refs/remotes/origin/master"), base, "source ref unchanged");
    release(); release = acquire(p); const tip = await prepare(p); assert.equal(tip, accepted.commit);
    const b2 = measured(tip, a.tree, "REJECT"); saveQueue(p, { items: [item] });
    const ii = next(p); appendFileSync(join(w, target), "// fixture two\n");
    const failed = await capture(p, ii, tip); assert.ok(failed); await verificationPaths(p, failed);
    const rejected = await record(p, { iteration: ii, item, before: b2, attempt: failed, after: measured(tip, failed.tree, "REJECT"), report });
    assert.equal(rejected.ok, false); assert.equal(rejected.commit, null); assert.ok(existsSync(failed.patch)); assert.equal(rejected.patch, failed.patch);
    assert.match(rejected.reasons.join(" "), /neither the targeted item nor the corpus improved/);
    assert.equal(readQueue(p).items[0]!.attempts, 1); assert.match(readQueue(p).items[0]!.notes[0]!, /attempt\.patch/);
    assert.equal(readFileSync(join(w, target), "utf8"), "// fixture one\n"); assert.equal(git(w, "status", "--porcelain"), ""); assert.equal(await prepare(p), tip);

    const iii = next(p), queued = readQueue(p).items[0]!;
    const protectedBytes = readFileSync(join(w, protectedFile));
    writeFileSync(join(w, protectedFile), Buffer.from([0, 32, 255, 0, 1])); const forbidden = await capture(p, iii, tip); assert.ok(forbidden);
    const binary = readFileSync(forbidden.patch, "utf8"); assert.match(binary, /GIT binary patch/); assert.match(binary, /index [0-9a-f]{40}\.\.[0-9a-f]{40}/);
    let reason = "";
    await assert.rejects(verificationPaths(p, forbidden), e => { assert.ok(e instanceof Error && !(e instanceof StateConflict)); reason = e.message; return true; });
    const protectedResult = await record(p, { iteration: iii, item: queued, before: b2, attempt: forbidden, after: null, report, reasons: [reason] });
    assert.equal(protectedResult.ok, false); assert.ok(protectedResult.reasons.includes(reason)); assert.ok(existsSync(forbidden.patch));
    assert.deepEqual(readFileSync(join(w, protectedFile)), protectedBytes);
    assert.equal(git(w, "status", "--porcelain"), ""); assert.equal(await prepare(p), tip);

    const iv = next(p); appendFileSync(join(w, target), "// fixture negative controls\n");
    const bad = await capture(p, iv, tip); assert.ok(bad); await verificationPaths(p, bad);
    const stale = await record(p, { iteration: iv, item: readQueue(p).items[0]!, before: b2, attempt: bad, report: { text: "  ", stopReason: "aborted" },
      after: { ...measured(base, a.tree, "ACCEPT"), cases: { "unexpected.smt2": { outcome: "ACCEPT", wall: 1 } } } });
    assert.equal(stale.ok, false); assert.equal(stale.commit, null); assert.match(stale.reasons.join(";"), /report/); assert.match(stale.reasons.join(";"), /case identities/); assert.match(stale.reasons.join(";"), /another base/);
    assert.equal(await prepare(p), tip);

    const v = next(p); appendFileSync(join(w, target), "// captured, not approved\n"); const interrupted = await capture(p, v, tip); assert.ok(interrupted);
    writeFileSync(join(w, "external.txt"), "external work\n", { flag: "wx" });
    await assert.rejects(record(p, { iteration: v, item: readQueue(p).items[0]!, before: b2, attempt: interrupted, after: null, report }), StateConflict);
    assert.equal(git(w, "rev-parse", "HEAD"), tip); assert.ok(existsSync(interrupted.patch)); assert.ok(!existsSync(join(state, "runs", String(v), "result.json")));
    assert.match(readFileSync(join(w, target), "utf8"), /captured, not approved/); assert.equal(readFileSync(join(w, "external.txt"), "utf8"), "external work\n");
    release(); release = acquire(p); await assert.rejects(prepare(p), StateConflict); assert.ok(existsSync(join(w, "external.txt")));
    assert.equal(git(w, "remote"), ""); release(); release = undefined;
    assert.equal(spawnSync("/usr/bin/flock", ["-n", state, "/usr/bin/true"], { env }).status, 0, "lock released on close");
    const now = lstatSync(fixture); assert.equal(now.ino, original.ino); assert.equal(now.dev, original.dev); assert.equal(realpathSync.native(w), w);
    execFileSync("/usr/bin/btrfs", ["subvolume", "delete", w], { env, stdio: "pipe" }); rmSync(fixture, { recursive: true });
  } catch (e) { console.error(`retained private state fixture: ${fixture}`); throw e; }
  finally { release?.(); }
}

/**
 * Reconciling a run that ended without persisting its outcomes (`continuity.ts
 * --reconcile-policy-blocked`). Run b9bdecb3 was stopped by killing its process: its journal row
 * still says `running`, but nothing renews its lease, so Atomic reports it `crashed`. These tests
 * use a real journal file holding a `running` run, its preflight checkpoint and its repair stages'
 * sessions, and a scratch repository with the run's slice branches.
 */
import { describe, expect, test } from "bun:test";
import { execFileSync, spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { atomicEntryPath } from "../lib/atomic-host.ts";
import { evaluateContinuity } from "../lib/continuity.ts";
import type { Finding } from "../lib/reports.ts";
import { inspectedRunStatus } from "../lib/stage-sessions.ts";
import { claimFindings, countUnprocessed, eligibleStateFindings, emptyState, readState, recordSeen, triageFindings, writeJsonAtomic } from "../lib/state.ts";

const launcher = join(import.meta.dir, "..", "continuity.ts");
const CYBER = 'github-copilot API error (422): {"message":"This content was flagged for possible cybersecurity risk.","code":"cyber_policy"}';
const RUN_KEY = "20261026T124947Z-test";
const RUN_ID = "b9bdecb3-0000-4000-8000-000000000001";

function finding(fingerprint: string): Finding {
  return {
    fingerprint, kind: "partial-rule", theory: "bitvectors", checker: "ocaml", rule: "rewrite", detail: `family ${fingerprint}`,
    affectedProofs: 2, obligations: 3, soleFamilyProofs: 1, examples: ["QF_BV/a.smt2"], evidence: ["results.jsonl"], sources: ["pulse-run:1-1"],
  };
}

/** The run's slices: a policy-blocked repair, a repair that committed unverified work, and one that committed nothing. */
const SLICES = [
  { id: "bitvectors-crash", fingerprints: ["h1", "h2"], error: CYBER },
  { id: "bitvectors-performance", fingerprints: ["c1", "c2"], commit: true },
  { id: "uf-crash", fingerprints: ["p1"] },
] as const;
const branchOf = (slice: string) => `fstar-proof-checking/work/${RUN_KEY}/i1-${slice}`;

/** A scratch repository whose slice branches start at `main`; only the committing slice is ahead of it. */
function repository(root: string): { repo: string; commit: string } {
  const repo = join(root, "repo");
  mkdirSync(repo, { recursive: true });
  const git = (...args: string[]) => execFileSync("git", args, { cwd: repo, encoding: "utf8" }).trim();
  git("init", "-q", "-b", "main");
  git("config", "user.email", "test@example.com");
  git("config", "user.name", "Test");
  git("commit", "-q", "--allow-empty", "-m", "base");
  for (const slice of SLICES) git("branch", branchOf(slice.id), "main");
  git("checkout", "-q", branchOf("bitvectors-performance"));
  git("commit", "-q", "--allow-empty", "-m", "Isolate bitvector append arithmetic");
  const commit = git("rev-parse", "HEAD");
  git("checkout", "-q", "main");
  return { repo, commit };
}

/**
 * A journal file with a `running` run whose lease was last renewed `leaseAgeMs` ago on the journal
 * clock (a stopped executor stops renewing it), its preflight checkpoint, and one repair stage per
 * slice whose session ends on the slice's provider error or on a normal answer.
 */
function journal(path: string, runDir: string, leaseAgeMs: number): void {
  // Paths from the package's exports: require.resolve would return a bare specifier once another test file registered the host modules.
  const atomic = pathToFileURL(atomicEntryPath(".")).href;
  const workflows = pathToFileURL(atomicEntryPath("./workflows")).href;
  const stages = SLICES.map((slice) => ({ stage: `iter-1/${slice.id}/repair`, error: "error" in slice ? slice.error : undefined }));
  const script = `
    import { DatabaseSync } from "node:sqlite";
    const atomic = await import(${JSON.stringify(atomic)});
    const { openSqlRunJournal, JOURNAL_TABLES, JOURNAL_COLUMNS } = await import(${JSON.stringify(workflows)});
    const connection = new DatabaseSync(${JSON.stringify(path)});
    const store = await atomic.resolveSessionStore(process.cwd(), { sessionStore: { kind: "database", database: atomic.wrapNodeSqliteDatabase(connection) } });
    const usage = { input: 0, output: 0, cacheRead: 0, cacheWrite: 0, totalTokens: 0, cost: { input: 0, output: 0, cacheRead: 0, cacheWrite: 0, total: 0 } };
    const sessions = [];
    for (const { error } of ${JSON.stringify(stages)}) {
      const session = await atomic.SessionManager.create(store, process.cwd());
      await session.appendMessage({ role: "user", content: [{ type: "text", text: "repair the slice" }], timestamp: Date.now() });
      const end = error ? { content: [], stopReason: "error", errorMessage: error } : { content: [{ type: "text", text: "slice report" }], stopReason: "stop" };
      await session.appendMessage({ role: "assistant", api: "openai-responses", provider: "github-copilot", model: "gpt-5", usage, timestamp: Date.now(), ...end });
      sessions.push(session.getSessionId());
    }
    await store.close();
    const journal = await openSqlRunJournal(connection);
    const runId = ${JSON.stringify(RUN_ID)};
    await journal.createRun({ runId, name: "fstar-proof-checking", cwd: process.cwd(), createdAt: Date.now(), status: "running" });
    const { lease } = await journal.acquire(runId, "executor-that-was-stopped");
    await journal.append(lease, { type: "CheckpointRecorded", payload: { kind: "tool", name: "preflight", checkpointId: "tool:preflight", output: { runKey: ${JSON.stringify(RUN_KEY)}, runDir: ${JSON.stringify(runDir)} } } });
    for (const [index, { stage }] of ${JSON.stringify(stages)}.entries()) {
      await journal.append(lease, { type: "CheckpointRecorded", payload: { kind: "stage", name: stage, checkpointId: "task:" + stage, output: { sessionId: sessions[index] } } });
    }
    // Journal tables carry the wf_ prefix; renewed_at is on the journal (database) clock.
    connection.prepare("UPDATE wf_" + JOURNAL_TABLES.leases + " SET " + JOURNAL_COLUMNS.renewedAt + " = " + JOURNAL_COLUMNS.renewedAt + " - ? WHERE " + JOURNAL_COLUMNS.runId + " = ?").run(${leaseAgeMs}, runId);
    await journal.close();
    connection.close();
  `;
  const result = spawnSync("node", ["--input-type=module", "-e", script], { encoding: "utf8" });
  if (result.status !== 0) throw new Error(`journal fixture failed: ${result.stderr}`);
}

/** State in which the run claimed its slices' findings; `o1` is open and `x1` is claimed by another run. */
function fixture(leaseAgeMs: number) {
  const root = mkdtempSync(join(tmpdir(), "fpc-reconcile-"));
  const { repo, commit } = repository(root);
  const stateDir = join(root, "state");
  const runDir = join(stateDir, "runs", RUN_KEY);
  mkdirSync(join(runDir, "iter-1"), { recursive: true });
  writeFileSync(join(runDir, "setup.json"), JSON.stringify({ setup: { repoRoot: repo, stateDir, runKey: RUN_KEY, runDir }, inputs: { baseRef: "main" } }));
  writeFileSync(join(runDir, "iter-1", "plan.json"), JSON.stringify({ slices: SLICES.map((slice) => ({ id: slice.id, branch: branchOf(slice.id), fingerprints: slice.fingerprints })) }));
  const claimed = SLICES.flatMap((slice) => slice.fingerprints.map(finding));
  const at = new Date();
  let state = recordSeen(emptyState(), [...claimed, finding("o1"), finding("x1")], at);
  state = claimFindings(state, claimed, { runKey: RUN_KEY, now: at });
  state = claimFindings(state, [finding("x1")], { runKey: "20261026T150000Z-live", now: at });
  writeJsonAtomic(join(stateDir, "state.json"), state);
  const database = join(root, "journal.sqlite");
  journal(database, runDir, leaseAgeMs);
  return { root, repo, commit, stateDir, statePath: join(stateDir, "state.json"), database, before: state };
}

function cli(fx: ReturnType<typeof fixture>, ...args: string[]) {
  const result = spawnSync(process.execPath, [launcher, ...args, "--state-dir", fx.stateDir], { encoding: "utf8" });
  return { code: result.status, report: JSON.parse(result.stdout) as Record<string, unknown>, stderr: result.stderr };
}
const reconcile = (fx: ReturnType<typeof fixture>, ...extra: string[]) => cli(fx, "--reconcile-policy-blocked", RUN_ID, "--journal", fx.database, ...extra);

describe("reconciling a run whose executor was stopped", () => {
  test("an expired lease means the run crashed: policy-blocked findings are held, committed work is kept as a candidate, other claims are released, and a second run is a no-op", () => {
    const fx = fixture(3 * 60_000);
    const { code, report, stderr } = reconcile(fx);
    const candidate = { runKey: RUN_KEY, branch: branchOf("bitvectors-performance"), commit: fx.commit };
    expect({ code, stderr: stderr.match(/Error.*/)?.[0], ...report }).toMatchObject({
      code: 0, stderr: undefined, runStatus: "crashed", journalStatus: "running", applied: true,
      held: ["h1", "h2"],
      candidates: [{ fingerprint: "c1", candidate }, { fingerprint: "c2", candidate }],
      released: ["p1"],
    });
    const after = readState(fx.stateDir).findings;
    // (a) held with the stage's evidence, no attempt, no backoff, no claim.
    for (const fingerprint of ["h1", "h2"]) {
      expect(after[fingerprint]).toMatchObject({ status: "provider_policy_blocked", attempts: 0, providerBlock: { runKey: RUN_KEY, runId: RUN_ID, stage: "iter-1/bitvectors-crash/repair", code: "cyber_policy" } });
      expect(after[fingerprint]?.providerBlock?.sessionId).toEqual(expect.any(String));
      expect([after[fingerprint]?.nextEligibleAt, after[fingerprint]?.claimedBy, after[fingerprint]?.claimedAt]).toEqual([undefined, undefined, undefined]);
    }
    // (b) the other interrupted claim is released: open, no attempt, no backoff.
    expect(after.p1).toMatchObject({ status: "open", attempts: 0 });
    expect([after.p1?.nextEligibleAt, after.p1?.claimedBy, after.p1?.claimedAt, after.p1?.candidate]).toEqual([undefined, undefined, undefined, undefined]);
    // (c) the committed slice's findings are released with the candidate recorded.
    for (const fingerprint of ["c1", "c2"]) {
      expect(after[fingerprint]).toMatchObject({ status: "open", attempts: 0, candidate });
      expect([after[fingerprint]?.nextEligibleAt, after[fingerprint]?.claimedBy]).toEqual([undefined, undefined]);
    }
    // Findings this run did not claim are untouched.
    expect(after.o1).toEqual(fx.before.findings.o1!);
    expect(after.x1).toEqual(fx.before.findings.x1!);
    // (d) applying it again changes nothing.
    const bytes = readFileSync(fx.statePath);
    const again = reconcile(fx);
    expect(again.code).toBe(0);
    expect(again.report).toMatchObject({ runStatus: "crashed", applied: false, held: [], candidates: [], released: [] });
    expect(readFileSync(fx.statePath).equals(bytes)).toBe(true);
  }, 120_000);

  test("a live lease is refused: the run is still running and state.json is not touched, also with --dry-run", () => {
    const fx = fixture(0);
    const bytes = readFileSync(fx.statePath);
    const { code, report } = reconcile(fx);
    expect({ code, ...report }).toMatchObject({ code: 1, runStatus: "running", journalStatus: "running", applied: false, wouldHold: ["h1", "h2"] });
    expect(report.reason).toMatch(/is running \(its lease was renewed \d+ s ago on the journal clock\): state\.json is not changed until it ends/);
    expect(report).not.toHaveProperty("released");
    const dry = reconcile(fx, "--dry-run");
    expect({ code: dry.code, ...dry.report }).toMatchObject({ code: 0, runStatus: "running", applied: false });
    expect(readFileSync(fx.statePath).equals(bytes)).toBe(true);
  }, 120_000);

  test("candidates stay out of triage, re-sourcing and the continuity retrigger until an operator releases them with a decision", () => {
    const fx = fixture(3 * 60_000);
    expect(reconcile(fx).code).toBe(0);
    // Two days later every claim would have expired; candidates are still not picked up, even with new evidence.
    const later = new Date(Date.now() + 48 * 3_600_000);
    const state = recordSeen(readState(fx.stateDir), [{ ...finding("c1"), examples: ["QF_BV/new.smt2"] }], later);
    expect(triageFindings(["c1", "c2", "p1"].map(finding), state, { now: later })).toMatchObject({ actionable: [{ fingerprint: "p1" }], skipped: { candidate: 2 } });
    expect(eligibleStateFindings(state, later).map((item) => item.fingerprint).sort()).toEqual(["o1", "p1", "x1"]);
    const onlyCandidates = { ...state, findings: { c1: state.findings.c1!, c2: state.findings.c2! } };
    expect(countUnprocessed(onlyCandidates, later, "partial-rule")).toBe(0);
    expect(evaluateContinuity({ runs: [], state: onlyCandidates, now: later, buildEvidence: [] }).retrigger).toBe(false);

    expect(() => execFileSync(process.execPath, [launcher, "--release-candidate", "c1", "--state-dir", fx.stateDir], { stdio: "pipe" })).toThrow(/requires --decision/);
    const decision = `verified ${fx.commit.slice(0, 9)}: rejected after the open-PR review; repair again`;
    const preview = cli(fx, "--release-candidate", "c1,o1", "--decision", decision, "--dry-run");
    expect(preview.report).toMatchObject({ applied: false, released: ["c1"], notCandidates: ["o1"] });
    const released = cli(fx, "--release-candidate", "c1,o1", "--decision", decision);
    expect(released.report).toMatchObject({ applied: true, released: ["c1"], notCandidates: ["o1"] });
    const after = readState(fx.stateDir).findings;
    expect(after.c1).toMatchObject({ status: "open", attempts: 0 });
    expect(after.c1?.candidate).toBeUndefined();
    expect(after.c1?.transitions?.at(-1)).toMatchObject({ from: "open", to: "open", reason: expect.stringContaining(decision), candidate: { commit: fx.commit } });
    expect(after.c2?.candidate).toMatchObject({ commit: fx.commit });
    expect(triageFindings([finding("c1"), finding("c2")], readState(fx.stateDir), { now: later }).actionable.map((item) => item.fingerprint)).toEqual(["c1"]);
    expect(cli(fx, "--release-candidate", "c1", "--decision", decision).report).toMatchObject({ applied: false, released: [], notCandidates: ["c1"] });
  }, 120_000);
});

describe("run liveness", () => {
  test("a running run has crashed once its lease is unheld or older than Atomic's two-minute expiry on the journal clock", () => {
    const lease = (ageMs: number) => ({ holderId: "executor", renewedAt: 0, ageMs });
    expect(inspectedRunStatus("running", lease(5_000))).toBe("running");
    // Atomic's expiry is strict: a lease exactly at the window is still live.
    expect(inspectedRunStatus("running", lease(120_000))).toBe("running");
    expect(inspectedRunStatus("running", lease(120_001))).toBe("crashed");
    expect(inspectedRunStatus("running", undefined)).toBe("crashed");
    // Other statuses are the journal's, whatever the lease.
    expect(inspectedRunStatus("paused", undefined)).toBe("paused");
    expect(inspectedRunStatus("completed", lease(10 * 60_000))).toBe("completed");
  });
});

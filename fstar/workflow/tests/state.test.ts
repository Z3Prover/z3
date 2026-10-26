import { afterEach, beforeEach, describe, expect, test } from "bun:test";
import { mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { hostname, tmpdir } from "node:os";
import { join } from "node:path";
import type { Finding } from "../lib/reports.ts";
import {
  acquireLock,
  claimFindings,
  countUnprocessed,
  emptyState,
  readState,
  recordOutcomes,
  recordSeen,
  triageFindings,
  withStateLock,
} from "../lib/state.ts";

let dir: string;
beforeEach(() => {
  dir = mkdtempSync(join(tmpdir(), "fpc-state-"));
});
afterEach(() => rmSync(dir, { recursive: true, force: true }));

function finding(overrides: Partial<Finding> = {}): Finding {
  return {
    fingerprint: "f1",
    kind: "partial-rule",
    theory: "arrays",
    checker: "ocaml",
    rule: "rewrite",
    detail: "eq(store:Array(...) -> ...)",
    affectedProofs: 3,
    obligations: 5,
    soleFamilyProofs: 1,
    examples: ["QF_AX/a.smt2"],
    evidence: ["results.jsonl"],
    sources: ["pulse-run:1-1"],
    ...overrides,
  };
}

const now = new Date("2026-10-26T10:00:00Z");
const hours = (n: number) => new Date(now.getTime() + n * 3_600_000);

describe("state lock", () => {
  test("a held lock blocks a second owner until released", async () => {
    const release = await acquireLock(join(dir, "state.lock"), { owner: "a" });
    await expect(acquireLock(join(dir, "state.lock"), { owner: "b", timeoutMs: 150 })).rejects.toThrow(/locked by a/);
    release();
    const again = await acquireLock(join(dir, "state.lock"), { owner: "b", timeoutMs: 150 });
    again();
  });

  test("a lock older than the stale bound is reclaimed", async () => {
    writeFileSync(join(dir, "state.lock"), JSON.stringify({ owner: "crashed", pid: process.pid, host: hostname(), acquiredAt: 0 }));
    const release = await acquireLock(join(dir, "state.lock"), { owner: "b", timeoutMs: 150, staleMs: 1000 });
    expect(JSON.parse(readFileSync(join(dir, "state.lock"), "utf8")).owner).toBe("b");
    release();
  });

  test("a lock left by a dead process on this host is reclaimed", async () => {
    writeFileSync(join(dir, "state.lock"), JSON.stringify({ owner: "dead", pid: 2 ** 22 + 12345, host: hostname(), acquiredAt: Date.now() }));
    const release = await acquireLock(join(dir, "state.lock"), { owner: "b", timeoutMs: 150 });
    release();
  });

  test("a failing mutation leaves the previous state and releases the lock", async () => {
    await withStateLock(dir, (state) => ({ state: { ...state, localScans: { a: { at: "x", offset: 1 } } }, result: undefined }));
    await expect(withStateLock(dir, () => { throw new Error("boom"); })).rejects.toThrow("boom");
    expect(readState(dir).localScans).toEqual({ a: { at: "x", offset: 1 } });
    expect(readdirSync(dir).sort()).toEqual(["state.json"]);
  });

  test("concurrent processes serialize read-modify-write updates", async () => {
    const script = join(dir, "increment.ts");
    const stateModule = join(import.meta.dir, "..", "lib", "state.ts").replaceAll("\\", "/");
    writeFileSync(script, [
      `import { withStateLock } from ${JSON.stringify(stateModule)};`,
      `for (let i = 0; i < 10; i++) {`,
      `  await withStateLock(${JSON.stringify(dir)}, (state) => {`,
      `    const offset = (state.localScans.counter?.offset ?? 0) + 1;`,
      `    return { state: { ...state, localScans: { counter: { at: "now", offset } } }, result: offset };`,
      `  }, { owner: "worker-" + process.pid, timeoutMs: 60000 });`,
      `}`,
    ].join("\n"));
    const workers = Array.from({ length: 4 }, () => Bun.spawn([process.execPath, script], { stdout: "pipe", stderr: "pipe" }));
    const codes = await Promise.all(workers.map((worker) => worker.exited));
    const errors = await Promise.all(workers.map((worker) => new Response(worker.stderr).text()));
    expect({ codes, errors: errors.filter(Boolean) }).toEqual({ codes: [0, 0, 0, 0], errors: [] });
    expect(readState(dir).localScans.counter?.offset).toBe(40);
    expect(readdirSync(dir).filter((name) => name.includes(".tmp"))).toEqual([]);
  }, 60_000);
});

describe("triage and outcome bookkeeping", () => {
  test("new findings are actionable and sorted by priority", () => {
    const crash = finding({ fingerprint: "c", kind: "crash", affectedProofs: 1 });
    const big = finding({ fingerprint: "big", soleFamilyProofs: 9 });
    const small = finding({ fingerprint: "small", soleFamilyProofs: 0 });
    const result = triageFindings([small, big, crash], emptyState(), { now });
    expect(result.actionable.map((f) => f.fingerprint)).toEqual(["c", "big", "small"]);
  });

  test("resolved findings are not reprocessed", () => {
    let state = claimFindings(recordSeen(emptyState(), [finding()], now), [finding()], { runKey: "r1", now });
    state = recordOutcomes(state, [{ fingerprint: "f1", status: "verified", note: "fixed" }], { runKey: "r1", now });
    expect(state.findings.f1?.status).toBe("resolved");
    expect(triageFindings([finding()], state, { now: hours(100) }).skipped).toEqual({ resolved: 1 });
  });

  test("failed attempts back off exponentially and block after the attempt limit", () => {
    let state = recordSeen(emptyState(), [finding()], now);
    const attempt = (at: Date) => {
      state = claimFindings(state, [finding()], { runKey: "r", now: at });
      state = recordOutcomes(state, [{ fingerprint: "f1", status: "unverified", note: "toolchain missing" }], { runKey: "r", now: at, backoffHours: 6, maxAttempts: 3 });
    };
    attempt(now);
    expect(triageFindings([finding()], state, { now: hours(5) }).skipped).toEqual({ backoff: 1 });
    expect(triageFindings([finding()], state, { now: hours(6) }).actionable).toHaveLength(1);
    attempt(hours(6));
    expect(triageFindings([finding()], state, { now: hours(17) }).skipped).toEqual({ backoff: 1 });
    attempt(hours(18));
    expect(state.findings.f1?.status).toBe("blocked");
    expect(triageFindings([finding()], state, { now: hours(1000) }).skipped).toEqual({ blocked: 1 });
    const changed = finding({ examples: ["QF_AX/new-evidence.smt2"] });
    expect(triageFindings([changed], recordSeen(state, [changed], hours(1000)), { now: hours(1000) }).actionable).toHaveLength(1);
  });

  test("claims exclude concurrent runs until they expire", () => {
    const state = claimFindings(recordSeen(emptyState(), [finding()], now), [finding()], { runKey: "other", now });
    expect(triageFindings([finding()], state, { now: hours(1) }).skipped).toEqual({ claimed: 1 });
    expect(triageFindings([finding()], state, { now: hours(25), claimTtlMs: 24 * 3_600_000 }).actionable).toHaveLength(1);
  });

  test("theory filters and in-run exclusions are honored", () => {
    const bv = finding({ fingerprint: "bv", theory: "bitvectors" });
    const result = triageFindings([finding(), bv], emptyState(), { now, theories: ["bitvectors"], exclude: new Set(["bv"]) });
    expect(result.actionable).toEqual([]);
    expect(result.skipped).toEqual({ "theory-filter": 1, "planned-this-run": 1 });
  });

  test("unprocessed counts include eligible open and retryable findings only", () => {
    let state = recordSeen(emptyState(), [finding(), finding({ fingerprint: "slow", kind: "slow-obligation" })], now);
    expect(countUnprocessed(state, now, "partial-rule")).toBe(1);
    state = claimFindings(state, [finding()], { runKey: "r", now });
    state = recordOutcomes(state, [{ fingerprint: "f1", status: "rejected", note: "admit introduced" }], { runKey: "r", now });
    expect(countUnprocessed(state, hours(1), "partial-rule")).toBe(0);
    expect(countUnprocessed(state, hours(7), "partial-rule")).toBe(1);
  });
});

/**
 * Provider failures of agent stages: classification, the held `provider_policy_blocked` status,
 * its exclusion from triage and the continuity retrigger, the explicit requeue, and the
 * reconciliation of outcomes that an older workflow version recorded for policy-blocked stages.
 */
import { describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { evaluateContinuity } from "../lib/continuity.ts";
import { classifyProviderError, policyHoldsFromRun, terminalAssistantFailure } from "../lib/provider.ts";
import type { Finding } from "../lib/reports.ts";
import {
  claimFindings,
  countUnprocessed,
  eligibleStateFindings,
  emptyState,
  holdPolicyBlocked,
  recordOutcomes,
  recordSeen,
  requeuePolicyBlocked,
  triageFindings,
  type ProviderBlock,
} from "../lib/state.ts";

const CYBER = "This content was flagged for possible cybersecurity risk. If this seems wrong, try rephrasing your request.";
/** The two shapes run b9bdecb3 recorded: an HTTP 422 body, and the same rejection inside a stream-wrapper error. */
const HTTP_REJECTION = `github-copilot API error (422): {"message":"${CYBER}","code":"cyber_policy"}`;
const STREAM_REJECTION = `reading rate-limited responses stream: reading program fingerprint response stream: reading SSE event: {"error":{"message":"${CYBER}","code":"cyber_policy"}}`;

function finding(fingerprint: string, overrides: Partial<Finding> = {}): Finding {
  return {
    fingerprint, kind: "partial-rule", theory: "arrays", checker: "ocaml", rule: "rewrite", detail: `family ${fingerprint}`,
    affectedProofs: 2, obligations: 3, soleFamilyProofs: 1, examples: ["QF_AX/a.smt2"], evidence: ["results.jsonl"], sources: ["pulse-run:1-1"],
    ...overrides,
  };
}

const now = new Date("2026-10-26T13:00:00Z");
const hours = (n: number) => new Date(now.getTime() + n * 3_600_000);
const block = (runKey: string, stage = "iter-1/arrays-repair/repair"): ProviderBlock => ({
  runKey, stage, sessionId: "01a1784c-f0ae-7202-a146-9ba4080cc028", code: "cyber_policy", error: HTTP_REJECTION, at: now.toISOString(),
});

describe("provider failure classification", () => {
  test("cyber_policy is a policy rejection, also inside a stream wrapper that mentions rate limiting", () => {
    for (const message of [HTTP_REJECTION, STREAM_REJECTION]) {
      expect(classifyProviderError(message)).toMatchObject({ kind: "provider-policy-blocked", code: "cyber_policy" });
    }
  });

  test("transport and availability errors are provider-unavailable", () => {
    expect(classifyProviderError("OpenAI Responses stream ended before a terminal response event").kind).toBe("provider-unavailable");
    expect(classifyProviderError('github-copilot API error (429): {"message":"rate limited","code":"rate_limit_exceeded"}')).toMatchObject({ kind: "provider-unavailable", code: "rate_limit_exceeded" });
  });

  test("only a session whose last assistant message ended on an error is a provider failure", () => {
    const failed = { role: "assistant", content: [], stopReason: "error", errorMessage: HTTP_REJECTION };
    const answered = { role: "assistant", content: [{ type: "text", text: "report" }], stopReason: "stop" };
    expect(terminalAssistantFailure([{ role: "user" }, failed, { role: "toolResult" }])).toBe(HTTP_REJECTION);
    // A retried transient error followed by a normal answer is not a failure.
    expect(terminalAssistantFailure([failed, { role: "user" }, answered])).toBeUndefined();
  });
});

describe("held provider-policy-blocked findings", () => {
  function held() {
    const state = claimFindings(recordSeen(emptyState(), [finding("f1"), finding("f2")], now), [finding("f1"), finding("f2")], { runKey: "r1", now });
    return recordOutcomes(state, [
      { fingerprint: "f1", status: "provider-policy-blocked", note: "repair stage rejected by the provider", provider: block("r1") },
      { fingerprint: "f2", status: "provider-unavailable", note: "stream ended before a terminal response event" },
    ], { runKey: "r1", now });
  }

  test("a policy-blocked outcome holds the finding with evidence, no attempt and no backoff", () => {
    const record = held().findings.f1;
    expect(record).toMatchObject({ status: "provider_policy_blocked", attempts: 0, providerBlock: block("r1") });
    expect(record?.nextEligibleAt).toBeUndefined();
    expect(record?.claimedBy).toBeUndefined();
  });

  test("a provider-unavailable outcome reopens the finding with no attempt and no backoff", () => {
    const record = held().findings.f2;
    expect(record).toMatchObject({ status: "open", attempts: 0 });
    expect(record?.nextEligibleAt).toBeUndefined();
    expect(record?.lastOutcome).toMatch(/^provider-unavailable:/);
  });

  test("held findings are excluded from triage, re-sourcing and the continuity retrigger, even with new evidence", () => {
    const state = recordSeen(held(), [finding("f1", { examples: ["QF_AX/new.smt2"] })], hours(1000));
    expect(triageFindings([finding("f1", { examples: ["QF_AX/new.smt2"] })], state, { now: hours(1000) }).skipped).toEqual({ "provider-policy-blocked": 1 });
    expect(eligibleStateFindings(state, hours(1000)).map((item) => item.fingerprint)).toEqual(["f2"]);
    expect(countUnprocessed(state, hours(1000), "partial-rule")).toBe(1);
    const decision = evaluateContinuity({ runs: [], state: { ...state, findings: { f1: state.findings.f1! } }, now: hours(1000), buildEvidence: [] });
    expect(decision.retrigger).toBe(false);
  });

  test("an explicit requeue reopens held findings and keeps the evidence in the transition", () => {
    const one = requeuePolicyBlocked(held(), ["f1", "f2"], hours(2));
    expect(one.requeued).toEqual(["f1"]);
    expect(one.notHeld).toEqual(["f2"]);
    expect(one.state.findings.f1).toMatchObject({ status: "open", attempts: 0 });
    expect(one.state.findings.f1?.providerBlock).toBeUndefined();
    expect(one.state.findings.f1?.transitions?.at(-1)).toMatchObject({ from: "provider_policy_blocked", to: "open", providerBlock: block("r1") });
    expect(triageFindings([finding("f1")], one.state, { now: hours(2) }).actionable).toHaveLength(1);
    expect(requeuePolicyBlocked(held(), "all", hours(2)).requeued).toEqual(["f1"]);
  });
});

describe("reconciling outcomes an older version recorded for policy-blocked stages", () => {
  /** What the old code's persist does to a policy-blocked slice: an `unverified`/`no-change` attempt with backoff. */
  function oldCode() {
    let state = recordSeen(emptyState(), [finding("a1"), finding("a2"), finding("v1"), finding("later")], now);
    state = claimFindings(state, [finding("a1"), finding("a2"), finding("v1"), finding("later")], { runKey: "old", now });
    state = recordOutcomes(state, [
      { fingerprint: "a1", status: "no-change", note: "the slice produced no committed changes" },
      { fingerprint: "v1", status: "verified", note: "verified" },
      { fingerprint: "later", status: "unverified", note: "no verdict" },
    ], { runKey: "old", now });
    // "later" was attempted again by a newer run; a2 stays claimed (the old run ended before persisting it).
    state = claimFindings(state, [finding("later")], { runKey: "newer", now: hours(7) });
    return recordOutcomes(state, [{ fingerprint: "later", status: "unverified", note: "genuine failure" }], { runKey: "newer", now: hours(7) });
  }

  test("only findings whose outcome that run recorded are held, with its attempt and backoff undone", () => {
    const before = oldCode();
    expect(before.findings.a1).toMatchObject({ status: "unverified", attempts: 1 });
    const result = holdPolicyBlocked(before, ["a1", "a2", "v1", "later", "gone"].map((fingerprint) => ({ fingerprint, block: block("old") })), hours(8));
    expect(result.held).toEqual(["a1", "a2"]);
    expect(result.state.findings.a1).toMatchObject({ status: "provider_policy_blocked", attempts: 0, providerBlock: block("old") });
    expect(result.state.findings.a1?.nextEligibleAt).toBeUndefined();
    expect(result.state.findings.a2).toMatchObject({ status: "provider_policy_blocked", attempts: 0 });
    expect(result.state.findings.a2?.claimedBy).toBeUndefined();
    expect(result.state.findings.v1?.status).toBe("integrated");
    expect(result.state.findings.later).toEqual(before.findings.later);
    expect(result.unchanged.map((item) => item.fingerprint)).toEqual(["v1", "later", "gone"]);
    // Idempotent: applying the same evidence again changes nothing.
    expect(holdPolicyBlocked(result.state, [{ fingerprint: "a1", block: block("old") }], hours(9)).state).toEqual(result.state);
  });

  test("stage evidence maps to the findings of the slices (and integrations) whose stages were policy-blocked", () => {
    const runDir = mkdtempSync(join(tmpdir(), "fpc-holds-"));
    mkdirSync(join(runDir, "iter-1"), { recursive: true });
    writeFileSync(join(runDir, "iter-1", "plan.json"), JSON.stringify({ slices: [
      { id: "uf-crash", fingerprints: ["u1"] }, { id: "arrays-crash", fingerprints: ["a1", "a2"] }, { id: "other-crash", fingerprints: ["o1"] },
    ] }));
    writeFileSync(join(runDir, "iter-1", "integration.json"), JSON.stringify({ contents: [{ slice: "uf-crash", fingerprints: ["u1"] }] }));
    const holds = policyHoldsFromRun({
      runId: "b9bdecb3", runKey: "old", runDir, at: now.toISOString(),
      stages: [
        { stage: "iter-1/uf-crash/repair", sessionId: "s1", kind: "completed" },
        { stage: "iter-1/arrays-crash/repair", sessionId: "s2", kind: "provider-policy-blocked", code: "cyber_policy", error: STREAM_REJECTION },
        { stage: "iter-1/other-crash/repair", sessionId: "s3", kind: "provider-unavailable", error: "stream ended" },
        { stage: "iter-1/integration/verify", sessionId: "s4", kind: "provider-policy-blocked", code: "cyber_policy", error: HTTP_REJECTION },
        { stage: "investigate/diagnostics-ux", sessionId: "s5", kind: "provider-policy-blocked", code: "cyber_policy", error: HTTP_REJECTION },
      ],
    });
    expect(holds.map((hold) => [hold.fingerprint, hold.block.stage, hold.block.sessionId, hold.block.runId])).toEqual([
      ["a1", "iter-1/arrays-crash/repair", "s2", "b9bdecb3"],
      ["a2", "iter-1/arrays-crash/repair", "s2", "b9bdecb3"],
      ["u1", "iter-1/integration/verify", "s4", "b9bdecb3"],
    ]);
  });
});

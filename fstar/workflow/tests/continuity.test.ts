import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { evaluateContinuity } from "../lib/continuity.ts";
import { fromGhRuns, reportingRuns, reportKey, selectWindow } from "../lib/sources.ts";
import { emptyState, recordSeen, type WorkflowState } from "../lib/state.ts";
import type { Finding } from "../lib/reports.ts";

const listing = JSON.parse(readFileSync(join(import.meta.dir, "fixtures", "gh-runs-sample.json"), "utf8"));
const runs = [...fromGhRuns(listing.regressions, "regressions"), ...fromGhRuns(listing.build, "build")];
const now = new Date("2026-10-26T10:00:00Z");

function processed(state: WorkflowState, ...keys: string[]): WorkflowState {
  return { ...state, processedReports: Object.fromEntries(keys.map((key) => [key, { processedAt: now.toISOString(), findings: 0 }])) };
}

const partial: Finding = {
  fingerprint: "p1", kind: "partial-rule", theory: "arrays", checker: "ocaml", rule: "rewrite", detail: "eq(...)",
  affectedProofs: 1, obligations: 1, soleFamilyProofs: 1, examples: [], evidence: [], sources: ["x"],
};

describe("report discovery", () => {
  test("only completed regression runs and failed builds publish reports", () => {
    expect(reportingRuns(runs).map(reportKey)).toEqual([
      "pulse-run:40244844124-1", "pulse-run:40244573105-1", "pulse-build:40280393373-1", "pulse-build:40278436680-1",
    ]);
  });

  test("local corpora are scanned in a rotating window", () => {
    expect(selectWindow([1, 2, 3, 4, 5], 3, 3)).toEqual({ selected: [4, 5, 1], nextOffset: 1 });
    expect(selectWindow([1, 2], 0, 10)).toEqual({ selected: [1, 2], nextOffset: 0 });
  });
});

describe("retrigger conditions", () => {
  const allReports = ["pulse-run:40244844124-1", "pulse-run:40244573105-1", "pulse-build:40280393373-1", "pulse-build:40278436680-1"];

  test("a new Pulse report retriggers and is passed to the workflow", () => {
    const decision = evaluateContinuity({ runs, state: processed(emptyState(), "pulse-run:40244573105-1"), now, buildEvidence: [] });
    expect(decision.retrigger).toBe(true);
    expect(decision.newReports).toEqual(["pulse-run:40244844124-1"]);
    expect(decision.pulseRunIds).toEqual(["40244844124"]);
    expect(decision.reasons[0]).toMatch(/new Pulse report/);
  });

  test("processed reports and skipped or approval-gated runs do not retrigger", () => {
    const decision = evaluateContinuity({ runs, state: processed(emptyState(), ...allReports), now, buildEvidence: [] });
    expect(decision).toMatchObject({ retrigger: false, newReports: [], buildTimeoutReports: [], unprocessedPartialRules: 0, pendingPublications: 0 });
  });

  test("pending publications are reported but are not a retrigger condition", () => {
    const pending = { runKey: "r1", branch: "fstar-proof-checking/integration/r1", head: "abc", fingerprints: ["p1"], slices: ["arrays-repair"], recordedAt: now.toISOString() };
    const decision = evaluateContinuity({ runs, state: { ...processed(emptyState(), ...allReports), pendingPublications: [pending] }, now, buildEvidence: [] });
    expect(decision).toMatchObject({ retrigger: false, pendingPublications: 1 });
  });

  test("unprocessed partial proof rules retrigger even without new reports", () => {
    const state = recordSeen(processed(emptyState(), ...allReports), [partial], now);
    const decision = evaluateContinuity({ runs, state, now, buildEvidence: [] });
    expect(decision.retrigger).toBe(true);
    expect(decision.unprocessedPartialRules).toBe(1);
    expect(decision.pulseRunIds).toEqual([]);
  });

  test("a checker build that timed out on proofs retriggers; other build failures do not", () => {
    const state = processed(emptyState(), "pulse-run:40244844124-1", "pulse-run:40244573105-1");
    const decision = evaluateContinuity({
      runs,
      state,
      now,
      buildEvidence: [
        { key: "pulse-build:40280393373-1", proofTimeouts: 1 },
        { key: "pulse-build:40278436680-1", proofTimeouts: 0 },
      ],
    });
    expect(decision.buildTimeoutReports).toEqual(["pulse-build:40280393373-1"]);
    expect(decision.pulseRunIds).toEqual(["40280393373"]);
    expect(decision.retrigger).toBe(true);
  });

  test("a local OCaml or Cherry build log with proof timeouts retriggers once", () => {
    const evidence = [{ key: "local-build:C:/logs/cherry-build.log@1793000000000", proofTimeouts: 2, reportPath: "C:/logs" }];
    const first = evaluateContinuity({ runs: [], state: emptyState(), now, buildEvidence: evidence });
    expect(first).toMatchObject({ retrigger: true, reportPaths: ["C:/logs"] });
    const second = evaluateContinuity({ runs: [], state: processed(emptyState(), evidence[0]!.key), now, buildEvidence: evidence });
    expect(second.retrigger).toBe(false);
  });
});

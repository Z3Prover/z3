import { describe, expect, test } from "bun:test";
import { join } from "node:path";
import type { Finding } from "../lib/reports.ts";
import { MAX_CORES, planSlices } from "../lib/plan.ts";

function finding(fingerprint: string, overrides: Partial<Finding> = {}): Finding {
  return {
    fingerprint,
    kind: "partial-rule",
    theory: "arrays",
    checker: "ocaml",
    rule: "rewrite",
    detail: fingerprint,
    affectedProofs: 1,
    obligations: 1,
    soleFamilyProofs: 0,
    examples: [],
    evidence: [],
    sources: ["test"],
    ...overrides,
  };
}

const theories = ["arrays", "bitvectors", "finite-fields", "floating-point", "quantifiers", "uf", "datatypes",
  "linear-arithmetic", "nonlinear-arithmetic", "other"] as const;
const many = theories.flatMap((theory) => [finding(`${theory}-1`, { theory }), finding(`${theory}-2`, { theory }), finding(`${theory}-3`, { theory })]);
const base = { runKey: "20261026T101500Z", iteration: 1, worktreeRoot: join("C:", "state", "worktrees"), branchPrefix: "fstar-proof-checking" };

describe("slice planning", () => {
  test("total cores never exceed the 32-core budget", () => {
    for (const coreBudget of [1, 3, 4, 7, 16, 32, 64, 1000]) {
      for (const coresPerSlice of [1, 2, 4, 8, 32]) {
        const plan = planSlices(many, { ...base, coreBudget, coresPerSlice, maxFindingsPerSlice: 2 });
        const used = plan.slices.reduce((sum, slice) => sum + slice.cores, 0);
        expect(used).toBeLessThanOrEqual(Math.min(coreBudget, MAX_CORES));
        expect(plan.totalCores).toBe(used);
        expect(plan.slices.every((slice) => slice.cores >= 1)).toBe(true);
        expect(plan.concurrency).toBe(plan.slices.length);
      }
    }
  });

  test("each slice is one theory with its own worktree and branch", () => {
    const plan = planSlices(many, { ...base, coreBudget: 32, coresPerSlice: 4, maxFindingsPerSlice: 2 });
    expect(plan.slices).toHaveLength(8);
    expect(plan.slices.every((slice) => slice.cores === 4)).toBe(true);
    expect(new Set(plan.slices.map((slice) => slice.worktree)).size).toBe(8);
    expect(new Set(plan.slices.map((slice) => slice.branch)).size).toBe(8);
    for (const slice of plan.slices) {
      expect(new Set(slice.findings.map((item) => item.theory))).toEqual(new Set([slice.theory]));
      expect(slice.findings.length).toBeLessThanOrEqual(2);
      expect(slice.branch).toBe(`fstar-proof-checking/work/20261026T101500Z/i1-${slice.id}`);
      expect(slice.worktree).toBe(join(base.worktreeRoot, `20261026T101500Z-i1-${slice.id}`));
    }
    const planned = plan.slices.flatMap((slice) => slice.findings.map((item) => item.fingerprint));
    expect(new Set([...planned, ...plan.deferred]).size).toBe(many.length);
    expect(planned.filter((fingerprint) => plan.deferred.includes(fingerprint))).toEqual([]);
  });

  test("a smaller slice count shares the budget", () => {
    const plan = planSlices(many.slice(0, 6), { ...base, coreBudget: 32, coresPerSlice: 4, maxFindingsPerSlice: 3 });
    expect(plan.slices.map((slice) => slice.cores)).toEqual([16, 16]);
  });

  test("crashes, possible unsoundness, performance and partial rules get separate focuses", () => {
    const plan = planSlices([
      finding("crash", { kind: "crash", theory: "bitvectors" }),
      finding("reject", { kind: "rejected", theory: "bitvectors" }),
      finding("slow", { kind: "slow-obligation", theory: "bitvectors" }),
      finding("gap", { theory: "bitvectors" }),
    ], { ...base, coreBudget: 32, coresPerSlice: 4, maxFindingsPerSlice: 2 });
    expect(plan.slices.map((slice) => slice.id).sort()).toEqual([
      "bitvectors-crash", "bitvectors-performance", "bitvectors-repair", "bitvectors-soundness",
    ]);
  });

  test("an empty finding list produces no slices", () => {
    expect(planSlices([], { ...base, coreBudget: 32, coresPerSlice: 4, maxFindingsPerSlice: 2 })).toMatchObject({ slices: [], totalCores: 0 });
  });
});

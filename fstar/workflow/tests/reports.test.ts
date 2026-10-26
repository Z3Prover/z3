import { describe, expect, test } from "bun:test";
import { join } from "node:path";
import { normalizeReportTree, parseBuildLog, mergeFindings } from "../lib/reports.ts";
import { classifyTheory } from "../lib/theories.ts";

const fixtures = join(import.meta.dir, "fixtures");
const pulseRun = join(fixtures, "pulse-run-40244844124-1");
const buildReport = join(fixtures, "build-run-40280393373-1", "pulse-checker-build-report");

describe("Pulse report normalization", () => {
  const { findings, diagnostics } = normalizeReportTree(pulseRun, { source: "pulse-run:40244844124-1" });
  const byKind = (kind: string) => findings.filter((finding) => finding.kind === kind);

  test("partial proofs become one finding per diagnosed rule family with its theory", () => {
    const partial = byKind("partial-rule");
    expect(partial).toHaveLength(12);
    const nlsat = partial.find((finding) => finding.rule === "assumed:nlsat");
    expect(nlsat?.theory).toBe("nonlinear-arithmetic");
    expect(nlsat?.logic).toBe("QF_NIA");
    const store = partial.find((finding) => finding.detail.startsWith("eq(store:Array"));
    expect(store?.theory).toBe("arrays");
    expect(store?.obligations).toBe(63);
    expect(partial.filter((finding) => finding.detail.startsWith("eq(bvadd")).map((f) => f.theory)).toEqual(["bitvectors"]);
    expect(partial.filter((finding) => finding.logic === "QF_FF").every((f) => f.theory === "finite-fields")).toBe(true);
    expect(new Set(partial.map((finding) => finding.fingerprint)).size).toBe(partial.length);
  });

  test("crashes are grouped by checker, exit status and logic", () => {
    const crashes = byKind("crash");
    expect(crashes).toHaveLength(2);
    const bv = crashes.find((finding) => finding.logic === "QF_BV");
    expect(bv).toMatchObject({ checker: "cherry", rule: "exit -11", affectedProofs: 2, theory: "bitvectors" });
    expect(bv?.examples).toHaveLength(2);
  });

  test("whole-case checker timeouts are separate from solver UNKNOWN answers", () => {
    const timeouts = byKind("check-timeout");
    expect(timeouts.map((finding) => `${finding.checker}:${finding.logic}`).sort()).toEqual(["cherry:QF_IDL", "ocaml:QF_AUFBV"]);
    expect(findings.some((finding) => finding.examples.some((path) => path.includes("lra_lassoranker")))).toBe(false);
  });

  test("an interrupted final record is reported, not fatal", () => {
    expect(diagnostics.some((line) => line.includes("Incomplete final record"))).toBe(true);
  });

  test("fingerprints are stable across repeated normalization", () => {
    const again = normalizeReportTree(pulseRun, { source: "pulse-run:40244844124-1" });
    expect(again.findings.map((finding) => finding.fingerprint)).toEqual(findings.map((finding) => finding.fingerprint));
  });

  test("the same rule family from two sources merges evidence instead of duplicating", () => {
    const second = normalizeReportTree(pulseRun, { source: "pulse-run:99-1" }).findings;
    const merged = mergeFindings([...findings, ...second]);
    expect(merged).toHaveLength(findings.length);
    const nlsat = merged.find((finding) => finding.rule === "assumed:nlsat");
    expect(nlsat?.sources.sort()).toEqual(["pulse-run:40244844124-1", "pulse-run:99-1"]);
  });
});

describe("F* build log parsing", () => {
  test("declarations over 2 s and SMT timeouts are extracted from the real log format", async () => {
    const text = await Bun.file(join(buildReport, "build.log")).text();
    const parsed = parseBuildLog(text);
    expect(parsed.slow.map((item) => [item.declaration, item.milliseconds])).toEqual([
      ["Z3IntegerDivision.lemma_upper_bound", 13545],
      ["Z3IntegerDivision.lemma_residual_bound", 12637],
      ["Z3BvWord.lemma_append_number", 5287],
    ]);
    expect(parsed.timeouts).toEqual([
      expect.objectContaining({ location: "Z3BvWord.fst(290,6-290,35)", declaration: "Z3BvWord.lemma_append_number" }),
    ]);
  });

  test("a build report yields build-timeout and slow-obligation findings without double counting", () => {
    const { findings } = normalizeReportTree(join(fixtures, "build-run-40280393373-1"), { source: "pulse-build:40280393373-1" });
    expect(findings.filter((f) => f.kind === "build-timeout").map((f) => [f.rule, f.theory])).toEqual([
      ["Z3BvWord.lemma_append_number", "bitvectors"],
    ]);
    expect(findings.filter((f) => f.kind === "slow-obligation").map((f) => f.rule).sort()).toEqual([
      "Z3IntegerDivision.lemma_residual_bound",
      "Z3IntegerDivision.lemma_upper_bound",
    ]);
    expect(findings.every((f) => f.checker === "fstar-build")).toBe(true);
  });
});

describe("theory classification", () => {
  test.each([
    [{ rule: "quant-inst", detail: "holds(or:Bool(...))" }, "quantifiers"],
    [{ rule: "sk", detail: "" }, "quantifiers"],
    [{ rule: "arith/farkas", detail: "", logic: "QF_LRA" }, "linear-arithmetic"],
    [{ rule: "arith/lp-monomial-interval", detail: "" }, "nonlinear-arithmetic"],
    [{ rule: "rewrite", detail: "eq(fp.add:FP(...) -> ...)" }, "floating-point"],
    [{ rule: "rewrite", detail: "eq(u0:U -> u1:U)", logic: "QF_DT" }, "datatypes"],
    [{ rule: "rewrite", detail: "eq(u0:U -> u1:U)", logic: "QF_UF" }, "uf"],
    [{ rule: "", detail: "", module: "Z3QuantifierInstantiation" }, "quantifiers"],
    [{ rule: "", detail: "", module: "Z3FiniteFieldTheory" }, "finite-fields"],
    [{ rule: "rewrite", detail: "eq(u0:U -> u1:U)" }, "other"],
  ] as const)("%o is %s", (input, theory) => {
    expect(classifyTheory(input)).toBe(theory);
  });
});

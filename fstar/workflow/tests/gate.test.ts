import { describe, expect, test } from "bun:test";
import { decideSliceOutcome, scanDiffForUnsoundness, type VerifierVerdict } from "../lib/gate.ts";

const diff = (file: string, ...lines: string[]) => [
  `diff --git a/${file} b/${file}`,
  `--- a/${file}`,
  `+++ b/${file}`,
  "@@ -1,3 +1,4 @@",
  ...lines,
].join("\n");

const verified: VerifierVerdict = {
  verdict: "verified",
  toolchainAvailable: true,
  commands: [
    { command: "pwsh -NoProfile -File fstar/tools/build_ocaml_checker.ps1 -RunTests", exitCode: 0, phase: "final" },
    { command: "python fstar/tools/run_checker_regressions.py run ...", exitCode: 0, phase: "final" },
  ],
  resolvedFingerprints: ["f1"],
  soundnessConcerns: [],
  summary: "Rule family now ACCEPTs; no admits.",
};

describe("soundness scan", () => {
  test.each([
    ["admit ()", "let lemma_x () : Lemma (p) = admit ()"],
    ["assume val", "assume val magic_axiom : squash False"],
    ["assume (", "let f x = assume (x > 0); x"],
    ["admit_smt_queries", "#set-options \"--admit_smt_queries true\""],
    ["lax", "#push-options \"--lax\""],
    ["tadmit", "let t () = by (tadmit ())"],
  ])("rejects an added %s", (_label, line) => {
    expect(scanDiffForUnsoundness(diff("fstar/Z3Foo.fst", ` context`, `+${line}`)).violations).toHaveLength(1);
  });

  test("ignores removed lines, comments, strings and identifiers that merely contain the words", () => {
    const result = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst",
      "-let old () = admit ()",
      "+let rule_name = \"assumed:nlsat\" // was admit () before",
      "+(* no assume val here *) let assumed_count = 0",
      "+let admitted_by_policy = false",
    ));
    expect(result.violations).toEqual([]);
  });

  test("a raised global z3rlimit is a violation; a local push-options increase is a warning", () => {
    const global = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst", "-#set-options \"--z3rlimit 10\"", "+#set-options \"--z3rlimit 40\""));
    expect(global.violations.map((item) => item.pattern)).toEqual(["increased global z3rlimit"]);
    const local = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst", "+#push-options \"--z3rlimit 40\""));
    expect(local.violations).toEqual([]);
    expect(local.warnings).toHaveLength(1);
    const lowered = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst", "-#set-options \"--z3rlimit 40\"", "+#set-options \"--z3rlimit 10\""));
    expect(lowered.violations).toEqual([]);
  });
});

describe("slice verdict", () => {
  const clean = { violations: [], warnings: [] };
  test("verified requires an available toolchain, a verifier verdict and successful final commands", () => {
    expect(decideSliceOutcome({ scan: clean, changedFiles: 2, uncommitted: false, verifier: verified, toolchainAvailable: true }).status).toBe("verified");
  });

  test("an unavailable toolchain can never yield verified", () => {
    const outcome = decideSliceOutcome({ scan: clean, changedFiles: 2, uncommitted: false, verifier: verified, toolchainAvailable: false });
    expect(outcome.status).toBe("unverified");
    expect(outcome.reasons.join(" ")).toMatch(/toolchain/);
    expect(decideSliceOutcome({ scan: clean, changedFiles: 2, uncommitted: false, verifier: { ...verified, toolchainAvailable: false }, toolchainAvailable: true }).status).toBe("unverified");
  });

  test("an unsound change is rejected even if the verifier approved it", () => {
    const scan = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst", "+let l () : Lemma False = admit ()"));
    expect(decideSliceOutcome({ scan, changedFiles: 1, uncommitted: false, verifier: verified, toolchainAvailable: true }).status).toBe("rejected");
  });

  test.each([
    ["a failed final command", { verifier: { ...verified, commands: [{ command: "build", exitCode: 1, phase: "final" as const }] } }],
    ["no final command", { verifier: { ...verified, commands: [{ command: "build", exitCode: 0, phase: "exploratory" as const }] } }],
    ["a missing verifier verdict", { verifier: undefined }],
    ["uncommitted changes", { uncommitted: true }],
    ["a verifier that did not verify", { verifier: { ...verified, verdict: "unverified" as const } }],
  ])("%s is unverified", (_label, override) => {
    const outcome = decideSliceOutcome({ scan: clean, changedFiles: 2, uncommitted: false, verifier: verified, toolchainAvailable: true, ...override });
    expect(outcome.status).toBe("unverified");
  });

  test("no changes and verifier rejection are reported as such", () => {
    expect(decideSliceOutcome({ scan: clean, changedFiles: 0, uncommitted: false, verifier: verified, toolchainAvailable: true }).status).toBe("no-change");
    expect(decideSliceOutcome({ scan: clean, changedFiles: 1, uncommitted: false, verifier: { ...verified, verdict: "rejected" }, toolchainAvailable: true }).status).toBe("rejected");
  });
});

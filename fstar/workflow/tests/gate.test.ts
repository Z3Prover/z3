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

  test.each([
    ["magic", "fstar/Z3Foo.fst", "let f () : Lemma False = magic ()"],
    ["tadmit_t", "fstar/Z3Foo.fst", "let t () : Lemma False = assert False by (tadmit_t ())"],
    ["admit_all", "fstar/Z3Foo.fst", "let t () = assert False by (FStar.Tactics.V2.admit_all ())"],
    ["assume type", "fstar/Z3Foo.fsti", "assume type t"],
    ["assume without parentheses", "fstar/Z3Foo.fst", "let f (x:int) : int = assume x > 0; x"],
    ["#reset-options rlimit raise", "fstar/Z3Foo.fst", "#reset-options \"--z3rlimit 400\""],
    ["--z3rlimit_factor", "fstar/Z3Foo.fst", "#set-options \"--z3rlimit_factor 20\""],
    ["--admit_except", "fstar/Z3Foo.fst", "#set-options \"--admit_except Z3Foo.lemma\""],
    ["Makefile admit_smt_queries", "fstar/Makefile", "OTHERFLAGS += --admit_smt_queries true"],
    ["shell --lax", "fstar/tools/check.sh", "fstar.exe --lax Z3Foo.fst"],
    ["CI --z3rlimit_factor", ".github/workflows/pulse-checker-build.yml", "          fstar.exe --z3rlimit_factor 8 Z3Foo.fst"],
    ["PowerShell build flag rlimit raise", "fstar/tools/build_ocaml_checker.ps1", "  & $FstarExe --z3rlimit 100 --cache_checked_modules $f"],
  ])("rejects an added %s", (_label, file, line) => {
    expect(scanDiffForUnsoundness(diff(file, " context", `+${line}`)).violations).toHaveLength(1);
  });

  test.each([
    ["Prims _assume", "fstar/Z3Foo.fst", "let x = _assume (1 == 2)"],
    ["Pulse assume_", "fstar/Z3PulseFoo.fst", "let y = assume_ (pts_to x v)"],
    ["qualified Pulse assume_", "fstar/Z3PulseFoo.fst", "let y = Pulse.Lib.Core.assume_ (pts_to x v)"],
    ["--__no_positivity", "fstar/Z3Foo.fst", "#set-options \"--__no_positivity\""],
    ["an admit after a double-quote char literal", "fstar/Z3Foo.fst", "let c = '\"' let z = admit ()"],
    ["an admit after an escaped-quote char literal", "fstar/Z3Foo.fst", "let c = '\\'' let z = admit ()"],
    ["OCaml Obj.magic", "fstar/ocaml_runtime/Z3Native.ml", "let to_term (x : Obj.t) : term = Obj.magic x"],
    ["OCaml Stdlib.Obj.repr", "fstar/ocaml_runtime/prims.ml", "let r = Stdlib.Obj.repr v"],
    ["OCaml Obj.obj in an interface", "fstar/ocaml_runtime/Z3Native.mli", "val cast : Obj.t -> 'a  (* = Obj.obj *)\nlet c = Obj.obj"],
  ])("rejects an added %s", (_label, file, line) => {
    const lines = line.split("\n").map((text) => `+${text}`);
    expect(scanDiffForUnsoundness(diff(file, " context", ...lines)).violations).toHaveLength(1);
  });

  test("char literals, primed identifiers and names that contain the words are not escapes", () => {
    const fstar = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst",
      "+let quote = '\\'' let backslash = '\\\\' let dq = '\"' let assumed_ok = 1",
      "+let f (#a:Type) (x':a) : a = x' // 'a type variables and primes",
      "+let my_assume = 0 let assumes_ = 1 let admitted_ = true let magic_number = 42",
      "+let s = \"don't admit () here\"",
    ));
    expect(fstar.violations).toEqual([]);
    const ocaml = scanDiffForUnsoundness(diff("fstar/ocaml_runtime/Z3Native.ml",
      "+(* Never use",
      "+   Obj.magic here *)",
      "-let old x = Obj.magic x",
      "+let objects = MyObj.magic_count + 1",
    ));
    expect(ocaml.violations).toEqual([]);
  });

  test("ignores escapes inside multi-line comments and in comments of build files", () => {
    const fstar = scanDiffForUnsoundness(diff("fstar/Z3Foo.fst", " (* Never write", "+   admit () or assume val here,", "+   nor magic (). *)", "+let x = 1"));
    expect(fstar.violations).toEqual([]);
    const make = scanDiffForUnsoundness(diff("fstar/Makefile", "+# --lax and --admit_smt_queries are forbidden", "-OTHERFLAGS += --lax"));
    expect(make.violations).toEqual([]);
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

  test("any verifier soundness concern blocks verified, whatever its wording, and is reported", () => {
    for (const concern of ["minor: relies on an unproven axiom in Z3ArithRewriter", "Low severity: assume_ in a test helper"]) {
      const outcome = decideSliceOutcome({ scan: clean, changedFiles: 2, uncommitted: false, verifier: { ...verified, soundnessConcerns: [concern] }, toolchainAvailable: true });
      expect(outcome.status).not.toBe("verified");
      expect(outcome.reasons.join(" ")).toContain(concern);
    }
  });

  test("no changes and verifier rejection are reported as such", () => {
    expect(decideSliceOutcome({ scan: clean, changedFiles: 0, uncommitted: false, verifier: verified, toolchainAvailable: true }).status).toBe("no-change");
    expect(decideSliceOutcome({ scan: clean, changedFiles: 1, uncommitted: false, verifier: { ...verified, verdict: "rejected" }, toolchainAvailable: true }).status).toBe("rejected");
  });
});

import assert from "node:assert/strict";
import { expectedPaths, parseDiagnostic, validateBuildScript } from "./evaluation.ts";

const want = ["regressions/proofs/a.smt2", "regressions/proofs/b.smt2"];
expectedPaths(want, want);
for (const damaged of [[want[0]!], [want[0]!, want[0]!], [...want].reverse()]) {
  assert.throws(() => expectedPaths(damaged, want), /corpus case/);
}
const stderr = "diagnostic\tchecked\tpending=3\tfamilies=2\nobligation\tth-lemma\t1\t7\teq(a,b)\nobligation\trewrite\t2\t9\teq(b,c)\n";
const diagnostic = { code: 3, stdout: "PARTIAL 3\n", stderr };
assert.deepEqual(parseDiagnostic("PARTIAL 3", diagnostic).families.map(f => f[2]), [1,2]);
for (const bad of [
  { ...diagnostic, code: 2 }, { ...diagnostic, stdout: "PARTIAL 1\n" }, { ...diagnostic, stderr: "" },
  { ...diagnostic, stderr: stderr.slice(0, stderr.indexOf("obligation\trewrite")) },
  { ...diagnostic, stderr: stderr.replace("rewrite\t2", "rewrite\t1") },
  { ...diagnostic, stderr: stderr.replace("rewrite\t2\t9\teq(b,c)", "th-lemma\t2\t9\teq(a,b)") },
]) assert.throws(() => parseDiagnostic("PARTIAL 3", bad));
assert.equal(parseDiagnostic("REJECT", {code: 1, stdout: "REJECT\n", stderr: "diagnostic\trejected\tstage=proof-entry\tindex=11\n"}).stage, "stage=proof-entry index=11");
assert.throws(() => parseDiagnostic("REJECT", {code: 1, stdout: "REJECT\n", stderr: ""}));

const script = '  $modules = @(\n    "Z3Old.fst"\n  )\n  $testModules = @(\n    "Z3OldTests.fst"\n  )\n  $order = @(\n    "Z3Old.ml", "main.ml"\n  )\n  Check $modules -RunTests\n';
const extended = script.replace('"Z3Old.fst"', '"Z3Old.fst", "Z3New.fst"').replace('"Z3OldTests.fst"', '"Z3OldTests.fst", "Z3NewTests.fst"').replace('"main.ml"', '"Z3New.ml", "main.ml"');
const additions = new Set(["fstar/Z3New.fst", "fstar/Z3NewTests.fst"]);
assert.deepEqual(validateBuildScript(script, extended, additions).modules, ["Z3Old.fst", "Z3New.fst"]);
for (const tampered of [
  extended.replace("-RunTests", "-ProfileChecker"), extended.replace('"Z3OldTests.fst", ', ''),
  extended.replace('"Z3New.ml", ', ''), extended.replace('"main.ml"', '"main.ml", $(exit 0)'),
  extended.replace('"Z3Old.ml", "Z3New.ml", "main.ml"', '"main.ml", "Z3New.ml", "Z3Old.ml"'),
]) assert.throws(() => validateBuildScript(script, tampered, additions));
assert.throws(() => validateBuildScript(script, extended, new Set()), /unverified/);

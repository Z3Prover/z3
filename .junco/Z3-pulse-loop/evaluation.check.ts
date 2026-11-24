import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { appendFile, chmod, mkdir, mkdtemp, readFile, rm, symlink, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { checkStatistics, checkoutTestedTree, evaluationPaths, expectedPaths, parseDiagnostic, prCandidateFailure, validateBuildScript, validatePatch, validateRegistration, validateScope, type Analysis } from "./evaluation.ts";
import { paths } from "./state.ts";

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

const manifest = JSON.stringify({ modules: ["Z3Old.fst"], tests: ["Z3OldTests.fst"], cherry_modules: [] });
const revised = manifest.replace('"Z3Old.fst"', '"Z3Old.fst","Z3New.fst"').replace('"Z3OldTests.fst"', '"Z3OldTests.fst","Z3NewTests.fst"');
const order = '  $order = @(\n    "Z3Old.ml", "main.ml"\n  )\n  $modules = @($scope.modules)\n';
const linked = order.replace('"main.ml"', '"Z3New.ml", "main.ml"');
assert.deepEqual(validateRegistration(manifest, revised, order, linked, additions).order, ["Z3Old.ml", "Z3New.ml", "main.ml"]);
validateRegistration(manifest, revised, order, order, additions); // Verification-only modules need not be linked.
for (const [doc, script] of [
  [revised.replace('"Z3New.fst"', '"Z3Old.fst"'), linked], [revised.replace('"Z3OldTests.fst",', ""), linked],
  [revised.replace("[]", '["Z3New.fst"]'), linked], [revised.replace(/}$/, ',"unexpected":1}'), linked],
  [revised.replace(/}$/, ',"tests":[]}'), linked], [revised, linked.replace('"Z3New.ml"', '$(Get-Content x)')],
  [revised, linked.replace('"Z3New.ml"', '"Z3NewTests.ml"')], [revised, linked.replace("$scope.modules", "$scope.tests")],
  [revised, linked.replace('"Z3Old.ml", "Z3New.ml", "main.ml"', '"main.ml", "Z3New.ml", "Z3Old.ml"')],
] as const) assert.throws(() => validateRegistration(manifest, doc, order, script, additions));
assert.throws(() => validateRegistration(manifest, revised, order, linked, new Set()));

const scope = {source_sha: "candidate", backend: "ocaml", mode: "full", native_tests: true, fstar: "release", selected_modules: ["M.fst","T.fst"], selected_count: 2, registered_not_selected: []};
const checkScope = (r: Record<string,unknown>) => validateScope(r, ["M.fst"], ["T.fst"], "candidate", "release\n");
checkScope(scope);
for (const bad of [{source_sha:"parent"}, {backend:"cherry"}, {mode:"checker"}, {native_tests:false}, {fstar:"nightly"}, {selected_count:1},
  {selected_modules:["T.fst","M.fst"]}, {selected_modules:["M.fst","M.fst"]}, {registered_not_selected:["T.fst"]}]) assert.throws(() => checkScope({...scope,...bad}));
const native = {solve_ms: 0.1, marshal_ms: 2, check_ms: 3, expressions: 4, declarations: 5, proof_nodes: 6, semantics: "sorted-core"};
const stats = "solve_ms=0.100 marshal_ms=2.000 check_ms=3.000 expressions=4 declarations=5 proof_nodes=6 semantics=sorted-core";
checkStatistics(stats, native);
assert.throws(() => checkStatistics(stats.replace("sorted-core","future-semantics"), native));
assert.throws(() => checkStatistics(stats, {...native,proof_nodes:0}));
const attempted = Object.fromEntries(Array.from({length:242}, (_,i) => [`${i}.smt2`, { outcome:"TIMEOUT",wall:60 }]));
const complete: Analysis = { sha:"parent",tree:"tree",evaluator:"test",buildOk:true,ciPass:true,statsCases:0,tested:242,counts:{TIMEOUT:242},
  cases:attempted, pending:0,proofNodes:0,checkMs:0,solveMs:0,families:[],lemmas:0,assumed:0 };
assert.equal(prCandidateFailure(complete),null);
for (const bad of [{buildOk:false}, {ciPass:false}, {tested:241}, {cases:{}}, {counts:{TIMEOUT:241,ERROR:1}},
  ...["ERROR","CRASH","PROTOCOL_ERROR","NOT_RUN"].map(outcome => ({cases:{...attempted,"0.smt2":{outcome,wall:0}}}))]) {
  assert.ok(prCandidateFailure({...complete,...bad}));
}

// Exercise the real official layout without writing the source checkout or touching campaign state.
const review = "803df8055301cf5e65a3a05a2402a5da678652dd";
const env = {PATH:"/usr/bin:/bin", HOME:"/nonexistent", LC_ALL:"C", GIT_ALLOW_PROTOCOL:"file", GIT_CONFIG_NOSYSTEM:"1", GIT_CONFIG_GLOBAL:"/dev/null",
  GIT_AUTHOR_NAME:"fixture", GIT_AUTHOR_EMAIL:"fixture@localhost", GIT_COMMITTER_NAME:"fixture", GIT_COMMITTER_EMAIL:"fixture@localhost"};
const git = (cwd:string,...args:string[]) => execFileSync("/usr/bin/git", ["-c","core.hooksPath=/dev/null","-c","gc.auto=0",...args], {cwd,env,encoding:"utf8",stdio:["ignore","pipe","pipe"]}).trimEnd();
const root = await mkdtemp(join(process.env.PULSE_CHECK_TMPDIR ?? tmpdir(),"pulse-evaluator-"));
try {
  const w = join(root,"repo"); await mkdir(w);
  git(w,"init","--template=","--quiet");
  await writeFile(join(w,".git/objects/info/alternates"), git(import.meta.dir,"rev-parse","--path-format=absolute","--git-path","objects")+"\n", {flag:"wx"});
  git(w,"switch","--detach",review);
  const p = {...paths({Z3_PULSE_LOOP_REPO:w,Z3_PULSE_LOOP_STATE:root}),reviewedUpstream:review,worktree:w};
  const test = "fstar/Z3BvFreshTests.fst", original = await readFile(join(w,test),"utf8");
  const stage = (file:string) => git(w,"add","--",file);
  await appendFile(join(w,test),"\nlet retained_assertion () : Lemma (1 = 1) = ()\n"); stage(test);
  await validatePatch(p,review,w);
  const parent = git(w,"commit-tree",git(w,"write-tree"),"-p",review,"-m","parent with retained assertion");
  git(w,"switch","--detach",parent);
  await writeFile(join(w,test),original); stage(test);
  await assert.rejects(validatePatch(p,parent,w), /original test changed/);
  git(w,"restore","--source=HEAD","--staged","--worktree","--",test);

  const build = "fstar/tools/build_ocaml_checker.ps1", modules = "fstar/tools/checker_modules.json", newFile = "fstar/Z3PolicyFixture.fst";
  await writeFile(join(w,newFile),"module Z3PolicyFixture\nlet n = 1\n"); stage(newFile);
  await assert.rejects(validatePatch(p,parent,w), /unregistered/);
  const registered = (await readFile(join(w,modules),"utf8")).replace('"Z3List.fst"', '"Z3List.fst", "Z3PolicyFixture.fst"');
  await writeFile(join(w,modules),registered); stage(modules);
  await writeFile(join(w,build),(await readFile(join(w,build),"utf8")).replace('"Z3List.ml"', '"Z3List.ml", "Z3PolicyFixture.ml"')); stage(build);
  await validatePatch(p,parent,w);
  const out = join(root,"attempt"); await mkdir(out);
  const tree = git(w,"write-tree"), tested = await checkoutTestedTree(p,out,{sha:parent,tree});
  const isolated = evaluationPaths(p,out);
  assert.notEqual(tested,parent); assert.equal(git(isolated.worktree,"rev-parse","HEAD^"),parent);
  assert.equal(git(isolated.worktree,"rev-parse","HEAD^{tree}"),tree);
  assert.equal(git(isolated.worktree,"remote"),""); assert.equal(git(w,"rev-parse","HEAD"),parent);
  assert.notEqual(isolated.fstarCache,p.fstarCache);
  await chmod(join(w,newFile),0o755); stage(newFile);
  await assert.rejects(validatePatch(p,parent,w));
  await chmod(join(w,newFile),0o644); await appendFile(join(w,newFile),"assume val unchecked: int\n"); stage(newFile);
  await assert.rejects(validatePatch(p,parent,w), /unsafe proof marker/);
  await rm(join(w,newFile)); await symlink("Z3List.fst",join(w,newFile)); stage(newFile);
  await assert.rejects(validatePatch(p,parent,w));
  git(w,"restore","--source=HEAD","--staged","--worktree","--",modules,build,newFile);
  for (const file of [modules,"fstar/tools/checker_scope.py","fstar/tools/run_checker_regressions.py","fstar/Z3Native.fsti","fstar/ocaml_runtime/Z3Native.ml"]) {
    await rm(join(w,file)); stage(file); await assert.rejects(validatePatch(p,parent,w));
    git(w,"restore","--source=HEAD","--staged","--worktree","--",file);
  }
  // An incompatible official harness must fail even when the candidate and its parent match it.
  const harness = "fstar/tools/run_checker_regressions.py";
  await appendFile(join(w,harness),"\n# upstream harness changed\n"); stage(harness);
  const moved = git(w,"commit-tree",git(w,"write-tree"),"-p",parent,"-m","incompatible upstream");
  git(w,"switch","--detach",moved);
  await assert.rejects(validatePatch({...p,reviewedUpstream:moved},moved,w));
} finally { await rm(root,{recursive:true,force:true}); }

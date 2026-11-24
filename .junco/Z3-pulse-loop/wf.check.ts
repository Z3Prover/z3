// Model-free checks, with a fresh private Btrfs seed rather than the service worktree.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtemp, mkdir, readFile, rm } from 'node:fs/promises';
import { join } from 'node:path';
import { schedules, syntax } from 'junco';
import { type Analysis, analyticsMarkdown, judge, metrics, pickItem, refreshQueue } from './evaluation.ts';
import { ladder, makePublishTool, openCollection, parseMode } from './wf.ts';
import { checkPublisherParent } from './publication.check.ts';
import { checkPublication } from './publication.integration.check.ts';
import { checkClaims } from './claims.check.ts';
import { paths } from './state.ts';
import { checkState } from './state.check.ts';
import './evaluation.check.ts';

schedules.validateLadder(ladder);
for (const args of [['--publish-pr=7'],['--allow-paid','--publish-pr=0'],['--allow-paid','--publish-pr=01'],['--allow-paid','--publish-pr=2x'],['--allow-paid','--publish-pr=1','--publish-pr=2'],['--allow-paid','--once','--publish-pr=7'],['--prepare','--publish-pr=7']]) assert.equal(parseMode(args,false),undefined);
assert.equal(parseMode(['--allow-paid','--publish-pr=7'],true),undefined);
assert.equal(parseMode(['--allow-paid','--publish-pr=7'],false)?.pr,7);
assert.equal(parseMode(['--allow-paid'],false)?.pr,undefined);
process.umask(0o077);
await checkPublisherParent();
await checkPublication();
await checkClaims();
const disabled = makePublishTool({paths:paths(), sha:'', iteration:0});
await assert.rejects(disabled.execute('local',{},undefined), /No verified publication task/);
await syntax.resolveAgents(syntax.parse(await readFile(new URL('./wf.yml',import.meta.url),'utf8')), { cwd: import.meta.dir, tools:{publish_verified:disabled} });

const run = (over: Partial<Analysis> = {}): Analysis => ({
  sha: "abc", buildOk: true, tested: 4, counts: { ACCEPT: 1, PARTIAL: 2, REJECT: 1 }, pending: 7, proofNodes: 100, checkMs: 300, solveMs: 50,
  tree: 'fixture-tree', evaluator: 'fixture-evaluator', ciPass: true, statsCases: 3,
  families: [
    { rule: "PR_TH_LEMMA", shape: "arith", pending: 5, cases: [{ path: "a.smt2", count: 3, first: "7" }, { path: "b.smt2", count: 2, first: "1" }] },
    { rule: "PR_REWRITE", shape: "bv", pending: 2, cases: [{ path: "b.smt2", count: 2, first: "9" }] },
  ],
  cases: { "ok.smt2": { outcome: "ACCEPT", wall: 1, checkMs: 200 }, "a.smt2": { outcome: "PARTIAL", wall: 1, pending: 3, checkMs: 50 }, "b.smt2": { outcome: "PARTIAL", wall: 1, pending: 4, checkMs: 50 }, "r.smt2": { outcome: "REJECT", wall: 1, stage: "stage=rewrite index=4" } },
  lemmas: 10, assumed: 2, ...over,
});

const before = run();
const queue = refreshQueue({ items: [{ id: "obligation:PR_TH_LEMMA|arith", kind: "obligation", title: "", detail: "", cases: [], weight: 0, attempts: 2, status: "open", notes: ["tried"] }] }, before);
assert.deepEqual(queue.items.map((i) => i.id).sort(), ["obligation:PR_REWRITE|bv", "obligation:PR_TH_LEMMA|arith", "reject:stage=rewrite index=4", "slow:a.smt2", "slow:b.smt2", "slow:ok.smt2"]);
assert.equal(queue.items.find((i) => i.id === "obligation:PR_TH_LEMMA|arith")?.attempts, 2, "attempts survive a refresh");
assert.equal(pickItem(queue)?.id, "reject:stage=rewrite index=4", "rejects outrank obligations");
const th = queue.items.find((i) => i.id === "obligation:PR_TH_LEMMA|arith")!;
const rw = queue.items.find((i) => i.id === "obligation:PR_REWRITE|bv")!;
assert.equal(pickItem({ items: [th, rw] })?.id, rw.id, "fewer attempts first");
th.attempts = 0;
assert.equal(pickItem({ items: [th, rw] })?.id, th.id, "then larger pending first");

const improved = run({ pending: 4, families: [{ rule: "PR_TH_LEMMA", shape: "arith", pending: 2, cases: [{ path: "a.smt2", count: 2, first: "7" }] }, before.families[1]!], cases: { ...before.cases, "a.smt2": { outcome: "PARTIAL", wall: 1, pending: 2 }, "b.smt2": { outcome: "PARTIAL", wall: 1, pending: 2 } } });
assert.equal(judge(th, before, improved).ok, true);
assert.equal(judge(th, before, run()).ok, false, "unchanged corpus is not an improvement");
assert.equal(judge(th, before, run({ ...improved, assumed: 3 })).ok, false, "new assume/admit rejects");
assert.equal(judge(th, before, run({ ...improved, cases: { ...improved.cases, "ok.smt2": { outcome: "PARTIAL", wall: 1, pending: 1 } } })).ok, false, "ACCEPT -> PARTIAL rejects");
assert.equal(judge(th, before, run({ ...improved, cases: { ...improved.cases, "b.smt2": { outcome: "REJECT", wall: 1 } } })).ok, false, "PARTIAL -> REJECT rejects");
assert.equal(judge(th, before, run({ buildOk: false })).ok, false);
const timedOut = { ...improved, cases: { ...improved.cases, "ok.smt2": { outcome: "TIMEOUT", wall: 60 } } };
assert.equal(judge(th, before, run(timedOut)).ok, false, "ACCEPT -> TIMEOUT far from the budget rejects");
const edge = run({ cases: { ...before.cases, "ok.smt2": { outcome: "ACCEPT", wall: 50, checkMs: 200 } } });
assert.equal(judge(th, edge, run(timedOut)).ok, true, "ACCEPT -> TIMEOUT at the case budget is noise");
assert.match(judge(th, edge, run(timedOut)).reasons.join(), /budget-edge noise ignored/);
const solverEdge = run({ cases: { ...before.cases, "a.smt2": { outcome: "PARTIAL", wall: 10.4, pending: 3, solveMs: 9990 } } });
assert.equal(judge(th, solverEdge, run({ ...improved, cases: { ...improved.cases, "a.smt2": { outcome: "UNKNOWN", wall: 10.7 } } })).ok, true, "PARTIAL -> UNKNOWN at the solver budget is noise");
const reject = queue.items.find((i) => i.kind === "reject")!;
assert.equal(judge(reject, before, run({ cases: { ...before.cases, "r.smt2": { outcome: "PARTIAL", wall: 1, pending: 9 } }, pending: 16 })).ok, true, "REJECT -> PARTIAL is targeted progress");
assert.equal(metrics(before).proof_steps_checked, 93);
assert.match(analyticsMarkdown(before, improved), /\| proof_steps_pending \| 7 \| 4 \|/);
const root = await mkdtemp(join(process.env.PULSE_CHECK_TMPDIR ?? '/btrfs', 'pulse-check-'));
const seed = join(root,'seed'), home = join(root,'home');
await mkdir(home);
await checkState(root);
execFileSync('btrfs',['subvolume','create',seed],{stdio:'ignore'});
try {
  const p = { ...paths(), state:root, worktree:seed };
  process.env.PULSE_NONSECRET_SENTINEL = 'host-only fixture';
  const collection = await openCollection(p);
  try {
    const binding=collection.bind();
    try {
      const bash=binding.tools.get(collection.tools.find(t=>t.name==='bash')!)!;
      const result=await bash.execute('worker-preflight',{command:'test -z "${PULSE_NONSECRET_SENTINEL:-}" && test -w "$HOME" && ulimit -t'},undefined);
      assert.equal(result.content.map(x=>x.type==='text'?x.text:'').join('').trim(),'1800');
    } finally { await binding.close(); }
  } finally { await collection.close(); }
  const env = { PATH:process.env.PATH, HOME:home, LANG:'C.UTF-8', PULSE_CHECK_TMPDIR:root, ...(process.env.PULSE_CHECK_GRAFANA ? {PULSE_CHECK_GRAFANA:process.env.PULSE_CHECK_GRAFANA}: {}) };
  for (const check of ['wiring.check.ts','telemetry.check.ts']) {
    execFileSync(process.execPath,['run',check,seed,root],{cwd:import.meta.dir,env,stdio:'inherit'});
  }
} finally { execFileSync('btrfs',['subvolume','delete',seed],{stdio:'ignore'}); }
await rm(root,{recursive:true});
console.log('Z3-pulse-loop: queue, judge, evaluator, local Git, graph and telemetry checks passed');

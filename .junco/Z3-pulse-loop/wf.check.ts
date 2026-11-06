// Offline checks: YAML schema/roles, ladder identities, and the queue/judge rules on a synthetic run.
import assert from "node:assert/strict";
import { schedules, syntax, tools } from "junco";
import { type Analysis, analyticsMarkdown, document, judge, ladder, metrics, paths, pickItem, refreshQueue } from "./wf.ts";

schedules.validateLadder(ladder);
const seed = paths().worktree; // agent tools need a btrfs seed; resolveAgents only resolves tool names
const collection = await tools.ToolCollection.create(seed, {});
try { await syntax.resolveAgents(document, { cwd: seed, collection }); } finally { await collection.close(); }

const run = (over: Partial<Analysis> = {}): Analysis => ({
  sha: "abc", buildOk: true, tested: 4, counts: { ACCEPT: 1, PARTIAL: 2, REJECT: 1 }, pending: 7, proofNodes: 100, checkMs: 300, solveMs: 50,
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
console.log("Z3-pulse-loop: document, ladder and queue/judge checks passed");

/**
 * fstar-proof-checking — iterate on the F* proof checker from Pulse checker evidence.
 *
 * Requirements: fstar/workflow-instructions.txt. Usage, continuity, and limits: fstar/workflow/README.md.
 *
 * Graph (one bounded iteration i = 1..maxIterations; every node name is unique per iteration):
 *
 *   preflight → source ─┬─ iter-i/triage ─(nothing actionable or pending → stop)
 *                       │      └─ iter-i/plan (slices, cores ≤ 32, worktrees, claims)
 *                       │            ├─ iter-i/<slice>/repair   (parallel, one worktree each)
 *                       │            ├─ iter-i/<slice>/verify   (parallel, fresh verifier, schema)
 *                       │            └─ iter-i/gate → iter-i/integrate → [iter-i/integration/verify]
 *                       │                             → iter-i/publish → iter-i/persist
 *                       └─ investigate/select → [investigate/<topic> ×3] → finalize
 *
 * Verified work that is not pushed live stays `integrated` and pending in state; the first
 * iteration of a later `publish=live` run merges, re-verifies and pushes it even without new findings.
 *
 * Stop conditions: nothing actionable, iteration limit, two consecutive iterations without a
 * verified slice, or a blocked state (toolchain unavailable, PR closed without merge).
 */
import { join } from "node:path";
import { workflow } from "@bastani/atomic/workflows";
import { withSteeringPropagationContext } from "@bastani/atomic/workflows/builtin/steering-context";
import { Type } from "typebox";
import type { VerifierVerdict } from "./lib/gate.js";
import { INVESTIGATIONS, integrationVerifyPrompt, investigationPrompt, repairPrompt, verifyPrompt, type SlicePromptInput } from "./lib/prompts.js";
import { VerifierVerdictSchema } from "./lib/schemas.js";
import {
  finalizeStep,
  gateStep,
  integrateStep,
  persistStep,
  planStep,
  preflight,
  publishStep,
  selectInvestigation,
  sourceFindings,
  triageStep,
  type RunSetup,
  type SliceSummary,
  type WorkflowInputs,
} from "./lib/steps.js";
import { THEORIES } from "./lib/theories.js";

const HOUR = 3_600_000;

function sliceInput(setup: RunSetup, inputs: WorkflowInputs, slice: SliceSummary): SlicePromptInput {
  return {
    sliceId: slice.id, theory: slice.theory, focus: slice.focus, worktree: slice.worktree, branch: slice.branch,
    baseRef: inputs.baseRef, cores: slice.cores, findingsPath: slice.findingsPath, sliceDir: slice.sliceDir, toolchain: setup.toolchain,
  };
}

/** Structured result of a schema-backed task that may have failed; failures count as "no verdict" (null). */
function verdictOf(settled: PromiseSettledResult<{ structured?: unknown }>): VerifierVerdict | null {
  return settled.status === "fulfilled" ? ((settled.value.structured as VerifierVerdict | undefined) ?? null) : null;
}

export default workflow({
  name: "fstar-proof-checking",
  description: "Improve the F* proof checker from Pulse checker reports and local corpora: theory-sliced repairs in isolated worktrees (≤32 cores), independent verification, soundness gates, and branch/PR publication.",
  inputs: {
    pulseRunIds: Type.Array(Type.String(), { default: [], description: "Pulse regression or checker-build run IDs to process; empty lists the newest unprocessed runs (read-only gh)." }),
    pulseBranch: Type.String({ default: "master", description: "Branch whose Pulse runs are listed when pulseRunIds is empty; empty means all branches." }),
    maxReports: Type.Integer({ default: 2, minimum: 1, maximum: 10, description: "Most unprocessed Pulse runs to download per launch." }),
    reportPaths: Type.Array(Type.String(), { default: [], description: "Local report directories (run_checker_regressions.py output or downloaded artifacts) or build logs." }),
    localCorpora: Type.Array(Type.String(), { default: ["C:/z3test/regressions/smt2", "C:/bench/inputs"], description: "Local corpora: z3test regressions/smt2 runs in --interactive mode; others use the batch harness." }),
    localCaseLimit: Type.Integer({ default: 50, minimum: 0, maximum: 5000, description: "Cases per local corpus and checker per launch (rotating window)." }),
    ocamlChecker: Type.String({ default: "", description: "OCaml checker executable for local corpora (default Z3_FSTAR_CHECKER)." }),
    cherryChecker: Type.String({ default: "", description: "Cherry checker executable for local corpora (default Z3_FSTAR_CHERRY_CHECKER)." }),
    fstarExe: Type.String({ default: "", description: "F* executable (default FSTAR_EXE, PATH, or C:\\fstar\\fstar\\bin\\fstar.exe)." }),
    cherryFstarExe: Type.String({ default: "", description: "Cherry F* executable (default CHERRY_FSTAR_EXE)." }),
    theories: Type.Array(Type.Union(THEORIES.map((theory) => Type.Literal(theory))), { default: [], description: "Restrict to these theories; empty means all." }),
    maxIterations: Type.Integer({ default: 2, minimum: 1, maximum: 5, description: "Bounded iterations per launch." }),
    coreBudget: Type.Integer({ default: 32, minimum: 1, maximum: 32, description: "Total cores shared by concurrently running slices (machine has 32)." }),
    coresPerSlice: Type.Integer({ default: 4, minimum: 1, maximum: 32, description: "Minimum cores per slice; budget / coresPerSlice slices run per iteration." }),
    maxFindingsPerSlice: Type.Integer({ default: 2, minimum: 1, maximum: 6, description: "Rule families or declarations per slice." }),
    publish: Type.Union([Type.Literal("none"), Type.Literal("dry-run"), Type.Literal("live")], { default: "dry-run", description: "live pushes the active branch and opens/updates PRs and crash issues; dry-run only plans them." }),
    dryRun: Type.Boolean({ default: false, description: "Plan only: no GitHub calls, no checker or agent stages, no worktrees, no state changes." }),
    investigate: Type.Boolean({ default: true, description: "Run the report-only scalability, certificate and diagnostics investigations when findings changed." }),
    stateDir: Type.String({ default: ".atomic/fstar-proof-checking", description: "Persistent state, report cache, run evidence and worktrees (relative to the repository root)." }),
    repo: Type.String({ default: "Z3Prover/z3" }),
    remote: Type.String({ default: "origin" }),
    baseRef: Type.String({ default: "origin/master", description: "Base for slice worktrees." }),
    prBase: Type.String({ default: "master" }),
    branchPrefix: Type.String({ default: "fstar-proof-checking" }),
    bugReportRepo: Type.String({ default: "FStarLang/FStar", description: "Where crash bug reports are filed in live mode." }),
  },
  outputs: {
    status: Type.String({ description: "completed, or blocked with an actionable reason in summary." }),
    summary: Type.String(),
    stop_reason: Type.String(),
    iterations: Type.Integer(),
    verified_slices: Type.Integer(),
    run_dir: Type.String({ description: "Local evidence directory for this run." }),
    evidence_path: Type.String(),
    findings_path: Type.String(),
  },
  run: async (rawCtx) => {
    const ctx = withSteeringPropagationContext(rawCtx);
    const inputs = ctx.inputs as unknown as WorkflowInputs;
    const cwd = ctx.cwd ?? process.cwd();

    const setup = await ctx.tool("preflight", { cwd, stateDir: inputs.stateDir, dryRun: inputs.dryRun },
      ({ signal }) => preflight(inputs, cwd, signal), { timeoutMs: 5 * 60_000 });
    const source = await ctx.tool("source", { runKey: setup.runKey },
      ({ signal }) => sourceFindings(setup, inputs, signal), { timeoutMs: 3 * HOUR });

    const planned: string[] = [];
    const worktrees: string[] = [];
    const iterations: Array<Record<string, unknown>> = [];
    let status: "completed" | "blocked" = "completed";
    let stopReason = `iteration limit (${inputs.maxIterations}) reached`;
    let idle = 0;
    let verifiedSlices = 0;
    let attemptedSlices = 0;

    for (let i = 1; i <= inputs.maxIterations; i += 1) {
      const triage = await ctx.tool(`iter-${i}/triage`, { runKey: setup.runKey, exclude: [...planned] },
        async () => triageStep(setup, inputs, source.findingsPath, i, planned), { timeoutMs: 5 * 60_000 });
      // A live run publishes earlier verified integrations even when no new finding is actionable.
      const publishPending = i === 1 && !inputs.dryRun && inputs.publish === "live" && triage.pendingPublications > 0;
      if (triage.actionable === 0 && !publishPending) {
        stopReason = i === 1 ? "no new or unprocessed findings" : "every actionable finding was handled this run";
        break;
      }
      if (!inputs.dryRun && !setup.toolchain.available) {
        status = "blocked";
        stopReason = `proof-checking toolchain unavailable (${setup.toolchain.missing.join("; ")}); install it and relaunch`;
        break;
      }

      const plan = await ctx.tool(`iter-${i}/plan`, { runKey: setup.runKey, actionable: triage.actionable },
        ({ signal }) => planStep(setup, inputs, triage.actionablePath, i, signal), { timeoutMs: 30 * 60_000 });
      planned.push(...plan.slices.flatMap((slice) => slice.fingerprints));
      if (plan.worktreesCreated) worktrees.push(...plan.slices.map((slice) => slice.worktree));

      const verdicts: Array<VerifierVerdict | null> = [];
      if (!inputs.dryRun) {
        // Promise.allSettled rather than ctx.parallel: ctx.parallel rejects the whole set when one
        // step fails, which would discard the sibling slices' work and verdicts.
        await Promise.allSettled(plan.slices.map((slice) => ctx.task(`iter-${i}/${slice.id}/repair`, {
          prompt: repairPrompt(sliceInput(setup, inputs, slice)),
          cwd: slice.worktree, context: "fresh", output: slice.reportPath, outputMode: "file-only",
        })));
        const checked = await Promise.allSettled(plan.slices.map((slice) => ctx.task(`iter-${i}/${slice.id}/verify`, {
          prompt: verifyPrompt({ ...sliceInput(setup, inputs, slice), reportPath: slice.reportPath }),
          cwd: slice.worktree, context: "fresh", schema: VerifierVerdictSchema, output: slice.verifyPath, outputMode: "file-only",
        })));
        verdicts.push(...checked.map(verdictOf));
      }

      const gate = await ctx.tool(`iter-${i}/gate`, { runKey: setup.runKey, verdicts },
        ({ signal }) => gateStep(setup, inputs, plan, verdicts, i, signal), { timeoutMs: 30 * 60_000 });
      const integration = await ctx.tool(`iter-${i}/integrate`, { runKey: setup.runKey, verified: gate.verified },
        ({ signal }) => integrateStep(setup, inputs, plan, gate, i, signal), { timeoutMs: 30 * 60_000 });
      if (integration.worktree) worktrees.push(integration.worktree);

      let integrationVerdict: VerifierVerdict | null = null;
      const integrated = [...integration.merged, ...integration.pendingMerged.map((runKey) => `pending integration ${runKey}`)];
      if (!inputs.dryRun && integration.worktree && integration.branch && integrated.length > 0) {
        const [checked] = await Promise.allSettled([ctx.task(`iter-${i}/integration/verify`, {
          prompt: integrationVerifyPrompt({
            worktree: integration.worktree, branch: integration.branch, baseRef: integration.base,
            cores: inputs.coreBudget, mergedSlices: integrated, toolchain: setup.toolchain,
          }),
          cwd: integration.worktree, context: "fresh", schema: VerifierVerdictSchema,
          output: join(setup.runDir, `iter-${i}`, "integration-verification.md"), outputMode: "file-only",
        })]);
        integrationVerdict = checked ? verdictOf(checked) : null;
      }

      const publication = await ctx.tool(`iter-${i}/publish`, { runKey: setup.runKey, mode: inputs.publish, head: integration.head ?? "" },
        ({ signal }) => publishStep(setup, inputs, plan, gate, integration, integrationVerdict, i, signal), { timeoutMs: 30 * 60_000 });
      const persisted = await ctx.tool(`iter-${i}/persist`, { runKey: setup.runKey },
        async () => persistStep(setup, inputs, source, plan, gate, integration, publication, i), { timeoutMs: 5 * 60_000 });

      attemptedSlices += plan.slices.length;
      verifiedSlices += gate.verified;
      iterations.push({
        iteration: i, actionable: triage.actionable, skipped: triage.skipped, slices: plan.slices.map((slice) => slice.id),
        cores: plan.totalCores, gate: gate.slices.map((slice) => `${slice.id}: ${slice.status}`), merged: integration.merged,
        pendingMerged: integration.pendingMerged, pendingFailed: integration.pendingFailed,
        publication: publication.summary, published: persisted.published, stateCommitted: persisted.committed,
      });
      if (publication.blocked) {
        status = "blocked";
        stopReason = publication.blocked;
        break;
      }
      idle = gate.verified === 0 ? idle + 1 : 0;
      if (!inputs.dryRun && idle >= 2) {
        stopReason = "no progress: two consecutive iterations produced no verified slice (findings are backed off)";
        break;
      }
    }

    const investigation = await ctx.tool("investigate/select", { runKey: setup.runKey, status },
      async () => (status === "blocked" ? { run: false, reason: "run is blocked", digest: "" } : selectInvestigation(setup, inputs, source)),
      { timeoutMs: 60_000 });
    if (investigation.run) {
      await Promise.allSettled(INVESTIGATIONS.map((topic) => ctx.task(`investigate/${topic.id}`, {
        prompt: investigationPrompt(topic, { findingsPath: source.findingsPath, repoRoot: setup.repoRoot, runDir: setup.runDir }),
        cwd: setup.repoRoot, context: "fresh", excludedTools: ["edit", "write"],
        output: join(setup.runDir, "investigations", `${topic.id}.md`), outputMode: "file-only",
      })));
    }

    const final = await ctx.tool("finalize", { runKey: setup.runKey, status, stopReason },
      ({ signal }) => finalizeStep(setup, inputs, { status, stopReason, iterations, investigation, verified: verifiedSlices, attempted: attemptedSlices }, worktrees, signal),
      { timeoutMs: 30 * 60_000 });

    return {
      status,
      summary: `${stopReason}. Findings: ${source.total}; iterations: ${iterations.length}; verified slices: ${verifiedSlices}/${attemptedSlices}; remote mutations: ${final.mutatingCommands}. Evidence: ${final.evidencePath}`,
      stop_reason: stopReason,
      iterations: iterations.length,
      verified_slices: verifiedSlices,
      run_dir: setup.runDir,
      evidence_path: final.evidencePath,
      findings_path: source.findingsPath,
    };
  },
});

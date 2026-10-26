/**
 * fstar-proof-checking — iterate on the F* proof checker from Pulse checker evidence.
 *
 * Requirements: fstar/workflow-instructions.txt. Usage, continuity, and limits: fstar/workflow/README.md.
 *
 * Graph (one bounded iteration i = 1..maxIterations; every node name is unique per iteration):
 *
 *   preflight → reconcile-publications → source → record-sources
 *     ─┬─ iter-i/triage ─(nothing actionable or pending → stop)
 *      │      └─ iter-i/plan (slices, cores ≤ 32, worktrees, claims)
 *      │            ├─ iter-i/<slice>/repair   (parallel, one worktree each) → iter-i/repair-outcomes
 *      │            ├─ iter-i/<slice>/verify   (parallel, fresh verifier, schema; not after a
 *      │            │                           provider-failed repair) → [iter-i/verify-outcomes]
 *      │            └─ iter-i/gate → iter-i/integrate → [iter-i/integration/verify → [iter-i/integration/outcome]]
 *      │                             → iter-i/publish → iter-i/persist
 *      └─ investigate/select → [investigate/<topic> ×3 → investigate/outcomes] → finalize
 *
 * The `…outcomes` steps classify agent stages from their sessions (lib/provider.ts): Atomic
 * records a stage that ended on a provider error as completed. A provider policy rejection (for
 * example `cyber_policy`) holds the slice's findings as `provider_policy_blocked` and ends the run
 * `blocked` with the stage, session and code; an outage leaves them open. Neither counts as an
 * attempt, and neither is retried here on another model or with a different prompt.
 * `reconcile-publications` checks (read-only) the branches carrying published findings: a merged
 * PR marks them merged, a branch deleted before its PR merged reopens them, and integrated work no
 * pending publication carries reopens. `record-sources` marks the sourced reports processed and
 * records new findings before any iteration can stop early (a merged finding that newer report
 * evidence still shows is reopened there); findings left open (deferred by slice capacity, out of
 * backoff, abandoned claims, reopened) are re-sourced from state by later runs.
 *
 * Each iteration integrates into its own branch, on top of the run's earlier verified head, so a
 * merge whose integration verification failed never reaches a later head. Verified work that is
 * not pushed live stays `integrated` and pending in state; the first iteration of a later
 * `publish=live` run merges, re-verifies and pushes it even without new findings.
 *
 * Stop conditions: nothing actionable, iteration limit, two consecutive iterations without a
 * verified slice, or a blocked state (toolchain not found, PR closed without merge, push refused
 * as non-fast-forward).
 */
import { join } from "node:path";
import { workflow } from "@bastani/atomic/workflows";
import { withSteeringPropagationContext } from "@bastani/atomic/workflows/builtin/steering-context";
import { Type } from "typebox";
import type { VerifierVerdict } from "./lib/gate.js";
import { classifyStages, describeOutcome, isProviderFailure, type StageOutcome } from "./lib/provider.js";
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
  reconcilePublicationsStep,
  recordSourcesStep,
  recordStageOutcomes,
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
    localCaseLimit: Type.Integer({ default: 50, minimum: 0, maximum: 5000, description: "Cases per local corpus and checker per launch (rotating window; batch corpora such as C:/bench/inputs share it evenly between their top-level logic directories)." }),
    ocamlChecker: Type.String({ default: "", description: "OCaml checker executable in the build environment (default Z3_FSTAR_CHECKER, else the newest discovered build)." }),
    cherryChecker: Type.String({ default: "", description: "Cherry checker executable in the build environment (default Z3_FSTAR_CHERRY_CHECKER, else the newest discovered build)." }),
    fstarExe: Type.String({ default: "", description: "Linux F* v2026.09.27 in the build environment (default FSTAR_EXE, PATH, or the known install layouts)." }),
    cherryFstarExe: Type.String({ default: "", description: "Cherry-capable Linux F* (default CHERRY_FSTAR_EXE, else a discovered nightly)." }),
    wslDistro: Type.String({ default: "", description: "WSL distribution that builds and runs the checker on Windows (default Z3_FSTAR_WSL_DISTRO, else the first with bash, Ubuntu first)." }),
    opamRoot: Type.String({ default: "", description: "OPAMROOT that holds the OCaml 5.3 switch (default Z3_FSTAR_OPAMROOT, else ~/.opam and the known install layouts)." }),
    opamSwitch: Type.String({ default: "fstar53", description: "opam switch with OCaml 5.3.0, ocamlfind and zarith." }),
    pwshExe: Type.String({ default: "", description: "Linux PowerShell 7 for build_ocaml_checker.ps1 (default Z3_FSTAR_PWSH, PATH, or the known install layouts)." }),
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
    status: Type.String({ description: "completed, or blocked with an actionable reason in summary (including agent stages the provider rejected for policy)." }),
    summary: Type.String(),
    stop_reason: Type.String(),
    iterations: Type.Integer(),
    verified_slices: Type.Integer(),
    run_dir: Type.String({ description: "Local evidence directory for this run." }),
    evidence_path: Type.String(),
    findings_path: Type.String(),
    provider_failures: Type.Array(Type.String(), { description: "Agent stages that ended on a provider error: stage, outcome, code and session." }),
  },
  run: async (rawCtx) => {
    const ctx = withSteeringPropagationContext(rawCtx);
    const inputs = ctx.inputs as unknown as WorkflowInputs;
    const cwd = ctx.cwd ?? process.cwd();

    const setup = await ctx.tool("preflight", { cwd, stateDir: inputs.stateDir, dryRun: inputs.dryRun },
      ({ signal }) => preflight(inputs, cwd, signal), { timeoutMs: 5 * 60_000 });
    // Before sourcing: merged PRs mark their findings merged; lost publications and orphaned integrations reopen (and are re-sourced).
    await ctx.tool("reconcile-publications", { runKey: setup.runKey, publish: inputs.publish },
      ({ signal }) => reconcilePublicationsStep(setup, inputs, signal), { timeoutMs: 10 * 60_000 });
    const source = await ctx.tool("source", { runKey: setup.runKey },
      ({ signal }) => sourceFindings(setup, inputs, signal), { timeoutMs: 3 * HOUR });
    // Record ingested reports, scan windows and new findings before any iteration can stop early.
    await ctx.tool("record-sources", { runKey: setup.runKey, reports: source.reports.map((report) => report.key) },
      async () => recordSourcesStep(setup, inputs, source), { timeoutMs: 5 * 60_000 });

    const planned: string[] = [];
    const worktrees: string[] = [];
    const iterations: Array<Record<string, unknown>> = [];
    let status: "completed" | "blocked" = "completed";
    let stopReason = `iteration limit (${inputs.maxIterations}) reached`;
    let idle = 0;
    let verifiedSlices = 0;
    let attemptedSlices = 0;
    const providerFailures: StageOutcome[] = [];
    /** Classify settled agent stages from their sessions (durable, so a resumed run replays the classification). */
    const classify = async (group: string, names: string[], settled: ReadonlyArray<PromiseSettledResult<{ sessionId?: string }>>) => {
      const sessions = settled.map((item) => (item.status === "fulfilled" ? item.value.sessionId ?? null : null));
      const outcomes = await ctx.tool(group, { runKey: setup.runKey, stages: names, sessions },
        async () => recordStageOutcomes(setup, group, await classifyStages(cwd, names, settled)), { timeoutMs: 5 * 60_000 });
      providerFailures.push(...outcomes.filter(isProviderFailure));
      return outcomes;
    };
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
        stopReason = `proof-checking toolchain not found (${setup.toolchain.missing.join("; ")}); set the named input or environment variable, or install it, and relaunch`;
        break;
      }

      const plan = await ctx.tool(`iter-${i}/plan`, { runKey: setup.runKey, actionable: triage.actionable },
        ({ signal }) => planStep(setup, inputs, triage.actionablePath, i, signal), { timeoutMs: 30 * 60_000 });
      planned.push(...plan.slices.flatMap((slice) => slice.fingerprints));
      if (plan.worktreesCreated) worktrees.push(...plan.slices.map((slice) => slice.worktree));

      const verdicts: Array<VerifierVerdict | null> = plan.slices.map(() => null);
      const providers: Array<StageOutcome | null> = plan.slices.map(() => null);
      if (!inputs.dryRun && plan.slices.length > 0) {
        // Promise.allSettled rather than ctx.parallel: ctx.parallel rejects the whole set when one
        // step fails, which would discard the sibling slices' work and verdicts.
        const repairNames = plan.slices.map((slice) => `iter-${i}/${slice.id}/repair`);
        const repairs = await Promise.allSettled(plan.slices.map((slice) => ctx.task(`iter-${i}/${slice.id}/repair`, {
          prompt: repairPrompt(sliceInput(setup, inputs, slice)),
          cwd: slice.worktree, context: "fresh", output: slice.reportPath, outputMode: "file-only",
        })));
        const repaired = await classify(`iter-${i}/repair-outcomes`, repairNames, repairs);
        // A repair that ended on a provider error is not verified: its findings are held or stay open.
        repaired.forEach((outcome, index) => {
          if (isProviderFailure(outcome)) providers[index] = outcome;
        });
        const toVerify = plan.slices.flatMap((slice, index) => (providers[index] ? [] : [{ slice, index }]));
        const checked = await Promise.allSettled(toVerify.map(({ slice }) => ctx.task(`iter-${i}/${slice.id}/verify`, {
          prompt: verifyPrompt({ ...sliceInput(setup, inputs, slice), reportPath: slice.reportPath }),
          cwd: slice.worktree, context: "fresh", schema: VerifierVerdictSchema, output: slice.verifyPath, outputMode: "file-only",
        })));
        toVerify.forEach(({ index }, position) => {
          verdicts[index] = checked[position] ? verdictOf(checked[position]) : null;
        });
        // A verifier that returned no verdict may have ended on a provider error.
        const missing = toVerify.flatMap((item, position) => (verdicts[item.index] === null ? [{ ...item, position }] : []));
        if (missing.length > 0) {
          const outcomes = await classify(`iter-${i}/verify-outcomes`, missing.map(({ slice }) => `iter-${i}/${slice.id}/verify`),
            missing.map(({ position }) => checked[position] as PromiseSettledResult<{ sessionId?: string }>));
          outcomes.forEach((outcome, k) => {
            const item = missing[k];
            if (item && isProviderFailure(outcome)) providers[item.index] = outcome;
          });
        }
      }

      const gate = await ctx.tool(`iter-${i}/gate`, { runKey: setup.runKey, verdicts, providers },
        ({ signal }) => gateStep(setup, inputs, plan, verdicts, i, signal, undefined, providers), { timeoutMs: 30 * 60_000 });
      const integration = await ctx.tool(`iter-${i}/integrate`, { runKey: setup.runKey, verified: gate.verified },
        ({ signal }) => integrateStep(setup, inputs, plan, gate, i, signal), { timeoutMs: 30 * 60_000 });
      if (integration.worktree) worktrees.push(integration.worktree);

      let integrationVerdict: VerifierVerdict | null = null;
      let integrationProvider: StageOutcome | null = null;
      // Exactly what the integrated head contains: this iteration's slices and merged pending integrations.
      const integrated = integration.contents.map((item) => `${item.slice} (${item.fingerprints.join(", ")})${item.from ? ` from pending integration ${item.from}` : ""}`);
      if (!inputs.dryRun && integration.worktree && integration.branch && integrated.length > 0) {
        const name = `iter-${i}/integration/verify`;
        const [checked] = await Promise.allSettled([ctx.task(`iter-${i}/integration/verify`, {
          prompt: integrationVerifyPrompt({
            worktree: integration.worktree, branch: integration.branch, baseRef: integration.base,
            cores: inputs.coreBudget, mergedSlices: integrated, toolchain: setup.toolchain,
          }),
          cwd: integration.worktree, context: "fresh", schema: VerifierVerdictSchema,
          output: join(setup.runDir, `iter-${i}`, "integration-verification.md"), outputMode: "file-only",
        })]);
        integrationVerdict = checked ? verdictOf(checked) : null;
        if (checked && integrationVerdict === null) {
          const [outcome] = await classify(`iter-${i}/integration/outcome`, [name], [checked]);
          if (isProviderFailure(outcome)) integrationProvider = outcome;
        }
      }

      const publication = await ctx.tool(`iter-${i}/publish`, { runKey: setup.runKey, mode: inputs.publish, head: integration.head ?? "" },
        ({ signal }) => publishStep(setup, inputs, plan, gate, integration, integrationVerdict, i, signal, undefined, integrationProvider), { timeoutMs: 30 * 60_000 });
      const persisted = await ctx.tool(`iter-${i}/persist`, { runKey: setup.runKey },
        async () => persistStep(setup, inputs, plan, gate, integration, publication, i), { timeoutMs: 5 * 60_000 });

      attemptedSlices += plan.slices.length;
      verifiedSlices += gate.verified;
      iterations.push({
        iteration: i, actionable: triage.actionable, skipped: triage.skipped, slices: plan.slices.map((slice) => slice.id),
        cores: plan.totalCores, gate: gate.slices.map((slice) => `${slice.id}: ${slice.status}`), merged: integration.merged,
        pendingMerged: integration.pendingMerged, pendingFailed: integration.pendingFailed,
        publication: publication.summary, published: persisted.published, stateCommitted: persisted.committed,
        providerFailures: providerFailures.filter((outcome) => outcome.stage.startsWith(`iter-${i}/`)).map((outcome) => describeOutcome(outcome, false)),
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
    let investigated = investigation;
    if (investigation.run) {
      const names = INVESTIGATIONS.map((topic) => `investigate/${topic.id}`);
      const reports = await Promise.allSettled(INVESTIGATIONS.map((topic) => ctx.task(`investigate/${topic.id}`, {
        prompt: investigationPrompt(topic, { findingsPath: source.findingsPath, repoRoot: setup.repoRoot, runDir: setup.runDir }),
        cwd: setup.repoRoot, context: "fresh", excludedTools: ["edit", "write"],
        output: join(setup.runDir, "investigations", `${topic.id}.md`), outputMode: "file-only",
      })));
      const failed = (await classify("investigate/outcomes", names, reports)).filter(isProviderFailure);
      // Investigations that ended on a provider error are not recorded as done, so a later run repeats them.
      if (failed.length > 0) investigated = { ...investigation, run: false, reason: `${investigation.reason}; not recorded as done: ${failed.map((outcome) => describeOutcome(outcome, false)).join("; ")}` };
    }

    const policyBlocked = providerFailures.filter((outcome) => outcome.kind === "provider-policy-blocked");
    if (policyBlocked.length > 0) {
      // A provider restriction, not a proof failure: reported as blocked, never routed to another model or reworded.
      status = "blocked";
      stopReason = `${stopReason}; the provider rejected ${policyBlocked.length} agent stage(s) for policy: ${policyBlocked.map((outcome) => describeOutcome(outcome, false)).join("; ")}. `
        + "Their findings are held as provider_policy_blocked (no attempt, no backoff, not retried automatically); once the restriction is resolved, "
        + "requeue them with `bun fstar/workflow/continuity.ts --requeue-policy-blocked all` (or a fingerprint)";
    }

    const final = await ctx.tool("finalize", { runKey: setup.runKey, status, stopReason },
      ({ signal }) => finalizeStep(setup, inputs, { status, stopReason, iterations, investigation: investigated, verified: verifiedSlices, attempted: attemptedSlices, providerFailures }, worktrees, signal),
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
      provider_failures: providerFailures.map((outcome) => describeOutcome(outcome, false)),
    };
  },
});

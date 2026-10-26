/**
 * The continuity loop end to end: the launcher's decision (the real `continuity.ts --check` CLI),
 * the workflow's sourcing step on the inputs the launcher would pass, the state the run records,
 * and the launcher's next decision. A retrigger must give the launched run work it can process,
 * and processed evidence must not retrigger again.
 */
import { describe, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { copyFileSync, mkdirSync, mkdtempSync, utimesSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { CommandRunner } from "../lib/command.ts";
import { normalizeReportTree } from "../lib/reports.ts";
import { emptyState, readState, recordOutcomes, recordSeen, writeJsonAtomic, type WorkflowState } from "../lib/state.ts";
import * as steps from "../lib/steps.ts";

const fixtures = join(import.meta.dir, "fixtures");
const launcher = join(import.meta.dir, "..", "continuity.ts");
const signal = new AbortController().signal;

/** `gh run list` finds no Pulse runs; nothing else may reach GitHub. */
const noRemoteRuns: CommandRunner = async (argv, options) => {
  if (argv[0] === "gh" && argv[1] === "run" && argv[2] === "list") return { code: 0, stdout: "[]", stderr: "" };
  throw new Error(`unexpected command ${argv.join(" ")} (${options.cwd ?? ""})`);
};

function check(stateDir: string, ...extra: string[]) {
  const output = execFileSync(process.execPath, [launcher, "--check", "--no-remote", "--state-dir", stateDir, ...extra], { encoding: "utf8" });
  return JSON.parse(output).decision as { retrigger: boolean; reasons: string[]; unprocessedPartialRules: number; pulseRunIds: string[]; reportPaths: string[] };
}

function workflowRun(root: string, stateDir: string, decision: { pulseRunIds: string[]; reportPaths: string[] }) {
  const runDir = join(root, "run");
  mkdirSync(runDir, { recursive: true });
  const setup = {
    repoRoot: root, stateDir, runKey: "r", runDir, worktreeRoot: join(root, "wt"), startedAt: "t",
    toolchain: { opam: true, opamSwitch: "fstar53", candidates: {}, available: true, missing: [] },
  } as unknown as steps.RunSetup;
  const inputs = {
    pulseRunIds: decision.pulseRunIds, pulseBranch: "", maxReports: 2, reportPaths: decision.reportPaths, localCorpora: [], localCaseLimit: 0,
    theories: [], coreBudget: 32, dryRun: false, repo: "Z3Prover/z3",
  } as unknown as steps.WorkflowInputs;
  return { setup, inputs };
}

const seed = (stateDir: string, state: WorkflowState) => {
  mkdirSync(stateDir, { recursive: true });
  writeJsonAtomic(join(stateDir, "state.json"), state);
};

describe("continuity loop", () => {
  test("a partial-rule retrigger gives the launched run the unprocessed rules, and processing them ends the retrigger", async () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-loop-"));
    const stateDir = join(root, "state");
    const partials = normalizeReportTree(join(fixtures, "pulse-run-40244844124-1"), { source: "pulse-run:40244844124-1" }).findings
      .filter((finding) => finding.kind === "partial-rule");
    expect(partials.length).toBeGreaterThan(0);
    seed(stateDir, recordSeen(emptyState(), partials, new Date()));

    const decision = check(stateDir);
    expect(decision).toMatchObject({ retrigger: true, unprocessedPartialRules: partials.length, pulseRunIds: [], reportPaths: [] });

    const { setup, inputs } = workflowRun(root, stateDir, decision);
    const source = await steps.sourceFindings(setup, inputs, signal, noRemoteRuns);
    expect(source.total).toBe(partials.length);
    const triage = steps.triageStep(setup, inputs, source.findingsPath, 1, []);
    expect(triage.actionable).toBe(partials.length);

    // The run attempted them without verifying them: they back off, so the launcher stays quiet.
    const outcomes = partials.map((finding) => ({ fingerprint: finding.fingerprint, status: "unverified" as const, note: "scripted" }));
    seed(stateDir, recordOutcomes(readState(stateDir), outcomes, { runKey: "r", now: new Date() }));
    expect(check(stateDir)).toMatchObject({ retrigger: false, unprocessedPartialRules: 0 });
  }, 120_000);

  test("a processed local build log does not retrigger again; a rewritten one does", async () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-log-"));
    const stateDir = join(root, "state");
    const log = join(root, "ocaml-checker-build.log");
    copyFileSync(join(fixtures, "build-run-40280393373-1", "pulse-checker-build-report", "build.log"), log);

    const decision = check(stateDir, "--build-log", log);
    expect(decision.retrigger).toBe(true);
    expect(decision.reasons.join(" ")).toMatch(/timed out on proofs/);

    // The launched run sources exactly what the launcher passes and records those reports as processed.
    const { setup, inputs } = workflowRun(root, stateDir, decision);
    const source = await steps.sourceFindings(setup, inputs, signal, noRemoteRuns);
    expect(source.byKind["build-timeout"]).toBeGreaterThan(0);
    const now = new Date().toISOString();
    seed(stateDir, { ...emptyState(), processedReports: Object.fromEntries(source.reports.map((report) => [report.key, { processedAt: now, findings: source.total }])) });

    expect(check(stateDir, "--build-log", log).retrigger).toBe(false);
    const later = new Date(Date.now() + 60_000);
    utimesSync(log, later, later);
    expect(check(stateDir, "--build-log", log).retrigger).toBe(true);
  }, 120_000);
});

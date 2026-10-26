/**
 * Retrigger decision for the continuity launcher. The instructions name three conditions:
 * a new Pulse checker report, unprocessed partial proof rules, and an OCaml/Cherry checker build
 * that times out because of proof timeouts. A bounded workflow run never retriggers itself;
 * the launcher (or a scheduler that invokes it) evaluates these conditions between runs.
 */
import { mkdirSync } from "node:fs";
import { join } from "node:path";
import { reportingRuns, reportKey, type PulseRun } from "./sources.js";
import { acquireLock, countUnprocessed, LockBusyError, type WorkflowState } from "./state.js";

export interface BuildEvidence {
  /** `pulse-build:<id>-<attempt>`, or `localReportKey(log)` (`local-build:<path>@<mtimeMs>`) for a local log. */
  readonly key: string;
  /** Proof (SMT) timeouts found in the build log; a timed-out CI job counts as one. */
  readonly proofTimeouts: number;
  /** Local build log to hand to the workflow as a `reportPaths` entry; the run records the same key. */
  readonly reportPath?: string;
}

export interface ContinuityDecision {
  readonly retrigger: boolean;
  readonly reasons: string[];
  readonly newReports: string[];
  readonly unprocessedPartialRules: number;
  readonly buildTimeoutReports: string[];
  /** Verified integrations awaiting a live push (reported only; not a retrigger condition). */
  readonly pendingPublications: number;
  /** Run IDs to pass as the workflow's `pulseRunIds` input. */
  readonly pulseRunIds: string[];
  /** Local build logs to pass as `reportPaths`. */
  readonly reportPaths: string[];
}

export function evaluateContinuity(input: {
  runs: readonly PulseRun[];
  state: WorkflowState;
  now: Date;
  buildEvidence: readonly BuildEvidence[];
}): ContinuityDecision {
  const processed = (key: string) => key in input.state.processedReports;
  const reporting = reportingRuns(input.runs);
  const newRegressions = reporting.filter((run) => run.workflow === "regressions" && !processed(reportKey(run)));
  const evidence = new Map(input.buildEvidence.map((item) => [item.key, item]));
  const timedOutBuilds = reporting.filter((run) => {
    if (run.workflow !== "build" || processed(reportKey(run))) return false;
    return run.conclusion === "timed_out" || (evidence.get(reportKey(run))?.proofTimeouts ?? 0) > 0;
  });
  const localTimeouts = input.buildEvidence.filter((item) => item.key.startsWith("local-build:") && item.proofTimeouts > 0 && !processed(item.key));
  const unprocessedPartialRules = countUnprocessed(input.state, input.now, "partial-rule");
  const reasons: string[] = [];
  if (newRegressions.length > 0) reasons.push(`new Pulse report(s): ${newRegressions.map(reportKey).join(", ")}`);
  if (unprocessedPartialRules > 0) reasons.push(`${unprocessedPartialRules} partial proof rule famil${unprocessedPartialRules === 1 ? "y has" : "ies have"} not been processed`);
  const buildTimeoutReports = [...timedOutBuilds.map(reportKey), ...localTimeouts.map((item) => item.key)];
  if (buildTimeoutReports.length > 0) reasons.push(`checker build timed out on proofs: ${buildTimeoutReports.join(", ")}`);
  return {
    retrigger: reasons.length > 0,
    reasons,
    newReports: newRegressions.map(reportKey),
    unprocessedPartialRules,
    buildTimeoutReports,
    pendingPublications: input.state.pendingPublications.length,
    pulseRunIds: [...newRegressions, ...timedOutBuilds].map((run) => String(run.id)),
    reportPaths: localTimeouts.flatMap((item) => (item.reportPath ? [item.reportPath] : [])),
  };
}

export type LaunchOutcome<T> =
  | { readonly kind: "launched"; readonly value: T }
  /** Another launcher holds the lock: an overlapping schedule, not a failure. */
  | { readonly kind: "skipped"; readonly reason: string }
  /** The launcher could not take its lock at all (for example, an unusable state directory). */
  | { readonly kind: "failed"; readonly reason: string };

/**
 * Run `launch` while holding `<stateDir>/launcher.lock`, creating the state directory first (it
 * lives under the ignored `.atomic/`, so a fresh clone has none). Only a lock held by a live
 * owner skips the launch; any other locking error is a failure. Errors from `launch` propagate.
 */
export async function launchExclusively<T>(stateDir: string, launch: () => Promise<T>): Promise<LaunchOutcome<T>> {
  let release: () => void;
  try {
    mkdirSync(stateDir, { recursive: true });
    release = await acquireLock(join(stateDir, "launcher.lock"), { owner: `launcher-${process.pid}`, timeoutMs: 0, staleMs: 12 * 3_600_000 });
  } catch (error) {
    return { kind: error instanceof LockBusyError ? "skipped" : "failed", reason: (error as Error).message };
  }
  try {
    return { kind: "launched", value: await launch() };
  } finally {
    release();
  }
}

/**
 * Retrigger decision for the continuity launcher. The instructions name three conditions:
 * a new Pulse checker report, unprocessed partial proof rules, and an OCaml/Cherry checker build
 * that times out because of proof timeouts. A bounded workflow run never retriggers itself;
 * the launcher (or a scheduler that invokes it) evaluates these conditions between runs.
 */
import { reportingRuns, reportKey, type PulseRun } from "./sources.js";
import { countUnprocessed, type WorkflowState } from "./state.js";

export interface BuildEvidence {
  /** `pulse-build:<id>-<attempt>` or `local-build:<path>@<mtimeMs>`. */
  readonly key: string;
  /** Proof (SMT) timeouts found in the build log; a timed-out CI job counts as one. */
  readonly proofTimeouts: number;
  /** Local report directory to hand to the workflow, for local build logs. */
  readonly reportPath?: string;
}

export interface ContinuityDecision {
  readonly retrigger: boolean;
  readonly reasons: string[];
  readonly newReports: string[];
  readonly unprocessedPartialRules: number;
  readonly buildTimeoutReports: string[];
  /** Run IDs to pass as the workflow's `pulseRunIds` input. */
  readonly pulseRunIds: string[];
  /** Local report directories to pass as `reportPaths`. */
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
    pulseRunIds: [...newRegressions, ...timedOutBuilds].map((run) => String(run.id)),
    reportPaths: localTimeouts.flatMap((item) => (item.reportPath ? [item.reportPath] : [])),
  };
}

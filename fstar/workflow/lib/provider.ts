/**
 * Provider failures of agent stages.
 *
 * Atomic records a stage that sets no `model` as completed even when its agent turn ended on a
 * provider error: the turn's last assistant message has `stopReason: "error"` and an
 * `errorMessage`, the output artifact is empty, and `WorkflowTaskResult` carries no error field.
 * Only the stage session holds that evidence, so after each group of agent stages the workflow
 * reads the stages' sessions by `sessionId` (lib/stage-sessions.ts) and classifies them here:
 *
 * - `provider-policy-blocked`: a safety or content-policy rejection (for example GitHub Copilot's
 *   `cyber_policy`). It is a provider restriction, not a proof failure. The slice's findings are
 *   held until an operator requeues them; the run reports it as blocked. Nothing here retries it,
 *   rewords the prompt, or moves the stage to another model.
 * - `provider-unavailable`: any other provider or transport error after Atomic's own same-model
 *   retries (`settings.retry`). The findings stay open with no attempt counted.
 */
import { readFileSync } from "node:fs";
import { join } from "node:path";
import type { PolicyHold } from "./state.js";
import { readStageSessionMessages, type RunStageSessions } from "./stage-sessions.js";

export type ProviderFailureKind = "provider-policy-blocked" | "provider-unavailable";

export type ProviderFailure = {
  readonly kind: ProviderFailureKind;
  /** Provider error code when the message carries one (for example `cyber_policy`). */
  readonly code?: string;
  /** The provider's error message, at most 400 characters. */
  readonly error: string;
};

/** Error codes of safety and content-policy rejections (`cyber_policy`, `content_filter`, `content_policy_violation`, …). */
const POLICY_CODE = /(?:^|_)(?:policy|safety)(?:_|$)|content_?filter|responsible_?ai/i;
/** Wording of safety and content-policy rejections that carry no code. */
const POLICY_TEXT = [/flagged for possible/i, /content (?:management )?polic(?:y|ies)/i, /\bcontent[_ -]?filter/i, /usage polic(?:y|ies)/i, /safety (?:system|polic)/i];

/** Classify a provider error message; anything that is not a policy rejection is `provider-unavailable`. */
export function classifyProviderError(message: string): ProviderFailure {
  // Codes appear in JSON bodies, also inside wrapped stream errors ("reading SSE event: {...}").
  const codes = [...message.matchAll(/"code"\s*:\s*"([^"]+)"/g)].flatMap((match) => (match[1] ? [match[1]] : []));
  const policyCode = codes.find((code) => POLICY_CODE.test(code));
  const policy = policyCode !== undefined || POLICY_TEXT.some((pattern) => pattern.test(message));
  const code = policyCode ?? codes[0];
  return { kind: policy ? "provider-policy-blocked" : "provider-unavailable", ...(code ? { code } : {}), error: message.trim().slice(0, 400) };
}

/** The error of a session whose last assistant message ended on a provider error; undefined otherwise. */
export function terminalAssistantFailure(messages: readonly unknown[]): string | undefined {
  for (let index = messages.length - 1; index >= 0; index -= 1) {
    const message = messages[index] as { role?: unknown; stopReason?: unknown; errorMessage?: unknown } | undefined;
    if (message?.role !== "assistant") continue;
    if (message.stopReason !== "error") return undefined;
    return typeof message.errorMessage === "string" && message.errorMessage.trim() ? message.errorMessage : "the provider ended the turn with an error and no message";
  }
  return undefined;
}

/** Transient provider failures that reject a stage (as opposed to workflow or contract errors). */
const TRANSIENT_REJECTION = /rate.?limit|too many requests|\b429\b|\b5\d\d\b|overloaded|unavailable|timed? ?out|timeout|stream ended|connection|socket|network|fetch failed|empty completion|provider/i;

export type StageOutcomeKind = "completed" | "failed" | ProviderFailureKind;

/** How one agent stage ended, with the evidence a report or a held finding records. */
export type StageOutcome = {
  readonly stage: string;
  readonly kind: StageOutcomeKind;
  readonly sessionId?: string;
  readonly code?: string;
  /** The provider error, or the stage's rejection. */
  readonly error?: string;
  readonly at: string;
  /** Why the session could not be inspected (the outcome then rests on the task result alone). */
  readonly note?: string;
};

export const isProviderFailure = (outcome: StageOutcome | null | undefined): outcome is StageOutcome & { kind: ProviderFailureKind } =>
  outcome?.kind === "provider-policy-blocked" || outcome?.kind === "provider-unavailable";

/** One line of evidence: stage, outcome, code, session and (unless `withError` is false) the error. */
export function describeOutcome(outcome: StageOutcome, withError = true): string {
  const session = outcome.sessionId ? ` in session ${outcome.sessionId}` : "";
  const code = outcome.code ? ` (${outcome.code})` : "";
  return `${outcome.stage} ended ${outcome.kind}${code}${session}${withError ? `: ${outcome.error ?? "no error recorded"}` : ""}`;
}

/**
 * Classify settled agent stages. A fulfilled stage is a provider failure when its session's last
 * assistant message ended on an error; a rejected stage is classified from its error.
 */
export async function classifyStages(
  cwd: string,
  names: readonly string[],
  settled: ReadonlyArray<PromiseSettledResult<{ readonly sessionId?: string }>>,
  now = new Date(),
): Promise<StageOutcome[]> {
  const at = now.toISOString();
  const sessionIds = settled.flatMap((item) => (item.status === "fulfilled" && item.value.sessionId ? [item.value.sessionId] : []));
  let sessions: Record<string, readonly unknown[]> = {};
  let unreadable: string | undefined;
  if (sessionIds.length > 0) {
    try {
      sessions = await readStageSessionMessages(cwd, sessionIds);
    } catch (error) {
      unreadable = `stage sessions could not be read: ${error instanceof Error ? error.message : String(error)}`;
    }
  }
  return settled.map((item, index): StageOutcome => {
    const stage = names[index] ?? `stage-${index}`;
    if (item.status === "rejected") {
      const message = item.reason instanceof Error ? item.reason.message : String(item.reason);
      const failure = classifyProviderError(message);
      const kind = failure.kind === "provider-policy-blocked" ? failure.kind : TRANSIENT_REJECTION.test(message) ? "provider-unavailable" : "failed";
      return { stage, kind, ...(kind !== "failed" && failure.code ? { code: failure.code } : {}), error: failure.error, at };
    }
    const sessionId = item.value.sessionId;
    const messages = sessionId ? sessions[sessionId] : undefined;
    const ids = sessionId ? { sessionId } : {};
    if (!messages) return { stage, kind: "completed", ...ids, at, note: unreadable ?? (sessionId ? `session ${sessionId} was not found` : "the stage reported no session") };
    const error = terminalAssistantFailure(messages);
    if (error === undefined) return { stage, kind: "completed", ...ids, at };
    const failure = classifyProviderError(error);
    return { stage, kind: failure.kind, ...ids, ...(failure.code ? { code: failure.code } : {}), error: failure.error, at };
  });
}

/** How each agent stage of an earlier run ended, from its session (see `readRunStageSessions`). */
export type RunStageOutcome = Omit<StageOutcome, "at">;

export function classifyRunStages(run: RunStageSessions): RunStageOutcome[] {
  return run.stages.map(({ stage, sessionId }): RunStageOutcome => {
    const messages = sessionId ? run.sessions[sessionId] : undefined;
    const ids = sessionId ? { sessionId } : {};
    if (!messages) return { stage, kind: "completed", ...ids, note: sessionId ? `session ${sessionId} was not found` : "no session was recorded" };
    const error = terminalAssistantFailure(messages);
    if (error === undefined) return { stage, kind: "completed", ...ids };
    const failure = classifyProviderError(error);
    return { stage, kind: failure.kind, ...ids, ...(failure.code ? { code: failure.code } : {}), error: failure.error };
  });
}

function readJsonOr<T>(path: string, fallback: T): T {
  try {
    return JSON.parse(readFileSync(path, "utf8")) as T;
  } catch {
    return fallback;
  }
}

/**
 * The findings to hold for an earlier run's policy-blocked stages: a slice's repair or verify
 * stage holds the slice's findings (`iter-<n>/plan.json`), an integration verify stage holds what
 * that integration contained (`iter-<n>/integration.json`). Investigation stages hold nothing.
 */
export function policyHoldsFromRun(run: { runId?: string; runKey: string; runDir: string; at: string; stages: readonly RunStageOutcome[] }): PolicyHold[] {
  const holds = new Map<string, PolicyHold>();
  for (const outcome of run.stages) {
    if (outcome.kind !== "provider-policy-blocked") continue;
    const integration = /^iter-(\d+)\/integration\/verify$/.exec(outcome.stage);
    const slice = /^iter-(\d+)\/([^/]+)\/(?:repair|verify)$/.exec(outcome.stage);
    let fingerprints: string[] = [];
    if (integration) {
      const contents = readJsonOr<{ contents?: Array<{ fingerprints?: string[] }> }>(join(run.runDir, `iter-${integration[1]}`, "integration.json"), {}).contents ?? [];
      fingerprints = contents.flatMap((item) => item.fingerprints ?? []);
    } else if (slice) {
      const plan = readJsonOr<{ slices?: Array<{ id: string; fingerprints?: string[] }> }>(join(run.runDir, `iter-${slice[1]}`, "plan.json"), {});
      fingerprints = plan.slices?.find((item) => item.id === slice[2])?.fingerprints ?? [];
    }
    const block = {
      runKey: run.runKey, ...(run.runId ? { runId: run.runId } : {}), stage: outcome.stage,
      ...(outcome.sessionId ? { sessionId: outcome.sessionId } : {}), ...(outcome.code ? { code: outcome.code } : {}),
      error: outcome.error ?? "provider policy rejection", at: run.at,
    };
    for (const fingerprint of fingerprints) if (!holds.has(fingerprint)) holds.set(fingerprint, { fingerprint, block });
  }
  return [...holds.values()];
}

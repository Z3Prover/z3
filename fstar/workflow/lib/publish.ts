/**
 * Publication lifecycle: keep pushing verified improvements to one branch until its PR is merged
 * or the branch is deleted, then start a new branch and PR. All git/gh calls go through the
 * injectable runner; only `mode: "live"` issues remote mutations, and every mutation is
 * preceded by a read-only check so re-running a publication never duplicates a PR or issue.
 */
import { readFileSync, writeFileSync } from "node:fs";
import { runChecked, type CommandRunner } from "./command.js";
import type { PublicationState } from "./state.js";

export type PublishMode = "none" | "dry-run" | "live";

export type RemotePr = {
  readonly number: number;
  readonly state: "OPEN" | "MERGED" | "CLOSED";
  readonly url: string;
  readonly mergedAt?: string;
};

export interface PublicationFacts {
  /** False when the remote was not queried (workflow dry run); the plan then relies on state only. */
  readonly known: boolean;
  readonly branchExists: boolean;
  readonly prs: readonly RemotePr[];
  /** First unused `<prefix>/<n>` branch name after the recorded sequence. */
  readonly freeBranch: string;
}

export type PublicationAction =
  | { kind: "push-existing"; branch: string; pr?: RemotePr; reason: string }
  | { kind: "push-and-open-pr"; branch: string; reason: string }
  | { kind: "new-branch"; branch: string; sequence: number; previous?: { branch: string; state: string; pr?: RemotePr }; reason: string }
  | { kind: "blocked"; branch: string; reason: string }
  | { kind: "nothing-to-publish"; reason: string };

export interface PublicationPlan {
  readonly action: PublicationAction;
  readonly facts: PublicationFacts;
  /** The publication state the plan was computed from. */
  readonly state: PublicationState;
}

export interface RemoteOptions {
  readonly repo: string;
  readonly remote: string;
  readonly prefix: string;
  readonly cwd: string;
  readonly timeoutMs: number;
  readonly signal?: AbortSignal;
}

function sequenceOf(branch: string, prefix: string): number {
  const match = new RegExp(`^${prefix.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}/(\\d+)$`).exec(branch);
  return match?.[1] ? Number(match[1]) : 0;
}

async function remoteBranchExists(runner: CommandRunner, branch: string, options: RemoteOptions): Promise<boolean> {
  const output = await runChecked(runner, ["git", "ls-remote", "--heads", options.remote, branch], options);
  return output.split(/\r?\n/).some((line) => line.endsWith(`refs/heads/${branch}`));
}

async function listPrs(runner: CommandRunner, branch: string, state: "all" | "open", options: RemoteOptions): Promise<RemotePr[]> {
  const output = await runChecked(runner, [
    "gh", "pr", "list", "--repo", options.repo, "--head", branch, "--state", state, "--json", "number,state,url,mergedAt", "--limit", "20",
  ], options);
  return output === "" ? [] : (JSON.parse(output) as RemotePr[]);
}

/** Read-only: whether a branch exists on the remote, and every PR from it. */
export async function remoteBranchStatus(runner: CommandRunner, branch: string, options: RemoteOptions): Promise<{ branchExists: boolean; prs: RemotePr[] }> {
  return { branchExists: await remoteBranchExists(runner, branch, options), prs: await listPrs(runner, branch, "all", options) };
}

/** Read-only queries about the active branch and the next free branch name. */
export async function gatherPublicationFacts(runner: CommandRunner, state: PublicationState, options: RemoteOptions): Promise<PublicationFacts> {
  const branch = state.activeBranch;
  const { branchExists, prs } = branch ? await remoteBranchStatus(runner, branch, options) : { branchExists: false, prs: [] };
  let freeBranch = "";
  for (let sequence = Math.max(state.sequence, branch ? sequenceOf(branch, options.prefix) : 0) + 1, tries = 0; tries < 20; sequence += 1, tries += 1) {
    const candidate = `${options.prefix}/${sequence}`;
    if (!(await remoteBranchExists(runner, candidate, options))) {
      freeBranch = candidate;
      break;
    }
  }
  if (freeBranch === "") throw new Error(`No free ${options.prefix}/<n> branch name found after 20 attempts`);
  return { known: true, branchExists, prs, freeBranch };
}

/** What happens to the active branch, given what the remote says about it. */
export type BranchDecision =
  | { kind: "push-existing"; pr: RemotePr; reason: string }
  | { kind: "push-and-open-pr"; reason: string }
  | { kind: "new-branch"; previous: { state: "MERGED" | "DELETED"; pr?: RemotePr }; reason: string }
  | { kind: "blocked"; reason: string };

/**
 * The one branch lifecycle rule, used both to choose the integration base and to plan the push:
 * an open PR keeps the branch (even if an earlier PR from it merged); otherwise a merged PR or a
 * deleted branch starts a new branch; a PR closed without merging blocks; a branch without a PR
 * gets one. Deterministic in the facts.
 */
export function decideActiveBranch(branch: string, facts: Pick<PublicationFacts, "branchExists" | "prs">): BranchDecision {
  const open = facts.prs.find((pr) => pr.state === "OPEN");
  if (open) return { kind: "push-existing", pr: open, reason: `PR #${open.number} is open` };
  const merged = facts.prs.find((pr) => pr.state === "MERGED");
  if (merged) return { kind: "new-branch", previous: { state: "MERGED", pr: merged }, reason: `PR #${merged.number} was merged` };
  if (!facts.branchExists) return { kind: "new-branch", previous: { state: "DELETED", pr: facts.prs[0] }, reason: `branch ${branch} was deleted` };
  const closed = facts.prs.find((pr) => pr.state === "CLOSED");
  if (closed) {
    return { kind: "blocked", reason: `PR #${closed.number} for ${branch} was closed without merging; reopen it, or delete ${branch} so the next run starts a new branch and PR (and reopens its findings)` };
  }
  return { kind: "push-and-open-pr", reason: `${branch} exists without a PR` };
}

/** Decide where verified changes go, following the instructions' branch/PR lifecycle. */
export function planPublication(state: PublicationState, facts: PublicationFacts, options: { prefix: string; hasChanges: boolean }): PublicationPlan {
  const plan = (action: PublicationAction): PublicationPlan => ({ action, facts, state });
  if (!options.hasChanges) return plan({ kind: "nothing-to-publish", reason: "no verified changes to publish" });
  const nextBranch = facts.known ? facts.freeBranch : `${options.prefix}/${state.sequence + 1}`;
  const branch = state.activeBranch;
  if (!branch) {
    return plan({ kind: "new-branch", branch: nextBranch, sequence: sequenceOf(nextBranch, options.prefix), reason: "no active publication branch" });
  }
  if (!facts.known) {
    return plan({ kind: "push-existing", branch, reason: "remote not queried in a dry run; a live run re-checks the branch and PR first" });
  }
  const decision = decideActiveBranch(branch, facts);
  if (decision.kind === "new-branch") {
    return plan({ kind: "new-branch", branch: nextBranch, sequence: sequenceOf(nextBranch, options.prefix), previous: { branch, ...decision.previous }, reason: decision.reason });
  }
  return plan({ ...decision, branch });
}

export interface ExecuteOptions extends RemoteOptions {
  readonly mode: PublishMode;
  readonly base: string;
  readonly title: string;
  readonly bodyFile: string;
}

export interface PublicationResult {
  readonly executed: boolean;
  readonly state: PublicationState;
  readonly summary: string;
  readonly prUrl?: string;
  /** Why a live push was refused (the remote branch has commits the integration does not contain). */
  readonly blocked?: string;
}

async function ensurePr(runner: CommandRunner, branch: string, options: ExecuteOptions): Promise<RemotePr> {
  const existing = (await listPrs(runner, branch, "open", options))[0];
  if (existing) return existing;
  const url = (await runChecked(runner, [
    "gh", "pr", "create", "--repo", options.repo, "--base", options.base, "--head", branch, "--title", options.title, "--body-file", options.bodyFile,
  ], options)).split(/\r?\n/).pop() ?? "";
  return { number: Number(url.split("/").pop()), state: "OPEN", url };
}

/**
 * Carry out a plan. Non-live modes return the unchanged state and describe the intended effect.
 * Pushes are never forced: a push the remote rejects as non-fast-forward ends blocked.
 */
export async function executePublication(runner: CommandRunner, plan: PublicationPlan, options: ExecuteOptions): Promise<PublicationResult> {
  const { action } = plan;
  const describe = action.kind === "nothing-to-publish" || action.kind === "blocked"
    ? `${action.kind}: ${action.reason}`
    : `${action.kind} ${action.branch}: ${action.reason}`;
  if (options.mode !== "live" || action.kind === "nothing-to-publish" || action.kind === "blocked") {
    return { executed: false, state: plan.state, summary: options.mode === "live" ? describe : `${options.mode}: would ${describe}` };
  }
  const push = await runner(["git", "push", options.remote, `HEAD:refs/heads/${action.branch}`], options);
  if (push.code !== 0) {
    if (/non-fast-forward|\[rejected\]|fetch first/i.test(`${push.stderr}\n${push.stdout}`)) {
      const blocked = `push to ${action.branch} was rejected as non-fast-forward: the remote branch has commits the verified integration does not contain; inspect them, then merge them into ${action.branch}'s PR or delete the branch, and relaunch (the verified work stays pending)`;
      return { executed: false, state: plan.state, summary: `blocked: ${blocked}`, blocked };
    }
    throw new Error(`git push ${options.remote} HEAD:refs/heads/${action.branch} failed (exit ${push.code}): ${push.stderr.trim()}`);
  }
  const pr = action.kind === "push-existing" && action.pr ? action.pr : await ensurePr(runner, action.branch, options);
  const previous = plan.state;
  const history = action.kind === "new-branch" && action.previous
    ? [...previous.history, { branch: action.previous.branch, prNumber: action.previous.pr?.number, prUrl: action.previous.pr?.url, state: action.previous.state, at: new Date().toISOString() }]
    : previous.history;
  return {
    executed: true,
    state: {
      activeBranch: action.branch,
      prNumber: pr.number,
      prUrl: pr.url,
      sequence: action.kind === "new-branch" ? Math.max(previous.sequence, action.sequence) : previous.sequence,
      history,
    },
    summary: describe,
    prUrl: pr.url,
  };
}

export interface BugReportDraft {
  readonly fingerprint: string;
  readonly title: string;
  readonly bodyFile: string;
}

export type BugReportResult = {
  readonly fingerprint: string;
  readonly action: "existing" | "created" | "would-create";
  readonly url?: string;
};

export function bugReportMarker(fingerprint: string): string {
  return `fstar-proof-checking:crash:${fingerprint}`;
}

/** File crash reports upstream once per fingerprint; non-live modes only search. */
export async function fileBugReports(
  runner: CommandRunner,
  drafts: readonly BugReportDraft[],
  options: { repo: string; mode: PublishMode; timeoutMs: number; signal?: AbortSignal },
): Promise<BugReportResult[]> {
  const results: BugReportResult[] = [];
  for (const draft of drafts) {
    const marker = bugReportMarker(draft.fingerprint);
    const found = await runChecked(runner, [
      "gh", "issue", "list", "--repo", options.repo, "--state", "all", "--search", `"${marker}" in:body`, "--json", "number,url", "--limit", "5",
    ], options);
    const existing = found === "" ? [] : (JSON.parse(found) as Array<{ number: number; url: string }>);
    if (existing[0]) {
      results.push({ fingerprint: draft.fingerprint, action: "existing", url: existing[0].url });
      continue;
    }
    if (options.mode !== "live") {
      results.push({ fingerprint: draft.fingerprint, action: "would-create" });
      continue;
    }
    // The hidden marker makes the report findable by the duplicate search above.
    const marked = `${draft.bodyFile}.marked.md`;
    writeFileSync(marked, `${readFileSync(draft.bodyFile, "utf8").trimEnd()}

<!-- ${marker} -->
`, "utf8");
    const url = (await runChecked(runner, ["gh", "issue", "create", "--repo", options.repo, "--title", draft.title, "--body-file", marked], options))
      .split(/\r?\n/).pop() ?? "";
    results.push({ fingerprint: draft.fingerprint, action: "created", url });
  }
  return results;
}

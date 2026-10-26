/**
 * Persistent, concurrency-safe workflow state: processed reports, per-finding progress with
 * exponential backoff, active publication branch/PR, and drafted bug reports.
 *
 * Every read-modify-write runs under an exclusive lock file and replaces `state.json` with
 * write-to-temporary-then-rename, so concurrent launches and crashed runs cannot corrupt it.
 */
import { closeSync, existsSync, mkdirSync, openSync, readFileSync, renameSync, rmSync, writeFileSync } from "node:fs";
import { hostname } from "node:os";
import { join } from "node:path";
import { evidenceDigest, type Finding, type FindingKind } from "./reports.js";
import type { Theory } from "./theories.js";

/**
 * Finding status machine (see README "State and evidence"):
 * open → in_progress → integrated (verified, merged into a local integration branch, awaiting a live push)
 * → resolved (published on a branch/PR, awaiting merge) → merged (its PR merged).
 * Failures go to unverified (backoff) and, after the attempt limit, blocked (reopened by new evidence).
 * Reopen edges back to open: resolved whose publication was lost (branch deleted before its PR merged),
 * merged with changed report evidence produced after the merge, and integrated with no pending publication.
 * A stage the provider rejected for policy holds its findings in provider_policy_blocked (no attempt,
 * no backoff, never picked up automatically) until an explicit requeue; a provider outage reopens them.
 * A run that ended without recording outcomes (crashed or stopped) has its claims released to open;
 * a finding whose slice branch carries that run's unverified commit keeps it as `candidate`, which
 * keeps the open finding out of automatic work until an operator releases it.
 */
export type FindingStatus = "open" | "in_progress" | "integrated" | "resolved" | "merged" | "unverified" | "blocked" | "provider_policy_blocked";
export type SliceOutcome = "verified" | "unverified" | "rejected" | "no-change" | "integration-conflict" | "provider-policy-blocked" | "provider-unavailable";

/** Evidence of the provider policy rejection (for example `cyber_policy`) that holds a finding. */
export type ProviderBlock = {
  /** Workflow run whose agent stage was rejected, and its Atomic run id when known. */
  runKey: string;
  runId?: string;
  stage: string;
  sessionId?: string;
  code?: string;
  /** The provider's error message (at most 400 characters). */
  error: string;
  at: string;
};

/** Where a finding's verified change was pushed. */
export interface PublicationLink {
  branch: string;
  prNumber?: number;
  prUrl?: string;
  /** The integration head that was pushed. */
  head?: string;
  at: string;
}

/** Unverified work that a run committed on a finding's slice branch before it ended without an outcome. */
export type CandidateWork = {
  runKey: string;
  branch: string;
  /** The branch head when the run's claim was released. */
  commit: string;
};

/** One status change and why it happened; a reopen keeps the publication it replaced, a requeue the provider block, a released candidate the candidate. */
export interface FindingTransition {
  at: string;
  from: FindingStatus;
  to: FindingStatus;
  reason: string;
  publication?: PublicationLink;
  mergedAt?: string;
  providerBlock?: ProviderBlock;
  candidate?: CandidateWork;
}

export interface FindingRecord {
  fingerprint: string;
  kind: FindingKind;
  theory: Theory;
  rule: string;
  detail: string;
  status: FindingStatus;
  attempts: number;
  firstSeen: string;
  lastSeen: string;
  evidenceDigest: string;
  nextEligibleAt?: string;
  claimedBy?: string;
  claimedAt?: string;
  lastOutcome?: string;
  lastRunKey?: string;
  /** The latest observation, so later runs can re-source the finding without its original report. */
  snapshot?: Finding;
  /** Set while resolved or merged: the branch/PR that carries the verified change. */
  publishedOn?: PublicationLink;
  /** When the PR in `publishedOn` merged (status `merged`). */
  mergedAt?: string;
  /** Why a resolved or merged finding was last kept despite new observations. */
  keptReason?: string;
  /** Set while provider_policy_blocked: the rejected stage, session, code and time. */
  providerBlock?: ProviderBlock;
  /**
   * Unverified committed work of an interrupted run. While set, the finding is not triaged, re-sourced
   * or counted for the continuity retrigger: verify the commit explicitly, then release it
   * (continuity.ts --release-candidate) to let automatic runs repair the finding again.
   */
  candidate?: CandidateWork;
  /** The most recent status changes, oldest first. */
  transitions?: FindingTransition[];
}

const MAX_TRANSITIONS = 10;

/** Change a record's status, recording why; the reason is part of the record. */
function transition(record: FindingRecord, to: FindingStatus, reason: string, at: string, extra: Partial<FindingTransition> = {}): FindingRecord {
  const entry: FindingTransition = { at, from: record.status, to, reason, ...extra };
  return { ...record, status: to, transitions: [...(record.transitions ?? []), entry].slice(-MAX_TRANSITIONS) };
}

/** Back to `open`, keeping in the transition the publication (and merge) being given up. */
function reopen(record: FindingRecord, reason: string, at: string, evidence?: string): FindingRecord {
  const { publishedOn, mergedAt, keptReason: _kept, nextEligibleAt: _next, claimedBy: _by, claimedAt: _claimed, ...rest } = record;
  const reopened = transition(rest, "open", reason, at, { ...(publishedOn ? { publication: publishedOn } : {}), ...(mergedAt ? { mergedAt } : {}) });
  return { ...reopened, attempts: 0, lastOutcome: `reopened: ${reason}`, ...(evidence ? { evidenceDigest: evidence } : {}) };
}

export type PublicationRecord = {
  branch: string;
  prNumber?: number;
  prUrl?: string;
  state: string;
  at: string;
};

export type PublicationState = {
  /** Branch that receives pushes until it is deleted or its PR is merged. */
  activeBranch?: string;
  prNumber?: number;
  prUrl?: string;
  /** Monotonic counter used to name the next branch after a merge or deletion. */
  sequence: number;
  history: PublicationRecord[];
};

/** Verified, locally integrated work that a later `publish=live` run must still push. */
export interface PendingPublication {
  /** Run that verified and integrated the work. */
  runKey: string;
  /** Local integration branch and the verified head it pointed to. */
  branch: string;
  head: string;
  fingerprints: string[];
  slices: string[];
  recordedAt: string;
  /** Why the last live run could not include it (missing branch, merge conflict, soundness scan). */
  lastError?: string;
}

export interface WorkflowState {
  version: 1;
  processedReports: Record<string, { processedAt: string; findings: number }>;
  findings: Record<string, FindingRecord>;
  publication: PublicationState;
  /** Oldest first; cleared only after a live push that includes them succeeds. */
  pendingPublications: PendingPublication[];
  bugReports: Record<string, { draft: string; issueUrl?: string; filedAt?: string }>;
  /** Rotating scan position per local corpus and checker (batch corpora: also per logic directory). */
  localScans: Record<string, { at: string; offset: number; groupOffsets?: Record<string, number> }>;
  investigation?: { digest: string; at: string };
  runs: Array<{ runKey: string; startedAt: string; endedAt?: string; stopReason?: string; verified: number; attempted: number }>;
}

export function emptyState(): WorkflowState {
  return {
    version: 1,
    processedReports: {},
    findings: {},
    publication: { sequence: 0, history: [] },
    pendingPublications: [],
    bugReports: {},
    localScans: {},
    runs: [],
  };
}

export const STATE_FILE = "state.json";
export const LOCK_FILE = "state.lock";

export function readState(stateDir: string): WorkflowState {
  const path = join(stateDir, STATE_FILE);
  if (!existsSync(path)) return emptyState();
  const parsed = JSON.parse(readFileSync(path, "utf8")) as WorkflowState;
  if (parsed.version !== 1) throw new Error(`Unsupported workflow state version in ${path}`);
  return { ...emptyState(), ...parsed };
}

/** Windows reports these while another process briefly holds or is deleting a file. */
const TRANSIENT_WINDOWS_CODES = new Set(["EPERM", "EBUSY", "EACCES"]);

/** Replace a JSON file atomically: write a sibling temporary file, then rename over the target. */
export function writeJsonAtomic(path: string, value: unknown): void {
  const temporary = `${path}.tmp-${process.pid}-${Math.random().toString(16).slice(2)}`;
  writeFileSync(temporary, `${JSON.stringify(value, null, 2)}\n`, { encoding: "utf8", flag: "wx" });
  for (let attempt = 1; ; attempt += 1) {
    try {
      renameSync(temporary, path);
      return;
    } catch (error) {
      // Windows refuses to replace a file that an unlocked reader has open for a moment; retry briefly.
      if (attempt < 20 && TRANSIENT_WINDOWS_CODES.has((error as NodeJS.ErrnoException).code ?? "")) {
        Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25);
        continue;
      }
      rmSync(temporary, { force: true });
      throw error;
    }
  }
}

interface LockRecord {
  owner: string;
  pid: number;
  host: string;
  acquiredAt: number;
}

export interface LockOptions {
  readonly owner: string;
  /** Give up waiting after this many milliseconds. */
  readonly timeoutMs?: number;
  /** A lock older than this is presumed abandoned. Critical sections are short, so 10 minutes is ample. */
  readonly staleMs?: number;
}

function processAlive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) {
    return (error as NodeJS.ErrnoException).code === "EPERM";
  }
}

function readLock(path: string): LockRecord | undefined {
  try {
    return JSON.parse(readFileSync(path, "utf8")) as LockRecord;
  } catch {
    return undefined;
  }
}

const sleep = (ms: number) => new Promise((resolve) => setTimeout(resolve, ms));

/** The lock is held by another (live) owner: contention, as opposed to a failure to lock at all. */
export class LockBusyError extends Error {
  override readonly name = "LockBusyError";
}

/**
 * Acquire an exclusive lock file. Returns a release function. Abandoned locks (older than
 * `staleMs`, or held by a dead process on this host) are reclaimed by renaming them aside and
 * confirming the renamed file is the abandoned one, so two reclaimers cannot both win.
 */
export async function acquireLock(path: string, options: LockOptions): Promise<() => void> {
  const timeoutMs = options.timeoutMs ?? 30_000;
  const staleMs = options.staleMs ?? 10 * 60_000;
  const deadline = Date.now() + timeoutMs;
  const record: LockRecord = { owner: options.owner, pid: process.pid, host: hostname(), acquiredAt: Date.now() };
  for (let delay = 10; ; delay = Math.min(delay * 2, 250)) {
    try {
      const descriptor = openSync(path, "wx");
      try {
        writeFileSync(descriptor, JSON.stringify({ ...record, acquiredAt: Date.now() }));
      } finally {
        closeSync(descriptor);
      }
      return () => {
        const current = readLock(path);
        if (current?.pid !== record.pid || current.owner !== record.owner) return;
        for (let attempt = 1; ; attempt += 1) {
          try {
            rmSync(path, { force: true });
            return;
          } catch (error) {
            if (attempt >= 40 || !TRANSIENT_WINDOWS_CODES.has((error as NodeJS.ErrnoException).code ?? "")) throw error;
            Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 25);
          }
        }
      };
    } catch (error) {
      const code = (error as NodeJS.ErrnoException).code ?? "";
      // On Windows a lock file that another process is deleting ("delete pending") or briefly
      // reading refuses to open with EPERM/EACCES/EBUSY; that is contention, not a failure.
      if (code !== "EEXIST" && !TRANSIENT_WINDOWS_CODES.has(code)) throw error;
      if (code !== "EEXIST") {
        // Still contention only while a lock file exists; otherwise it is a genuine access failure.
        if (Date.now() >= deadline) throw existsSync(path) ? new LockBusyError(`Lock ${path} is busy (${code})`) : error;
        await sleep(delay);
        continue;
      }
    }
    const holder = readLock(path);
    const abandoned = holder !== undefined && (
      Date.now() - holder.acquiredAt > staleMs || (holder.host === hostname() && !processAlive(holder.pid))
    );
    if (abandoned) {
      const aside = `${path}.stale-${process.pid}-${Math.random().toString(16).slice(2)}`;
      try {
        renameSync(path, aside);
        const moved = readLock(aside);
        if (moved?.acquiredAt === holder.acquiredAt && moved.pid === holder.pid) rmSync(aside, { force: true });
        else if (!existsSync(path)) renameSync(aside, path);
        else rmSync(aside, { force: true });
      } catch {
        // Another process reclaimed or released it first; retry normally.
      }
      continue;
    }
    if (Date.now() >= deadline) {
      throw new LockBusyError(`State is locked by ${holder?.owner ?? "an unknown owner"} (pid ${holder?.pid ?? "?"}) at ${path}`);
    }
    await sleep(delay);
  }
}

/**
 * Run a read-modify-write against `state.json` under the state lock. Returning `state` persists
 * it atomically; throwing leaves the stored state unchanged.
 */
export async function withStateLock<T>(
  stateDir: string,
  mutate: (state: WorkflowState) => { state?: WorkflowState; result: T } | Promise<{ state?: WorkflowState; result: T }>,
  options: Partial<LockOptions> = {},
): Promise<T> {
  mkdirSync(stateDir, { recursive: true });
  const release = await acquireLock(join(stateDir, LOCK_FILE), { owner: options.owner ?? `pid-${process.pid}`, ...options });
  try {
    const outcome = await mutate(readState(stateDir));
    if (outcome.state) writeJsonAtomic(join(stateDir, STATE_FILE), outcome.state);
    return outcome.result;
  } finally {
    release();
  }
}

const KIND_PRIORITY: Record<FindingKind, number> = {
  crash: 0,
  rejected: 1,
  "build-timeout": 2,
  "partial-rule": 3,
  "check-timeout": 4,
  "slow-obligation": 5,
};

/** Crashes and possible unsoundness first, then build timeouts, then the most widespread proof gaps. */
export function compareFindings(left: Finding, right: Finding): number {
  return KIND_PRIORITY[left.kind] - KIND_PRIORITY[right.kind]
    || right.soleFamilyProofs - left.soleFamilyProofs
    || right.affectedProofs - left.affectedProofs
    || right.obligations - left.obligations
    || (right.milliseconds ?? 0) - (left.milliseconds ?? 0)
    || left.fingerprint.localeCompare(right.fingerprint);
}

export interface TriageOptions {
  readonly now: Date;
  /** Restrict to these theories; empty or omitted means all. */
  readonly theories?: readonly Theory[];
  /** Fingerprints already planned earlier in this run. */
  readonly exclude?: ReadonlySet<string>;
  /** In-progress claims older than this are presumed abandoned (default 24 h). */
  readonly claimTtlMs?: number;
}

export interface TriageResult {
  readonly actionable: Finding[];
  readonly skipped: Record<string, number>;
}

export function triageFindings(findings: readonly Finding[], state: WorkflowState, options: TriageOptions): TriageResult {
  const now = options.now.getTime();
  const claimTtl = options.claimTtlMs ?? 24 * 3_600_000;
  const skipped: Record<string, number> = {};
  const skip = (reason: string) => {
    skipped[reason] = (skipped[reason] ?? 0) + 1;
  };
  const actionable: Finding[] = [];
  const pending = pendingFingerprints(state);
  for (const finding of findings) {
    if (options.theories && options.theories.length > 0 && !options.theories.includes(finding.theory)) {
      skip("theory-filter");
      continue;
    }
    if (options.exclude?.has(finding.fingerprint)) {
      skip("planned-this-run");
      continue;
    }
    const record = state.findings[finding.fingerprint];
    if (record?.status === "resolved" || record?.status === "merged" || (record?.status === "integrated" && pending.has(record.fingerprint))) {
      // Published or merged work is not repaired again (reopening is explicit); integrated work awaits its pending publication.
      skip(record.status);
      continue;
    }
    if (record?.status === "blocked" && record.evidenceDigest === evidenceDigest(finding)) {
      skip("blocked");
      continue;
    }
    if (record?.status === "provider_policy_blocked") {
      // Held until an operator requeues it (continuity.ts --requeue-policy-blocked); new evidence does not release it.
      skip("provider-policy-blocked");
      continue;
    }
    if (record?.candidate) {
      // An interrupted run's unverified commit awaits an operator's decision (continuity.ts --release-candidate).
      skip("candidate");
      continue;
    }
    if (record?.status === "in_progress" && record.claimedAt && now - Date.parse(record.claimedAt) < claimTtl) {
      skip("claimed");
      continue;
    }
    if (record?.status === "unverified" && record.nextEligibleAt && Date.parse(record.nextEligibleAt) > now) {
      skip("backoff");
      continue;
    }
    actionable.push(finding);
  }
  return { actionable: actionable.sort(compareFindings), skipped };
}

function newRecord(finding: Finding, at: string): FindingRecord {
  return {
    fingerprint: finding.fingerprint,
    kind: finding.kind,
    theory: finding.theory,
    rule: finding.rule,
    detail: finding.detail.slice(0, 400),
    status: "open",
    attempts: 0,
    firstSeen: at,
    lastSeen: at,
    evidenceDigest: evidenceDigest(finding),
  };
}

/**
 * Record every observed finding so continuity can count unprocessed work; existing progress is
 * kept. A merged finding that report evidence produced after its merge still shows with changed
 * evidence is reopened; published findings whose PR has not merged are kept, with the reason.
 * `producedAt` gives when the reporting evidence was produced (unknown: undefined; `null` for
 * evidence that cannot postdate a merge: a local scan by a checker binary of unknown build time).
 */
export function recordSeen(state: WorkflowState, findings: readonly Finding[], now: Date, producedAt?: (finding: Finding) => string | null | undefined): WorkflowState {
  const at = now.toISOString();
  const records = { ...state.findings };
  for (const finding of findings) {
    const existing = records[finding.fingerprint];
    records[finding.fingerprint] = existing
      ? observePublished({ ...existing, lastSeen: at, snapshot: finding }, finding, at, producedAt?.(finding))
      : { ...newRecord(finding, at), snapshot: finding };
  }
  return { ...state, findings: records };
}

function observePublished(record: FindingRecord, finding: Finding, at: string, producedAt: string | null | undefined): FindingRecord {
  if (record.status !== "resolved" && record.status !== "merged") return record;
  const link = record.publishedOn;
  const pr = link?.prNumber !== undefined ? `PR #${link.prNumber}` : "its PR";
  const where = link ? ` on ${link.branch}` : "";
  if (record.status === "resolved") {
    return { ...record, keptReason: `${pr}${where} is not merged yet: newer report evidence is not acted on until it merges` };
  }
  const digestNow = evidenceDigest(finding);
  if (producedAt === null) {
    return { ...record, keptReason: `local scan evidence comes from a prebuilt checker of unknown build time, which may predate the merge of ${pr}` };
  }
  const produced = producedAt ? `produced at ${producedAt}` : "of unknown production time";
  if (digestNow === record.evidenceDigest) {
    return { ...record, keptReason: `report evidence ${produced} is unchanged from before ${pr} merged` };
  }
  if (producedAt !== undefined && record.mergedAt !== undefined && Date.parse(producedAt) <= Date.parse(record.mergedAt)) {
    return { ...record, keptReason: `report evidence produced at ${producedAt} predates the merge of ${pr} at ${record.mergedAt}` };
  }
  return reopen(record, `report evidence ${produced} after ${pr} merged${record.mergedAt ? ` at ${record.mergedAt}` : ""} still shows this finding with changed evidence`, at, digestNow);
}

/** Whether a run could pick this finding up now: open, out of backoff, or with an expired claim (never while policy-blocked or carrying a candidate). */
export function isEligible(record: FindingRecord, now: Date, claimTtlMs = 24 * 3_600_000): boolean {
  if (record.candidate) return false;
  if (record.status === "open") return true;
  if (record.status === "unverified") return !record.nextEligibleAt || Date.parse(record.nextEligibleAt) <= now.getTime();
  if (record.status === "in_progress") return !record.claimedAt || now.getTime() - Date.parse(record.claimedAt) >= claimTtlMs;
  return false;
}

/** Fingerprints carried by pending (verified, not yet pushed) integrations. */
function pendingFingerprints(state: WorkflowState): Set<string> {
  return new Set(state.pendingPublications.flatMap((entry) => entry.fingerprints));
}

/** Eligible, or integrated work that no pending publication carries any more (it is reopened). */
function eligibleIn(state: WorkflowState, now: Date, claimTtlMs?: number): (record: FindingRecord) => boolean {
  const pending = pendingFingerprints(state);
  return (record) => isEligible(record, now, claimTtlMs) || (record.status === "integrated" && !pending.has(record.fingerprint));
}

/**
 * Findings recorded in state that are eligible now, as findings a run can triage and plan:
 * work deferred by slice capacity, retries whose backoff expired, abandoned claims, and reopened
 * work. Records written before snapshots existed are rebuilt from their stored fields.
 */
export function eligibleStateFindings(state: WorkflowState, now: Date, claimTtlMs?: number): Finding[] {
  return Object.values(state.findings).filter(eligibleIn(state, now, claimTtlMs)).map((record) => record.snapshot ?? {
    fingerprint: record.fingerprint, kind: record.kind, theory: record.theory, checker: "ocaml", rule: record.rule, detail: record.detail,
    affectedProofs: 1, obligations: 1, soleFamilyProofs: 0, examples: [], evidence: [], sources: ["state"],
  });
}

/** Mark findings in progress for one run; a blocked finding with new evidence restarts its attempts. */
export function claimFindings(state: WorkflowState, findings: readonly Finding[], options: { runKey: string; now: Date }): WorkflowState {
  const at = options.now.toISOString();
  const records = { ...state.findings };
  for (const finding of findings) {
    const existing = records[finding.fingerprint] ?? newRecord(finding, at);
    const digestNow = evidenceDigest(finding);
    const reopened = existing.status === "blocked" && existing.evidenceDigest !== digestNow;
    records[finding.fingerprint] = {
      ...transition(existing, "in_progress", `claimed by run ${options.runKey}${reopened ? " (blocked finding with new evidence)" : ""}`, at),
      attempts: reopened ? 0 : existing.attempts,
      evidenceDigest: digestNow,
      claimedBy: options.runKey,
      claimedAt: at,
      lastSeen: at,
    };
  }
  return { ...state, findings: records };
}

export interface OutcomeOptions {
  readonly runKey: string;
  readonly now: Date;
  readonly maxAttempts?: number;
  readonly backoffHours?: number;
  /** Whether a live push included the verified work; otherwise verified findings stay `integrated`. */
  readonly published?: boolean;
  /** Where the live push went (recorded on resolved findings). */
  readonly publishedOn?: PublicationLink;
}

/**
 * Apply slice outcomes: verified findings resolve once published (else stay integrated); a
 * provider policy rejection holds the finding (`provider_policy_blocked`) and a provider outage
 * reopens it, both without an attempt or backoff; other outcomes back off exponentially, then block.
 */
export function recordOutcomes(
  state: WorkflowState,
  outcomes: ReadonlyArray<{ fingerprint: string; status: SliceOutcome; note: string; provider?: ProviderBlock }>,
  options: OutcomeOptions,
): WorkflowState {
  const maxAttempts = options.maxAttempts ?? 3;
  const backoffMs = (options.backoffHours ?? 6) * 3_600_000;
  const at = options.now.toISOString();
  const records = { ...state.findings };
  for (const outcome of outcomes) {
    const existing = records[outcome.fingerprint];
    if (!existing) continue;
    const { claimedBy: _claimedBy, claimedAt: _claimedAt, nextEligibleAt: _next, providerBlock: _block, ...rest } = existing;
    if (outcome.status === "verified") {
      const published = options.published === true;
      records[outcome.fingerprint] = {
        ...transition(rest, published ? "resolved" : "integrated", outcome.note, at),
        lastOutcome: outcome.note, lastRunKey: options.runKey,
        ...(published && options.publishedOn ? { publishedOn: options.publishedOn } : {}),
      };
      continue;
    }
    if (outcome.status === "provider-policy-blocked" || outcome.status === "provider-unavailable") {
      // Not a proof failure: attempts and backoff are untouched.
      const note = `${outcome.status}: ${outcome.note}`;
      const held = outcome.status === "provider-policy-blocked";
      records[outcome.fingerprint] = {
        ...transition(rest, held ? "provider_policy_blocked" : "open", note, at),
        lastOutcome: note,
        lastRunKey: options.runKey,
        ...(held ? { providerBlock: outcome.provider ?? { runKey: options.runKey, stage: "unknown", error: outcome.note, at } } : {}),
      };
      continue;
    }
    const attempts = existing.attempts + 1;
    const blocked = attempts >= maxAttempts;
    const note = `${outcome.status}: ${outcome.note}`;
    records[outcome.fingerprint] = {
      ...transition(rest, blocked ? "blocked" : "unverified", blocked ? `${note} (attempt limit ${maxAttempts} reached)` : note, at),
      attempts,
      lastOutcome: note,
      lastRunKey: options.runKey,
      ...(blocked ? {} : { nextEligibleAt: new Date(options.now.getTime() + backoffMs * 2 ** (attempts - 1)).toISOString() }),
    };
  }
  return { ...state, findings: records };
}

/**
 * Release held provider-policy-blocked findings (`"all"` or the given fingerprints) back to
 * `open` once the provider restriction is resolved. Attempts are unchanged; the transition keeps
 * the provider block it releases. Fingerprints that are not held are reported in `notHeld`.
 */
export function requeuePolicyBlocked(state: WorkflowState, selector: "all" | readonly string[], now: Date): { state: WorkflowState; requeued: string[]; notHeld: string[] } {
  const at = now.toISOString();
  const wanted = selector === "all" ? undefined : new Set(selector);
  const records = { ...state.findings };
  const requeued: string[] = [];
  for (const record of Object.values(state.findings)) {
    if (record.status !== "provider_policy_blocked" || (wanted && !wanted.has(record.fingerprint))) continue;
    const { providerBlock, ...rest } = record;
    const reason = "requeued by an operator after the provider policy restriction was resolved";
    records[record.fingerprint] = { ...transition(rest, "open", reason, at, providerBlock ? { providerBlock } : {}), lastOutcome: `requeued: ${reason}` };
    requeued.push(record.fingerprint);
  }
  const notHeld = wanted ? [...wanted].filter((fingerprint) => !requeued.includes(fingerprint)) : [];
  return { state: { ...state, findings: records }, requeued, notHeld };
}

/** A finding whose slice (or integration) had an agent stage rejected for provider policy, with that evidence. */
export interface PolicyHold {
  readonly fingerprint: string;
  readonly block: ProviderBlock;
}

/**
 * Reconcile outcomes that a workflow version without provider classification recorded for
 * policy-blocked stages: a finding that run `block.runKey` recorded as a failure (`unverified` or
 * `blocked`, one attempt and its backoff) or left claimed is held as `provider_policy_blocked`,
 * with that attempt and backoff undone. Findings that run verified, that a later run touched, or
 * that are already held are left as they are and listed in `unchanged`. Applying it twice is a no-op.
 */
export function holdPolicyBlocked(state: WorkflowState, holds: readonly PolicyHold[], now: Date): { state: WorkflowState; held: string[]; unchanged: Array<{ fingerprint: string; reason: string }> } {
  const at = now.toISOString();
  const records = { ...state.findings };
  const held: string[] = [];
  const unchanged: Array<{ fingerprint: string; reason: string }> = [];
  for (const { fingerprint, block } of holds) {
    const record = records[fingerprint];
    if (!record) {
      unchanged.push({ fingerprint, reason: "not recorded in state" });
      continue;
    }
    if (record.status === "provider_policy_blocked") {
      unchanged.push({ fingerprint, reason: "already held" });
      continue;
    }
    const recordedFailure = record.lastRunKey === block.runKey && (record.status === "unverified" || record.status === "blocked");
    const leftClaimed = record.status === "in_progress" && record.claimedBy === block.runKey;
    if (!recordedFailure && !leftClaimed) {
      unchanged.push({ fingerprint, reason: `status ${record.status} (last run ${record.lastRunKey ?? "none"}) is not a failure or claim of run ${block.runKey}` });
      continue;
    }
    const { claimedBy: _by, claimedAt: _claimed, nextEligibleAt: _next, ...rest } = record;
    const attempts = recordedFailure ? Math.max(0, record.attempts - 1) : record.attempts;
    const undone = recordedFailure ? `; its ${record.status} outcome is undone (attempts ${record.attempts} → ${attempts}, backoff cleared)` : "; its claim is released";
    const reason = `provider-policy-blocked: ${block.stage} of run ${block.runKey} was rejected by the provider (${block.code ?? "policy"}, session ${block.sessionId ?? "unknown"}); reconciled from durable stage evidence${undone}`;
    records[fingerprint] = { ...transition(rest, "provider_policy_blocked", reason, at), attempts, lastOutcome: reason, providerBlock: block };
    held.push(fingerprint);
  }
  return { state: { ...state, findings: records }, held, unchanged };
}

/**
 * Release the claims of a run that ended without recording their outcomes (it crashed or was
 * stopped): every finding still `in_progress` under `runKey` goes back to `open` with its claim
 * cleared, no backoff and its attempts unchanged (a claim is not an attempt). A finding listed in
 * `candidates` (its slice branch carries that run's commit) records the candidate, which keeps it
 * out of automatic work until `releaseCandidates`. Findings the run did not leave claimed are
 * untouched, so applying it twice is a no-op.
 */
export function releaseInterruptedClaims(
  state: WorkflowState,
  options: { runKey: string; candidates: Readonly<Record<string, CandidateWork>>; now: Date },
): { state: WorkflowState; released: string[]; candidates: Array<{ fingerprint: string; candidate: CandidateWork }> } {
  const at = options.now.toISOString();
  const records = { ...state.findings };
  const released: string[] = [];
  const kept: Array<{ fingerprint: string; candidate: CandidateWork }> = [];
  for (const record of Object.values(state.findings)) {
    if (record.status !== "in_progress" || record.claimedBy !== options.runKey) continue;
    const { claimedBy: _by, claimedAt: _claimed, nextEligibleAt: _next, ...rest } = record;
    const candidate = options.candidates[record.fingerprint];
    const reason = `run ${options.runKey} ended before recording an outcome; its claim is released${candidate
      ? `, and its unverified commit ${candidate.commit} on ${candidate.branch} is kept as a candidate: no automatic repair until an operator releases it`
      : ""}`;
    records[record.fingerprint] = { ...transition(rest, "open", reason, at), lastOutcome: `released: ${reason}`, ...(candidate ? { candidate } : {}) };
    if (candidate) kept.push({ fingerprint: record.fingerprint, candidate });
    else released.push(record.fingerprint);
  }
  return { state: { ...state, findings: records }, released, candidates: kept };
}

/**
 * Clear the candidate of findings (`"all"` or the given fingerprints) once an operator has decided
 * on its commit, recording the decision; the findings are then eligible for automatic repair. The
 * transition keeps the candidate. Fingerprints without a candidate are reported in `notCandidates`.
 */
export function releaseCandidates(state: WorkflowState, selector: "all" | readonly string[], decision: string, now: Date): { state: WorkflowState; released: string[]; notCandidates: string[] } {
  const at = now.toISOString();
  const wanted = selector === "all" ? undefined : new Set(selector);
  const records = { ...state.findings };
  const released: string[] = [];
  for (const record of Object.values(state.findings)) {
    if (!record.candidate || (wanted && !wanted.has(record.fingerprint))) continue;
    const { candidate, ...rest } = record;
    const reason = `candidate ${candidate.commit} on ${candidate.branch} (run ${candidate.runKey}) released by an operator: ${decision}`;
    records[record.fingerprint] = { ...transition(rest, rest.status, reason, at, { candidate }), lastOutcome: reason };
    released.push(record.fingerprint);
  }
  const notCandidates = wanted ? [...wanted].filter((fingerprint) => !released.includes(fingerprint)) : [];
  return { state: { ...state, findings: records }, released, notCandidates };
}

export interface PublicationSettlement {
  readonly runKey: string;
  /** A live push of the integration (including `included`) succeeded. */
  readonly published: boolean;
  /** Where that push went. */
  readonly publishedOn?: PublicationLink;
  /** Run keys of pending entries merged into this run's integration. */
  readonly included: readonly string[];
  /** Pending entries this run could not include, with the reason. */
  readonly failed: ReadonlyArray<{ runKey: string; reason: string }>;
  /** This run's verified integration when it was not pushed. */
  readonly added?: PendingPublication;
  readonly now?: Date;
}

/**
 * Update the pending-publication list. Included entries resolve and leave the list only after a
 * successful live push; entries that could not be included keep their reason; unpushed verified
 * work is appended. A run's later iteration merges its own pending entry into its new head and
 * records exactly that head's contents, so the run's entry is replaced (which also makes a
 * resumed step idempotent).
 */
export function settlePublications(state: WorkflowState, settlement: PublicationSettlement): WorkflowState {
  const at = (settlement.now ?? new Date()).toISOString();
  const published = new Set(settlement.published ? settlement.included : []);
  const failed = new Map(settlement.failed.map((item) => [item.runKey, item.reason]));
  const records = { ...state.findings };
  const pending: PendingPublication[] = [];
  const added = settlement.added;
  for (const entry of state.pendingPublications) {
    if (added && entry.runKey === added.runKey) continue;
    if (!published.has(entry.runKey)) {
      const reason = failed.get(entry.runKey);
      pending.push(reason === undefined ? entry : { ...entry, lastError: reason });
      continue;
    }
    for (const fingerprint of entry.fingerprints) {
      const record = records[fingerprint];
      if (record?.status === "integrated") {
        const note = `published by ${settlement.runKey} (integrated in ${entry.runKey})`;
        records[fingerprint] = {
          ...transition(record, "resolved", note, at), lastOutcome: note, lastRunKey: settlement.runKey,
          ...(settlement.publishedOn ? { publishedOn: settlement.publishedOn } : {}),
        };
      }
    }
  }
  if (added) pending.push(added);
  return { ...state, findings: records, pendingPublications: pending };
}

/** Findings that a new run could pick up now (optionally of one kind), including reopened integrated work. */
export function countUnprocessed(state: WorkflowState, now: Date, kind?: FindingKind, claimTtlMs = 24 * 3_600_000): number {
  return Object.values(state.findings).filter((record) => (!kind || record.kind === kind) && eligibleIn(state, now, claimTtlMs)(record)).length;
}

/** What the remote reports about one branch that carries published findings. */
export interface BranchObservation {
  readonly branchExists: boolean;
  readonly prs: ReadonlyArray<{ readonly number: number; readonly state: string; readonly mergedAt?: string }>;
}

export interface Reconciliation {
  readonly state: WorkflowState;
  readonly merged: string[];
  readonly reopened: string[];
  readonly kept: string[];
}

/**
 * Apply what the remote says about the branches carrying resolved (published, unmerged)
 * findings, and reopen integrated findings that no pending publication carries any more:
 * - the finding's PR merged: `merged`, with the PR's merge time (deleting the branch afterwards is not a loss);
 * - the branch is gone and the PR never merged (closed and deleted, or deleted early): reopened,
 *   keeping the lost branch, PR and head in the transition;
 * - otherwise kept as `resolved`, with the reason (PR open, or closed while the branch still exists).
 * Branches without an observation are left alone. Applying the same observations again changes nothing.
 */
export function reconcilePublications(state: WorkflowState, observed: Readonly<Record<string, BranchObservation>>, now: Date): Reconciliation {
  const at = now.toISOString();
  const pending = pendingFingerprints(state);
  const records = { ...state.findings };
  const merged: string[] = [];
  const reopened: string[] = [];
  const kept: string[] = [];
  for (const record of Object.values(state.findings)) {
    const fingerprint = record.fingerprint;
    if (record.status === "integrated" && !pending.has(fingerprint)) {
      records[fingerprint] = reopen(record, "verified integration has no pending publication any more (its pendingPublications entry was removed), so its change would never be published", at);
      reopened.push(fingerprint);
      continue;
    }
    const link = record.publishedOn;
    const branch = link ? observed[link.branch] : undefined;
    if (record.status !== "resolved" || !link || !branch) continue;
    const label = link.prNumber !== undefined ? `PR #${link.prNumber}` : "its PR";
    const own = link.prNumber !== undefined ? branch.prs.find((pr) => pr.number === link.prNumber) : undefined;
    const mergedPr = branch.prs.find((pr) => pr.state === "MERGED" && (link.prNumber === undefined || pr.number === link.prNumber));
    if (mergedPr) {
      const { keptReason: _kept, ...rest } = record;
      records[fingerprint] = { ...transition(rest, "merged", `PR #${mergedPr.number} on ${link.branch} merged`, at), mergedAt: mergedPr.mergedAt ?? at };
      merged.push(fingerprint);
    } else if (!branch.branchExists) {
      const prState = own ? `${label} is ${own.state}` : "no PR was found for it";
      records[fingerprint] = reopen(record, `publication lost: branch ${link.branch} was deleted before ${label} merged (${prState})`, at);
      reopened.push(fingerprint);
    } else {
      const keptReason = own?.state === "OPEN"
        ? `${label} is open on ${link.branch}: awaiting merge`
        : own?.state === "CLOSED"
          ? `${label} was closed without merging but ${link.branch} still exists: reopen the PR, or delete the branch to have this finding reopened`
          : `${link.branch} still exists and ${label} has not merged`;
      if (record.keptReason !== keptReason) records[fingerprint] = { ...record, keptReason };
      kept.push(fingerprint);
    }
  }
  return { state: { ...state, findings: records }, merged, reopened, kept };
}

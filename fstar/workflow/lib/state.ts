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

/** `integrated`: verified and merged into a local integration branch, but not yet published remotely. */
export type FindingStatus = "open" | "in_progress" | "integrated" | "resolved" | "unverified" | "blocked";
export type SliceOutcome = "verified" | "unverified" | "rejected" | "no-change" | "integration-conflict";

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
  /** Rotating scan position per local corpus and checker. */
  localScans: Record<string, { at: string; offset: number }>;
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
        if (Date.now() >= deadline) throw error;
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
      throw new Error(`State is locked by ${holder?.owner ?? "an unknown owner"} (pid ${holder?.pid ?? "?"}) at ${path}`);
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
    if (record?.status === "resolved" || record?.status === "integrated") {
      // Integrated findings await publication of their verified integration, not another repair.
      skip(record.status);
      continue;
    }
    if (record?.status === "blocked" && record.evidenceDigest === evidenceDigest(finding)) {
      skip("blocked");
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

/** Record every observed finding so continuity can count unprocessed work; existing progress is kept. */
export function recordSeen(state: WorkflowState, findings: readonly Finding[], now: Date): WorkflowState {
  const at = now.toISOString();
  const records = { ...state.findings };
  for (const finding of findings) {
    const existing = records[finding.fingerprint];
    records[finding.fingerprint] = existing ? { ...existing, lastSeen: at } : newRecord(finding, at);
  }
  return { ...state, findings: records };
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
      ...existing,
      status: "in_progress",
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
}

/** Apply slice outcomes: verified findings resolve once published (else stay integrated); others back off exponentially, then block. */
export function recordOutcomes(
  state: WorkflowState,
  outcomes: ReadonlyArray<{ fingerprint: string; status: SliceOutcome; note: string }>,
  options: OutcomeOptions,
): WorkflowState {
  const maxAttempts = options.maxAttempts ?? 3;
  const backoffMs = (options.backoffHours ?? 6) * 3_600_000;
  const records = { ...state.findings };
  for (const outcome of outcomes) {
    const existing = records[outcome.fingerprint];
    if (!existing) continue;
    const { claimedBy: _claimedBy, claimedAt: _claimedAt, nextEligibleAt: _next, ...rest } = existing;
    if (outcome.status === "verified") {
      records[outcome.fingerprint] = { ...rest, status: options.published ? "resolved" : "integrated", lastOutcome: outcome.note, lastRunKey: options.runKey };
      continue;
    }
    const attempts = existing.attempts + 1;
    const blocked = attempts >= maxAttempts;
    records[outcome.fingerprint] = {
      ...rest,
      attempts,
      status: blocked ? "blocked" : "unverified",
      lastOutcome: `${outcome.status}: ${outcome.note}`,
      lastRunKey: options.runKey,
      ...(blocked ? {} : { nextEligibleAt: new Date(options.now.getTime() + backoffMs * 2 ** (attempts - 1)).toISOString() }),
    };
  }
  return { ...state, findings: records };
}

export interface PublicationSettlement {
  readonly runKey: string;
  /** A live push of the integration (including `included`) succeeded. */
  readonly published: boolean;
  /** Run keys of pending entries merged into this run's integration. */
  readonly included: readonly string[];
  /** Pending entries this run could not include, with the reason. */
  readonly failed: ReadonlyArray<{ runKey: string; reason: string }>;
  /** This run's verified integration when it was not pushed. */
  readonly added?: PendingPublication;
}

const union = (left: readonly string[], right: readonly string[]) => [...new Set([...left, ...right])];

/**
 * Update the pending-publication list. Included entries resolve and leave the list only after a
 * successful live push; entries that could not be included keep their reason; unpushed verified
 * work is appended. Later iterations of one run share its integration branch, so an entry from
 * the same run is replaced by the newer head with the union of their findings (also making a
 * resumed step idempotent).
 */
export function settlePublications(state: WorkflowState, settlement: PublicationSettlement): WorkflowState {
  const published = new Set(settlement.published ? settlement.included : []);
  const failed = new Map(settlement.failed.map((item) => [item.runKey, item.reason]));
  const records = { ...state.findings };
  const pending: PendingPublication[] = [];
  let added = settlement.added;
  for (const entry of state.pendingPublications) {
    if (added && entry.runKey === added.runKey) {
      added = { ...added, fingerprints: union(entry.fingerprints, added.fingerprints), slices: union(entry.slices, added.slices), recordedAt: entry.recordedAt };
      continue;
    }
    if (!published.has(entry.runKey)) {
      const reason = failed.get(entry.runKey);
      pending.push(reason === undefined ? entry : { ...entry, lastError: reason });
      continue;
    }
    for (const fingerprint of entry.fingerprints) {
      const record = records[fingerprint];
      if (record?.status === "integrated") {
        records[fingerprint] = { ...record, status: "resolved", lastOutcome: `published by ${settlement.runKey} (integrated in ${entry.runKey})`, lastRunKey: settlement.runKey };
      }
    }
  }
  if (added) pending.push(added);
  return { ...state, findings: records, pendingPublications: pending };
}

/** Findings that a new run could pick up now (optionally of one kind). */
export function countUnprocessed(state: WorkflowState, now: Date, kind?: FindingKind, claimTtlMs = 24 * 3_600_000): number {
  return Object.values(state.findings).filter((record) => {
    if (kind && record.kind !== kind) return false;
    if (record.status === "open") return true;
    if (record.status === "unverified") return !record.nextEligibleAt || Date.parse(record.nextEligibleAt) <= now.getTime();
    if (record.status === "in_progress") return !record.claimedAt || now.getTime() - Date.parse(record.claimedAt) >= claimTtlMs;
    return false;
  }).length;
}

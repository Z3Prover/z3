/**
 * Read access to Atomic stage sessions (and, for reconciliation, a run's journal) through
 * Atomic's documented SDK: `resolveSessionStore` + `SessionManager.open(store, sessionId)` and
 * `openSqlRunJournal(...).read(runId)`. These need Atomic's runtime (Node, `node:sqlite`): the
 * workflow runs there, and the launcher reaches them through `lib/node-evidence.ts`. Atomic's loader
 * (or lib/node-hooks.ts) supplies `@bastani/atomic` and `@bastani/atomic/workflows`.
 */

type SessionStoreLike = { close(): Promise<void> };
type AtomicSdk = {
  resolveSessionStore(cwd: string, options?: { sessionStore?: unknown }): Promise<SessionStoreLike>;
  SessionManager: { open(store: SessionStoreLike, sessionId: string): Promise<{ getEntries(): unknown[] }> };
  wrapNodeSqliteDatabase(connection: unknown): unknown;
};
type JournalEntry = { readonly event: { readonly type: string; readonly payload?: Record<string, unknown> } };
/** Atomic's `LeaseState`: `ageMs` is the time since the last renewal on the journal (database) clock. */
export type RunLease = { readonly holderId: string; readonly renewedAt: number; readonly ageMs: number };
type RunJournalLike = {
  getRun(runId: string): Promise<{ readonly status: string } | undefined>;
  leaseState(runId: string): Promise<RunLease | undefined>;
  read(runId: string): AsyncIterable<JournalEntry>;
  close(): Promise<void>;
};

/**
 * How long a run's lease may go unrenewed before Atomic stops treating its executor as alive:
 * "after a process crashes and its lease expires (about two minutes without renewal), inspection
 * reports `crashed`" (Atomic docs/workflows/operations.md). Atomic 0.9.39 exports neither this
 * window (`FOREIGN_LIVE_WORKFLOW_WINDOW_MS`, 120000) nor its ownership probe, which treats a lease
 * as expired when `ageMs` exceeds it.
 */
export const LEASE_EXPIRY_MS = 120_000;

/**
 * The run status Atomic's inspection reports: a `running` run whose lease is unheld, or older than
 * `LEASE_EXPIRY_MS` on the journal clock, has `crashed`; any other status is the journal's.
 */
export function inspectedRunStatus(status: string, lease: RunLease | undefined): string {
  return status === "running" && (lease === undefined || lease.ageMs > LEASE_EXPIRY_MS) ? "crashed" : status;
}

/** The messages of a session's entries, in order. */
function messagesOf(entries: readonly unknown[]): unknown[] {
  return entries.flatMap((entry) => {
    const item = entry as { type?: unknown; message?: unknown } | undefined;
    return item?.type === "message" && item.message ? [item.message] : [];
  });
}

async function readSessions(atomic: AtomicSdk, store: SessionStoreLike, sessionIds: readonly string[]): Promise<Record<string, readonly unknown[]>> {
  const sessions: Record<string, readonly unknown[]> = {};
  for (const sessionId of new Set(sessionIds)) {
    try {
      sessions[sessionId] = messagesOf((await atomic.SessionManager.open(store, sessionId)).getEntries());
    } catch {
      // Not in this store: the caller reports the session as not found.
    }
  }
  return sessions;
}

/** Messages of stage sessions, by id, from the session store Atomic is configured to use (the one stages write). */
export async function readStageSessionMessages(cwd: string, sessionIds: readonly string[]): Promise<Record<string, readonly unknown[]>> {
  const atomic = (await import("@bastani/atomic")) as unknown as AtomicSdk;
  const store = await atomic.resolveSessionStore(cwd);
  try {
    return await readSessions(atomic, store, sessionIds);
  } finally {
    await store.close();
  }
}

export type RunStageSessions = {
  readonly runId: string;
  /** Atomic's inspection status (`inspectedRunStatus`): `running` only while the run's lease is live, `crashed` after it expired. */
  readonly status: string;
  /** The status the journal records (still `running` after its executor stopped). */
  readonly journalStatus: string;
  /** The run's lease, read from the journal (absent when unheld). */
  readonly lease?: RunLease;
  /** The workflow's run key and evidence directory, from the run's `preflight` checkpoint. */
  readonly runKey?: string;
  readonly runDir?: string;
  /** Each agent stage and the session its task result recorded (else its last session checkpoint). */
  readonly stages: Array<{ readonly stage: string; readonly sessionId?: string }>;
  readonly sessions: Record<string, readonly unknown[]>;
};

/**
 * A finished (or still running) run's agent stages and their session messages, read from a SQLite
 * file that holds both the journal and the sessions (Atomic's default
 * `~/.atomic/workflows/journal.sqlite`). The file is opened read-only: nothing is written, and the
 * run's lease is only inspected, never claimed or taken over.
 */
export async function readRunStageSessions(runId: string, databasePath: string): Promise<RunStageSessions> {
  const { DatabaseSync } = (await import("node:sqlite")) as unknown as { DatabaseSync: new (path: string, options: { readOnly: boolean }) => { close(): void } };
  const atomic = (await import("@bastani/atomic")) as unknown as AtomicSdk;
  const workflows = (await import("@bastani/atomic/workflows")) as unknown as { openSqlRunJournal(database: unknown): Promise<RunJournalLike> };
  const connection = new DatabaseSync(databasePath, { readOnly: true });
  try {
    const journal = await workflows.openSqlRunJournal(connection);
    let summary: { readonly status: string } | undefined;
    let lease: RunLease | undefined;
    let setup: { runKey?: string; runDir?: string } = {};
    const fromTask = new Map<string, string | undefined>();
    const fromSession = new Map<string, string>();
    try {
      summary = await journal.getRun(runId);
      if (!summary) throw new Error(`run ${runId} is not in the journal ${databasePath}`);
      const state = await journal.leaseState(runId);
      if (state) lease = { holderId: state.holderId, renewedAt: state.renewedAt, ageMs: state.ageMs };
      for await (const entry of journal.read(runId)) {
        const payload = entry.event.payload;
        if (entry.event.type !== "CheckpointRecorded" || !payload) continue;
        const name = typeof payload.name === "string" ? payload.name : undefined;
        const checkpoint = typeof payload.checkpointId === "string" ? payload.checkpointId : "";
        if (payload.kind === "tool" && name === "preflight") setup = (payload.output ?? {}) as typeof setup;
        if (payload.kind !== "stage" || !name) continue;
        const output = payload.output as { sessionId?: unknown } | undefined;
        if (checkpoint.startsWith("task:")) fromTask.set(name, typeof output?.sessionId === "string" ? output.sessionId : undefined);
        else if (typeof payload.sessionId === "string") fromSession.set(name, payload.sessionId);
      }
    } finally {
      await journal.close();
    }
    const names = [...new Set([...fromSession.keys(), ...fromTask.keys()])];
    const stages = names.map((stage) => {
      const sessionId = fromTask.get(stage) ?? fromSession.get(stage);
      return sessionId ? { stage, sessionId } : { stage };
    });
    const store = await atomic.resolveSessionStore(process.cwd(), { sessionStore: { kind: "database", database: atomic.wrapNodeSqliteDatabase(connection) } });
    let sessions: Record<string, readonly unknown[]>;
    try {
      sessions = await readSessions(atomic, store, stages.flatMap((stage) => (stage.sessionId ? [stage.sessionId] : [])));
    } finally {
      await store.close();
    }
    return {
      runId, status: inspectedRunStatus(summary.status, lease), journalStatus: summary.status, ...(lease ? { lease } : {}),
      ...(setup.runKey ? { runKey: setup.runKey } : {}), ...(setup.runDir ? { runDir: setup.runDir } : {}), stages, sessions,
    };
  } finally {
    connection.close();
  }
}

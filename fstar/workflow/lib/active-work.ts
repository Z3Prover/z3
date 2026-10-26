/**
 * Local work reservations: `<stateDir>/active-work.json`, written by an operator (or the
 * orchestrator of a focused run) to keep automatic runs from duplicating work that is under way
 * in another local branch and worktree. Operational data, not state: nothing here changes
 * state.json, and nothing expires automatically. A missing or empty file means no reservations;
 * a malformed one is an error the caller must report and stop on, never a silent empty list.
 */
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { THEORIES, type Theory } from "./theories.js";

export type ActiveWork = {
  readonly branch: string;
  readonly worktree: string;
  /** Who holds the reservation, for example an Atomic run id. */
  readonly owner: string;
  /** ISO time the reservation was made. */
  readonly createdAt: string;
  readonly theories?: Theory[];
  /** Findings the reserved work covers: triage skips them. */
  readonly fingerprints?: string[];
  readonly files?: string[];
  readonly note?: string;
};

export type ActiveWorkRead =
  | { readonly ok: true; readonly path: string; readonly entries: ActiveWork[] }
  | { readonly ok: false; readonly path: string; readonly error: string };

export const ACTIVE_WORK_FILE = "active-work.json";

const isStrings = (value: unknown): value is string[] => Array.isArray(value) && value.every((item) => typeof item === "string");

function validate(value: unknown): ActiveWork[] {
  if (!Array.isArray(value)) throw new Error("expected a JSON array of reservations");
  return value.map((item, index) => {
    const where = `entry ${index}`;
    if (typeof item !== "object" || item === null || Array.isArray(item)) throw new Error(`${where} is not an object`);
    const entry = item as Record<string, unknown>;
    for (const key of ["branch", "worktree", "owner", "createdAt"]) {
      if (typeof entry[key] !== "string" || (entry[key] as string).trim() === "") throw new Error(`${where} needs a non-empty string "${key}"`);
    }
    if (Number.isNaN(Date.parse(entry.createdAt as string))) throw new Error(`${where} has an invalid createdAt "${String(entry.createdAt)}"`);
    for (const key of ["theories", "fingerprints", "files"]) {
      if (entry[key] !== undefined && !isStrings(entry[key])) throw new Error(`${where}: "${key}" must be an array of strings`);
    }
    const unknown = ((entry.theories as string[] | undefined) ?? []).filter((theory) => !(THEORIES as readonly string[]).includes(theory));
    if (unknown.length > 0) throw new Error(`${where} names unknown theories ${unknown.join(", ")} (known: ${THEORIES.join(", ")})`);
    if (entry.note !== undefined && typeof entry.note !== "string") throw new Error(`${where}: "note" must be a string`);
    return entry as unknown as ActiveWork;
  });
}

/** Read `<stateDir>/active-work.json`: missing or empty means no reservations; anything malformed or unreadable is an error. */
export function readActiveWork(stateDir: string): ActiveWorkRead {
  const path = join(stateDir, ACTIVE_WORK_FILE);
  if (!existsSync(path)) return { ok: true, path, entries: [] };
  try {
    const text = readFileSync(path, "utf8").replace(/^\uFEFF/, "");
    if (text.trim() === "") return { ok: true, path, entries: [] };
    return { ok: true, path, entries: validate(JSON.parse(text)) };
  } catch (error) {
    return { ok: false, path, error: error instanceof Error ? error.message : String(error) };
  }
}

/** The actionable message for a malformed reservation file. */
export function activeWorkError(read: Extract<ActiveWorkRead, { ok: false }>): string {
  return `active-work.json invalid: ${read.error} (${read.path}); fix or remove it`;
}

/** Reserved fingerprints and the branch that reserves each. */
export function reservedFingerprints(entries: readonly ActiveWork[]): Map<string, string> {
  const reserved = new Map<string, string>();
  for (const entry of entries) for (const fingerprint of entry.fingerprints ?? []) reserved.set(fingerprint, entry.branch);
  return reserved;
}

/**
 * The reservations a slice must not duplicate: those of its theory, and those that name fstar/
 * checker files (a slice may edit any of them).
 */
export function activeWorkFor(entries: readonly ActiveWork[], theory: string): ActiveWork[] {
  return entries.filter((entry) => (entry.theories ?? []).includes(theory as Theory)
    || (entry.files ?? []).some((file) => file.replaceAll("\\", "/").includes("fstar/") && !file.replaceAll("\\", "/").includes("fstar/workflow")));
}

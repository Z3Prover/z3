/**
 * Version coupling: `LEASE_EXPIRY_MS` mirrors Atomic's internal `FOREIGN_LIVE_WORKFLOW_WINDOW_MS`
 * (not public API; Atomic 0.9.39 defines it in dist/builtin/workflows/src/index.js). This test reads
 * the installed package so an Atomic upgrade that changes the window fails here instead of
 * silently changing when the reconcile treats a run as crashed.
 */
import { describe, expect, test } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { atomicPackageDir } from "../lib/atomic-host.ts";
import { LEASE_EXPIRY_MS } from "../lib/stage-sessions.ts";

const ATOMIC_SOURCE = ["dist", "builtin", "workflows", "src", "index.js"];

/** The window Atomic's installed workflow runtime defines, or why it could not be read. */
function atomicWindow(): { value: number } | { missing: string } {
  let path: string;
  try {
    path = join(atomicPackageDir(), ...ATOMIC_SOURCE);
  } catch (error) {
    return { missing: error instanceof Error ? error.message : String(error) };
  }
  if (!existsSync(path)) return { missing: `${path} does not exist` };
  const match = /\bFOREIGN_LIVE_WORKFLOW_WINDOW_MS\s*=\s*([0-9_]+)\s*;/.exec(readFileSync(path, "utf8"));
  return match?.[1] ? { value: Number(match[1].replaceAll("_", "")) } : { missing: `FOREIGN_LIVE_WORKFLOW_WINDOW_MS = <n> not found in ${path}` };
}

const window = atomicWindow();

describe("Atomic version coupling", () => {
  if ("missing" in window) {
    test.skip(`LEASE_EXPIRY_MS check skipped: ${window.missing}; Atomic's internals changed, so re-derive the lease window by hand`, () => {});
    return;
  }
  test("LEASE_EXPIRY_MS equals Atomic's FOREIGN_LIVE_WORKFLOW_WINDOW_MS", () => {
    expect(LEASE_EXPIRY_MS).toBe(window.value);
  });
});

/**
 * The continuity launcher's lock handling. A fresh state directory (a new clone: `.atomic/` is
 * ignored) must not stop the first launch; only a launcher lock held by a live process skips a
 * launch (exit 0); any other failure is reported as failed with a nonzero exit.
 */
import { describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { hostname, tmpdir } from "node:os";
import { join } from "node:path";
import { launchExclusively } from "../lib/continuity.ts";

const launcher = join(import.meta.dir, "..", "continuity.ts");
const buildLog = join(import.meta.dir, "fixtures", "build-run-40280393373-1", "pulse-checker-build-report", "build.log");

/** `--launch --dry-run` on a local build log with proof timeouts, so the decision is to retrigger. */
function launch(stateDir: string) {
  const result = spawnSync(process.execPath, [launcher, "--launch", "--dry-run", "--no-remote", "--state-dir", stateDir, "--build-log", buildLog], { encoding: "utf8" });
  return { code: result.status, output: JSON.parse(result.stdout) as { decision: { retrigger: boolean }; launched: boolean; skipped?: string; failed?: string } };
}

const liveLock = (stateDir: string) => {
  mkdirSync(stateDir, { recursive: true });
  writeFileSync(join(stateDir, "launcher.lock"), JSON.stringify({ owner: "another-launcher", pid: process.pid, host: hostname(), acquiredAt: Date.now() }));
};

describe("continuity launcher lock", () => {
  test("a launch into a state directory that does not exist yet creates it and launches", async () => {
    const stateDir = join(mkdtempSync(join(tmpdir(), "fpc-launch-")), "fresh", ".atomic", "fstar-proof-checking");
    let launched = 0;
    const outcome = await launchExclusively(stateDir, async () => {
      launched += 1;
      return "run-1";
    });
    expect(outcome).toEqual({ kind: "launched", value: "run-1" });
    expect(launched).toBe(1);
    expect(existsSync(stateDir)).toBe(true);
    // The lock is released afterwards, so the next scheduled launch is not skipped.
    expect(existsSync(join(stateDir, "launcher.lock"))).toBe(false);
  });

  test("a launcher lock held by a live process skips the launch", async () => {
    const stateDir = join(mkdtempSync(join(tmpdir(), "fpc-launch-")), "state");
    liveLock(stateDir);
    let launched = 0;
    const outcome = await launchExclusively(stateDir, async () => {
      launched += 1;
    });
    expect(outcome).toMatchObject({ kind: "skipped", reason: expect.stringMatching(/locked by another-launcher/) });
    expect(launched).toBe(0);
  });

  test("the CLI reports lock contention as skipped with exit 0", () => {
    const stateDir = join(mkdtempSync(join(tmpdir(), "fpc-launch-")), "state");
    liveLock(stateDir);
    const { code, output } = launch(stateDir);
    expect(output.decision.retrigger).toBe(true);
    expect(output).toMatchObject({ launched: false, skipped: expect.stringMatching(/locked by another-launcher/) });
    expect(output.failed).toBeUndefined();
    expect(code).toBe(0);
  }, 60_000);

  test("the CLI reports any other lock failure as failed with a nonzero exit", () => {
    // The state directory path is an existing file, so it can be neither created nor locked.
    const stateDir = join(mkdtempSync(join(tmpdir(), "fpc-launch-")), "not-a-directory");
    writeFileSync(stateDir, "");
    const { code, output } = launch(stateDir);
    expect(output.decision.retrigger).toBe(true);
    expect(output.launched).toBe(false);
    expect(output.skipped).toBeUndefined();
    expect(output.failed).toBeString();
    expect(code).not.toBe(0);
  }, 60_000);
});

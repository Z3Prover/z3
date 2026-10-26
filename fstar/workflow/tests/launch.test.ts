/**
 * A launch from the scheduler's runtime (Bun) must reach Atomic's persistent storage. The
 * scheduled `--launch --publish live` ran `run()` inside Bun and failed before its first step
 * with `StorageAdapterLoadError: Could not load storage adapter: node:sqlite`: Atomic's SQLite
 * journal and stage-session store need `node:sqlite`, which Bun 1.3 lacks. Dry runs used an
 * in-memory journal and never opened it. These tests use a real journal file.
 */
import { describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { atomicPackageDir } from "../lib/atomic-host.ts";
import { runWorkflowInNode } from "../lib/launch.ts";

const launcher = join(import.meta.dir, "..", "continuity.ts");
const probeWorkflow = join(import.meta.dir, "fixtures", "launch-probe.ts");
const buildLog = join(import.meta.dir, "fixtures", "build-run-40280393373-1", "pulse-checker-build-report", "build.log");

interface JournalEntry { readonly event: { readonly type: string; readonly payload: { readonly name?: string; readonly output?: unknown } } }

/** Reads a run back from the journal file in a fresh process, through Atomic's own journal API. */
function reopenRun(journalPath: string, runId: string) {
  const workflows = pathToFileURL(createRequire(join(atomicPackageDir(), "package.json")).resolve("@bastani/atomic/workflows")).href;
  const script = [
    `const { openSqlRunJournal } = await import(${JSON.stringify(workflows)});`,
    `const journal = await openSqlRunJournal(${JSON.stringify(journalPath)});`,
    `const run = await journal.getRun(${JSON.stringify(runId)});`,
    "const entries = [];",
    `for await (const entry of journal.read(${JSON.stringify(runId)})) entries.push(entry);`,
    "await journal.close();",
    "console.log(JSON.stringify({ run, entries }));",
  ].join("\n");
  const result = spawnSync("node", ["--input-type=module", "-e", script], { encoding: "utf8" });
  expect(result.stderr).not.toMatch(/Error/);
  return JSON.parse(result.stdout) as { run?: { status: string; storage?: { location: string } }; entries: JournalEntry[] };
}

describe("launching a run with persistent Atomic storage", () => {
  test("the run completes on a SQLite journal file and is read back from it by a fresh process", async () => {
    const directory = mkdtempSync(join(tmpdir(), "fpc-journal-"));
    const journalPath = join(directory, "journal.sqlite");
    const outcome = await runWorkflowInNode({ workflow: probeWorkflow, inputs: { value: 21 }, cwd: directory, journal: { path: journalPath } });
    expect(outcome).toMatchObject({ ok: true, status: "completed", result: { doubled: 42, loaded: "fstar-proof-checking" } });
    if (!outcome.ok) return;

    const { run, entries } = reopenRun(journalPath, outcome.runId);
    expect(run).toMatchObject({ status: "completed", storage: { location: journalPath } });
    const step = entries.find((entry) => entry.event.type === "CheckpointRecorded" && entry.event.payload.name === "double");
    expect(step?.event.payload.output).toBe(42);
  }, 120_000);

  test("a journal that cannot be opened is reported by the launcher as a storage failure with a nonzero exit", () => {
    const directory = mkdtempSync(join(tmpdir(), "fpc-journal-"));
    // The journal's parent directory is a file: the store can be neither created nor opened.
    writeFileSync(join(directory, "not-a-directory"), "");
    const journal = join(directory, "not-a-directory", "journal.sqlite");
    const result = spawnSync(process.execPath, [
      launcher, "--launch", "--dry-run", "--no-remote", "--state-dir", join(directory, "state"), "--build-log", buildLog, "--journal", journal,
    ], { encoding: "utf8" });
    const report = JSON.parse(result.stdout) as { decision: { retrigger: boolean }; launched: boolean; journal: unknown; failed?: string; failure?: { phase: string; error: string } };
    expect(report.decision.retrigger).toBe(true);
    expect(report).toMatchObject({ launched: false, journal: { path: journal }, failure: { phase: "storage" } });
    const error = report.failure?.error ?? "";
    expect(error).toMatch(/^Storage\w*Error$/);
    expect(report.failed).toContain(error);
    // The error's stack stays visible in the log.
    expect(result.stderr).toContain(`${error}: `);
    expect(result.status).toBe(1);
  }, 120_000);
});

/**
 * Runs a workflow in a Node child process, under Atomic's own runtime. An npm-installed Atomic
 * runs on Node, and its persistent storage needs `node:sqlite`: the workflow journal and the
 * stage sessions (both in ~/.atomic/workflows/journal.sqlite by default) and the Intercom
 * extension that stage sessions load. Bun before 1.4.2 has no `node:sqlite`, so the launcher
 * (run by Bun) keeps its checks and lock and hands only the run to `node lib/node-run.ts`.
 */
import { spawn } from "node:child_process";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { atomicPackageDir } from "./atomic-host.js";

export interface WorkflowRunRequest {
  /** Module whose default export is the workflow definition (absolute path). */
  readonly workflow: string;
  readonly inputs: Record<string, unknown>;
  /** Working directory of the run (and of the child process). */
  readonly cwd: string;
  /** Omitted: Atomic's own selection (ATOMIC_WORKFLOW_JOURNAL_PATH, settings, ~/.atomic/workflows/journal.sqlite). */
  readonly journal?: { readonly memory: true } | { readonly path: string };
  /** Installed `@bastani/atomic` package; default `atomicPackageDir()`. */
  readonly packageDir?: string;
}

/**
 * Where a run that produced no status failed: `runtime` (Node could not be started or exited
 * without a result), `load` (Atomic or the workflow module), `storage` (an Atomic storage or
 * journal error, such as a journal that cannot be opened), or `run` (any other error from `run`).
 */
export type StartPhase = "runtime" | "load" | "storage" | "run";

export type WorkflowRunOutcome =
  | { readonly ok: true; readonly runId: string; readonly status: string; readonly error?: string; readonly result?: unknown }
  | { readonly ok: false; readonly phase: StartPhase; readonly error: { readonly name: string; readonly message: string } };

const NODE_RUN = fileURLToPath(new URL("./node-run.ts", import.meta.url));

const failure = (phase: StartPhase, error: unknown): WorkflowRunOutcome => ({
  ok: false, phase, error: { name: error instanceof Error ? error.name : "Error", message: error instanceof Error ? error.message : String(error) },
});

/** Run the workflow under `node` (from PATH by default). The child's output is copied to stderr. */
export async function runWorkflowInNode(request: WorkflowRunRequest, node = "node"): Promise<WorkflowRunOutcome> {
  let packageDir: string;
  try {
    packageDir = request.packageDir ?? atomicPackageDir();
  } catch (error) {
    return failure("load", error);
  }
  const directory = mkdtempSync(join(tmpdir(), "fpc-node-run-"));
  const requestPath = join(directory, "request.json");
  const resultPath = join(directory, "result.json");
  try {
    writeFileSync(requestPath, JSON.stringify({ ...request, packageDir, resultPath }));
    const exit = await new Promise<{ code: number | null; signal: string | null } | Error>((settle) => {
      const child = spawn(node, [NODE_RUN, requestPath], { cwd: request.cwd, stdio: ["ignore", "pipe", "pipe"], windowsHide: true });
      // Keep the launcher's stdout for its JSON report.
      child.stdout?.on("data", (chunk) => process.stderr.write(chunk));
      child.stderr?.on("data", (chunk) => process.stderr.write(chunk));
      child.on("error", settle);
      child.on("close", (code, signal) => settle({ code, signal }));
    });
    if (exit instanceof Error) return failure("runtime", new Error(`could not start ${node}: ${exit.message}`));
    if (existsSync(resultPath)) return JSON.parse(readFileSync(resultPath, "utf8")) as WorkflowRunOutcome;
    return failure("runtime", new Error(`${node} ${NODE_RUN} exited with ${exit.code ?? exit.signal} and no result (Atomic needs Node >= 22.19)`));
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

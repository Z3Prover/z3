/**
 * Node entry point that runs one workflow under Atomic's own runtime (see lib/launch.ts):
 *
 *   node fstar/workflow/lib/node-run.ts <request.json>
 *
 * Node (>= 22.19, the runtime of an npm-installed Atomic) strips the TypeScript types. A resolve
 * hook loads the host modules (`@bastani/atomic/workflows`, `typebox`) from the installed Atomic
 * package, as Atomic's loader does, and maps the workflow's `.js` import specifiers to its `.ts`
 * sources. Only built-in modules are imported statically: the hook must be registered before the
 * workflow loads. The outcome is written to the request's `resultPath` as a `WorkflowRunOutcome`.
 */
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { registerHooks } from "node:module";
import { join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
// Explicit `.ts`: this module is loaded before the hook below maps `.js` specifiers to sources.
import { HOST_SPECIFIERS } from "./atomic-host.ts";
import type { StartPhase, WorkflowRunOutcome, WorkflowRunRequest } from "./launch.ts";

function registerWorkflowHooks(packageDir: string): void {
  const host = new Set<string>(HOST_SPECIFIERS);
  const hostParent = pathToFileURL(join(packageDir, "package.json")).href;
  registerHooks({
    resolve(specifier, context, nextResolve) {
      // Resolved as if imported from inside the installed package: the instances Atomic itself uses.
      if (host.has(specifier)) return nextResolve(specifier, { ...context, parentURL: hostParent });
      if (/^\.\.?\//.test(specifier) && specifier.endsWith(".js") && context.parentURL?.endsWith(".ts")) {
        const source = new URL(`${specifier.slice(0, -".js".length)}.ts`, context.parentURL);
        if (existsSync(fileURLToPath(source))) return { url: source.href, shortCircuit: true };
      }
      return nextResolve(specifier, context);
    },
  });
}

/** Atomic's storage (`StorageError`) and journal (`JournalError`) failures, also when wrapped as a cause. */
function isStorageFailure(error: unknown): boolean {
  for (let current = error, depth = 0; current instanceof Error && depth < 8; current = current.cause, depth += 1) {
    for (let proto = Object.getPrototypeOf(current); proto && proto !== Error.prototype; proto = Object.getPrototypeOf(proto)) {
      const name = (proto as { constructor?: { name?: string } }).constructor?.name;
      if (name === "StorageError" || name === "JournalError") return true;
    }
  }
  return false;
}

async function main(requestPath: string): Promise<number> {
  const request = JSON.parse(readFileSync(requestPath, "utf8")) as WorkflowRunRequest & { packageDir: string; resultPath: string };
  const finish = (outcome: WorkflowRunOutcome) => writeFileSync(request.resultPath, JSON.stringify(outcome));
  let phase: StartPhase = "load";
  try {
    registerWorkflowHooks(request.packageDir);
    const { default: definition } = await import(pathToFileURL(request.workflow).href);
    const sdk = await import("@bastani/atomic/workflows");
    phase = "run";
    const result = await sdk.run(definition, request.inputs as never, {
      cwd: request.cwd,
      executionMode: "non_interactive",
      // Omitted: Atomic's own selection (ATOMIC_WORKFLOW_JOURNAL_PATH, settings, ~/.atomic/workflows/journal.sqlite).
      ...(request.journal ? { journal: request.journal } : {}),
    });
    finish({ ok: true, runId: result.runId, status: result.status, error: result.error, result: result.result });
    return result.status === "completed" ? 0 : 1;
  } catch (error) {
    // The stack stays in the log; the result names the phase and the error class.
    console.error(error instanceof Error ? error.stack ?? error.message : String(error));
    const failure = error instanceof Error ? error : new Error(String(error));
    finish({ ok: false, phase: isStorageFailure(error) ? "storage" : phase, error: { name: failure.name, message: failure.message } });
    return 1;
  }
}

const requestPath = process.argv[2];
if (!requestPath) {
  console.error("usage: node fstar/workflow/lib/node-run.ts <request.json>");
  process.exit(2);
}
main(requestPath).then((code) => process.exit(code));

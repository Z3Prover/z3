/**
 * Node entry point that reads how an earlier run's agent stages ended (see `readRunEvidenceInNode`
 * in lib/launch.ts and `continuity.ts --reconcile-policy-blocked`):
 *
 *   node fstar/workflow/lib/node-evidence.ts <request.json>
 *
 * It opens the SQLite file holding the run journal and the stage sessions read-only, reads the
 * run's agent stages and their sessions through Atomic's SDK (lib/stage-sessions.ts), classifies
 * them (lib/provider.ts) and writes a `RunEvidenceOutcome` to the request's `resultPath`.
 */
import { readFileSync, writeFileSync } from "node:fs";
import type { RunEvidenceOutcome, RunEvidenceRequest } from "./launch.ts";
// Explicit `.ts`: this module is loaded before the hook maps `.js` specifiers to sources.
import { registerWorkflowHooks } from "./node-hooks.ts";

async function main(requestPath: string): Promise<number> {
  const request = JSON.parse(readFileSync(requestPath, "utf8")) as RunEvidenceRequest & { packageDir: string; resultPath: string };
  const finish = (outcome: RunEvidenceOutcome) => writeFileSync(request.resultPath, JSON.stringify(outcome));
  try {
    registerWorkflowHooks(request.packageDir);
    const { readRunStageSessions } = await import("./stage-sessions.ts");
    const { classifyRunStages } = await import("./provider.ts");
    const run = await readRunStageSessions(request.runId, request.database);
    finish({ ok: true, runId: run.runId, status: run.status, ...(run.runKey ? { runKey: run.runKey } : {}), ...(run.runDir ? { runDir: run.runDir } : {}), stages: classifyRunStages(run) });
    return 0;
  } catch (error) {
    console.error(error instanceof Error ? error.stack ?? error.message : String(error));
    const failure = error instanceof Error ? error : new Error(String(error));
    finish({ ok: false, error: { name: failure.name, message: failure.message } });
    return 1;
  }
}

const requestPath = process.argv[2];
if (!requestPath) {
  console.error("usage: node fstar/workflow/lib/node-evidence.ts <request.json>");
  process.exit(2);
}
main(requestPath).then((code) => process.exit(code));

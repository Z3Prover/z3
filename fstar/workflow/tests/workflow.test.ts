import { beforeAll, describe, expect, test } from "bun:test";
import { existsSync, mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { registerAtomicHostModules } from "../lib/atomic-host.ts";

const fixtures = join(import.meta.dir, "fixtures");
const repoRoot = join(import.meta.dir, "..", "..", "..");
const reportPaths = [join(fixtures, "pulse-run-40244844124-1"), join(fixtures, "build-run-40280393373-1")];

// The workflow module imports Atomic's host-provided SDK; load the installed package's modules.
let definition: any;
let sdk: any;
let steps: typeof import("../lib/steps.ts");
beforeAll(async () => {
  await registerAtomicHostModules();
  definition = (await import("../fstar-proof-checking.ts")).default;
  sdk = await import("@bastani/atomic/workflows");
  steps = await import("../lib/steps.ts");
}, 120_000);

describe("dry run through Atomic's workflow runtime", () => {
  test("terminates with unique, acyclic durable nodes per iteration and no remote commands", async () => {
    const stateDir = mkdtempSync(join(tmpdir(), "fpc-dry-"));
    const store = sdk.createStore();
    const result = await sdk.run(definition, {
      dryRun: true, publish: "dry-run", stateDir, maxIterations: 2, coresPerSlice: 16, reportPaths, localCorpora: [],
    }, { journal: { memory: true }, cwd: repoRoot, executionMode: "non_interactive", store });
    expect(result.status).toBe("completed");
    expect(result.result).toMatchObject({ status: "completed", iterations: 2, verified_slices: 0 });
    const run = store.snapshot().runs[0];
    const names: string[] = run.toolNodes.map((node: { name: string }) => node.name);
    expect(names).toEqual([
      "preflight", "source",
      "iter-1/triage", "iter-1/plan", "iter-1/gate", "iter-1/integrate", "iter-1/publish", "iter-1/persist",
      "iter-2/triage", "iter-2/plan", "iter-2/gate", "iter-2/integrate", "iter-2/publish", "iter-2/persist",
      "investigate/select", "finalize",
    ]);
    expect(new Set(names).size).toBe(names.length);
    // Every edge points to an earlier node: no self-edges or back-edges.
    const order = new Map<string, number>(run.toolNodes.map((node: { id: string; executionOrder: number }) => [node.id, node.executionOrder]));
    for (const node of run.toolNodes) {
      for (const parent of node.parentIds) expect(order.get(parent)).toBeLessThan(node.executionOrder);
    }
    expect(result.stages).toEqual([]);
    const evidence = JSON.parse(readFileSync(result.result.evidence_path, "utf8"));
    expect(evidence.mutatingCommands).toEqual([]);
    const commands = readFileSync(join(result.result.run_dir, "commands.jsonl"), "utf8");
    expect(commands).not.toMatch(/"gh"|"push"/);
    expect(existsSync(join(stateDir, "state.json"))).toBe(false);
    const plan = JSON.parse(readFileSync(join(result.result.run_dir, "iter-1", "plan.json"), "utf8"));
    expect(plan.totalCores).toBeLessThanOrEqual(32);
    expect(plan.worktreesCreated).toBe(false);
  }, 120_000);
});

type Override = (name: string, args: any, real: () => Promise<any>) => unknown;

/** A fake run context: records stage calls and lets tests script selected durable steps. */
function fakeContext(inputs: Record<string, unknown>, overrides: Record<string, Override>) {
  const tasks: Array<{ name: string; options: any }> = [];
  const tools: string[] = [];
  const ctx = {
    inputs,
    cwd: repoRoot,
    tool: async (name: string, args: unknown, fn: (tool: { signal: AbortSignal }) => Promise<unknown>) => {
      tools.push(name);
      const real = () => fn({ signal: new AbortController().signal }) as Promise<any>;
      const override = Object.entries(overrides).find(([pattern]) => new RegExp(`^${pattern}$`).test(name));
      if (override) return override[1](name, args, real);
      if (!["iter-[0-9]+/triage", "investigate/select", "finalize"].some((pattern) => new RegExp(`^${pattern}$`).test(name))) {
        throw new Error(`unscripted durable step ${name} would touch git, GitHub or state`);
      }
      return real();
    },
    task: async (name: string, options: any) => {
      tasks.push({ name, options });
      // Only iteration 1 verifies, so iterations 2 and 3 make no progress.
      const verified = name.startsWith("iter-1/");
      return {
        stageName: name,
        text: "done",
        structured: options.schema ? { verdict: verified ? "verified" : "unverified", toolchainAvailable: true, commands: [{ command: "build", exitCode: 0, phase: "final" }], resolvedFingerprints: [], soundnessConcerns: [], summary: "fake" } : undefined,
      };
    },
    chain: async () => [],
    parallel: async () => [],
    exit: (options: unknown) => { throw Object.assign(new Error("exit"), { options }); },
  };
  return { ctx, tasks, tools };
}

describe("full iteration topology with scripted durable steps", () => {
  async function runScripted(available: boolean) {
    const stateDir = mkdtempSync(join(tmpdir(), "fpc-topology-"));
    const defaults = Object.fromEntries(Object.entries(definition.inputs).map(([key, schema]: [string, any]) => [key, schema.default]));
    const inputs = { ...defaults, stateDir, reportPaths, localCorpora: [], maxIterations: 3, coresPerSlice: 8 };
    // Steps that would touch GitHub, the toolchain, or git worktrees run in their local/dry form.
    const local = { ...inputs, dryRun: true } as any;
    const signal = new AbortController().signal;
    let setup: any;
    let actionablePath = "";
    const overrides: Record<string, Override> = {
      preflight: async (_name, _args, real) => {
        const probed = await real();
        setup = { ...probed, toolchain: { ...probed.toolchain, available, missing: available ? [] : ["F* v2026.09.27"] } };
        return setup;
      },
      source: async () => steps.sourceFindings(setup, local, signal),
      "iter-[0-9]+/triage": async (_name, _args, real) => {
        const triage = await real();
        actionablePath = triage.actionablePath;
        return triage;
      },
      "iter-[0-9]+/plan": async (name) => steps.planStep(setup, local, actionablePath, Number(/iter-([0-9]+)/.exec(name)?.[1]), signal),
      "iter-[0-9]+/gate": async (_name, args) => ({
        verified: args.verdicts.filter((verdict: any) => verdict?.verdict === "verified").length,
        slices: args.verdicts.map((verdict: any, index: number) => ({ id: `s${index}`, status: verdict?.verdict === "verified" ? "verified" : "unverified", reasons: [], changedFiles: 1, warnings: [] })),
      }),
      "iter-[0-9]+/integrate": async (_name, args) => (args.verified > 0
        ? { worktree: "W", branch: "B", base: "origin/master", merged: ["s0"], conflicts: [], rejected: [], head: "abc", note: "" }
        : { base: "origin/master", merged: [], conflicts: [], rejected: [], note: "" }),
      "iter-[0-9]+/publish": async () => ({ mode: "dry-run", action: "new-branch", executed: false, summary: "dry-run: would new-branch", integrationVerified: true, bugReports: [], publication: { sequence: 0, history: [] } }),
      "iter-[0-9]+/persist": async () => ({ committed: true, outcomes: [], processedReports: [] }),
    };
    const fake = fakeContext(inputs, overrides);
    const output = await definition.run(fake.ctx);
    return { output, ...fake };
  }

  test("stages are fresh per iteration, slices run in their own worktrees, and the loop stops on no progress", async () => {
    const { output, tasks, tools } = await runScripted(true);
    expect(output.status).toBe("completed");
    expect(output.stop_reason).toMatch(/no progress/);
    expect(output.iterations).toBe(3);
    const names = tasks.map((task) => task.name);
    expect(new Set(names).size).toBe(names.length);
    expect(new Set(tools).size).toBe(tools.length);
    const worktrees = new Set<string>();
    for (const iteration of [1, 2, 3]) {
      const repairs = tasks.filter((task) => task.name.startsWith(`iter-${iteration}/`) && task.name.endsWith("/repair"));
      const verifies = tasks.filter((task) => task.name.startsWith(`iter-${iteration}/`) && task.name.endsWith("/verify") && !task.name.includes("integration"));
      expect(repairs.length).toBeGreaterThan(0);
      expect(verifies.map((task) => task.options.cwd)).toEqual(repairs.map((task) => task.options.cwd));
      expect(verifies.every((task) => task.options.context === "fresh" && task.options.schema !== undefined)).toBe(true);
      for (const repair of repairs) {
        expect(repair.options.cwd).toContain("worktrees");
        expect(worktrees.has(repair.options.cwd)).toBe(false);
        worktrees.add(repair.options.cwd);
      }
    }
    expect(names).toContain("iter-1/integration/verify");
    expect(names).not.toContain("iter-2/integration/verify");
    expect(names.filter((name) => name.startsWith("investigate/"))).toEqual([
      "investigate/checker-scalability", "investigate/certificate-reformulation", "investigate/diagnostics-ux",
    ]);
    expect(tasks.find((task) => task.name === "investigate/diagnostics-ux")?.options.excludedTools).toEqual(["edit", "write"]);
    expect(tasks.find((task) => task.name.endsWith("/repair"))?.options.prompt).toMatch(/Never add `admit`/);
  }, 120_000);

  test("an unavailable toolchain blocks before any agent stage with an actionable reason", async () => {
    const { output, tasks } = await runScripted(false);
    expect(output.status).toBe("blocked");
    expect(output.summary).toMatch(/toolchain unavailable.*F\* v2026\.09\.27/);
    expect(tasks).toEqual([]);
  }, 120_000);
});

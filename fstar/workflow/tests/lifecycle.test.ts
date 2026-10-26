/**
 * Publication lifecycle across runs, with real git (a scratch repository and a local bare
 * "origin") and a scripted gh. Agent stages are replaced by committing in the slice worktree and
 * by passing a verified verdict; every other step is the workflow's own step function.
 */
import { describe, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnRunner, type CommandLogEntry, type CommandResult, type CommandRunner } from "../lib/command.ts";
import type { VerifierVerdict } from "../lib/gate.ts";
import type { Finding } from "../lib/reports.ts";
import { readState, writeJsonAtomic, emptyState, type WorkflowState } from "../lib/state.ts";
import * as steps from "../lib/steps.ts";

type Pr = { number: number; state: "OPEN" | "MERGED" | "CLOSED"; url: string; head: string };

const signal = new AbortController().signal;
const verified: VerifierVerdict = {
  verdict: "verified", toolchainAvailable: true, commands: [{ command: "build and test the checker", exitCode: 0, phase: "final" }],
  resolvedFingerprints: [], soundnessConcerns: [], summary: "scripted verifier",
};

function finding(fingerprint: string): Finding {
  return {
    fingerprint, kind: "partial-rule", theory: "arrays", checker: "ocaml", rule: "rewrite", detail: `family ${fingerprint}`,
    affectedProofs: 2, obligations: 3, soleFamilyProofs: 1, examples: ["QF_AX/a.smt2"], evidence: ["results.jsonl"], sources: ["pulse-run:1-1"],
  };
}

function environment(prs: Pr[] = []) {
  const root = mkdtempSync(join(tmpdir(), "fpc-life-"));
  const repo = join(root, "repo");
  const origin = join(root, "origin.git");
  const stateDir = join(root, "state");
  const git = (cwd: string, ...args: string[]) => execFileSync("git", args, { cwd, encoding: "utf8" }).trim();
  mkdirSync(repo);
  git(root, "init", "-q", "--bare", "-b", "main", origin);
  git(repo, "init", "-q", "-b", "main");
  git(repo, "config", "user.email", "test@example.com");
  git(repo, "config", "user.name", "Test");
  mkdirSync(join(repo, "src"));
  writeFileSync(join(repo, "src", "Rule.fst"), "module Rule\nlet x = 1\n");
  git(repo, "add", "-A");
  git(repo, "commit", "-q", "-m", "init");
  git(repo, "remote", "add", "origin", origin);
  git(repo, "push", "-q", "origin", "main");
  const ok = (stdout = ""): CommandResult => ({ code: 0, stdout, stderr: "" });
  // gh is scripted; git runs for real against the local bare remote.
  const runner: CommandRunner = async (argv, options) => {
    if (argv[0] !== "gh") return spawnRunner(argv, options);
    const head = argv[argv.indexOf("--head") + 1] ?? "";
    if (argv[1] === "pr" && argv[2] === "list") {
      const state = argv[argv.indexOf("--state") + 1];
      return ok(JSON.stringify(prs.filter((pr) => pr.head === head && (state === "all" || pr.state.toLowerCase() === state)).map(({ number, state: s, url }) => ({ number, state: s, url }))));
    }
    if (argv[1] === "pr" && argv[2] === "create") {
      const number = 100 + prs.length;
      prs.push({ number, state: "OPEN", url: `https://github.com/Z3Prover/z3/pull/${number}`, head });
      return ok(`https://github.com/Z3Prover/z3/pull/${number}\n`);
    }
    throw new Error(`unexpected gh command ${argv.join(" ")}`);
  };
  const inputs = (publish: steps.WorkflowInputs["publish"], overrides: Partial<steps.WorkflowInputs> = {}): steps.WorkflowInputs => ({
    pulseRunIds: [], pulseBranch: "main", maxReports: 1, reportPaths: [], localCorpora: [], localCaseLimit: 0, ocamlChecker: "", cherryChecker: "",
    fstarExe: "", cherryFstarExe: "", wslDistro: "", opamRoot: "", opamSwitch: "fstar53", pwshExe: "", theories: [], maxIterations: 1, coreBudget: 32, coresPerSlice: 4, maxFindingsPerSlice: 2, publish, dryRun: false,
    investigate: false, stateDir, repo: "Z3Prover/z3", remote: "origin", baseRef: "main", prBase: "main", branchPrefix: "fstar-proof-checking", bugReportRepo: "FStarLang/FStar",
    ...overrides,
  });
  const setupFor = (runKey: string): steps.RunSetup => {
    const runDir = join(stateDir, "runs", runKey);
    mkdirSync(runDir, { recursive: true });
    return {
      repoRoot: repo, stateDir, runKey, runDir, worktreeRoot: join(stateDir, "worktrees"), startedAt: new Date().toISOString(),
      toolchain: { pwsh: "pwsh", opam: true, opamSwitch: "fstar53", candidates: {}, available: true, missing: [] },
    };
  };

  /**
   * Iterations exactly as the workflow entry sequences them, with scripted repair and verify
   * stages: each slice commits `src/<runKey>-<slice>.fst`, slice verifiers pass, and iteration i's
   * integration verifier returns `integrationVerdicts[i - 1]` (default: verified).
   */
  async function run(runKey: string, publish: steps.WorkflowInputs["publish"], findings: Finding[], options: { integrationVerdicts?: Array<VerifierVerdict | null>; overrides?: Partial<steps.WorkflowInputs> } = {}) {
    const setup = setupFor(runKey);
    const config = inputs(publish, options.overrides);
    const findingsPath = join(setup.runDir, "findings.json");
    writeFileSync(findingsPath, JSON.stringify(findings));
    const source: steps.SourceSummary = {
      findingsPath, total: findings.length, byKind: {}, byTheory: {}, localScans: {}, carried: [], diagnostics: [],
      reports: [{ key: `pulse-run:${runKey}-1`, directory: setup.runDir, artifacts: [], missing: [] }],
    };
    await steps.recordSourcesStep(setup, config, source);
    const verdicts = options.integrationVerdicts ?? [verified];
    const planned: string[] = [];
    const iterations = [];
    const worktrees: string[] = [];
    for (const [index, integrationVerdict] of verdicts.entries()) {
      const iteration = index + 1;
      const triage = steps.triageStep(setup, config, findingsPath, iteration, planned);
      const plan = await steps.planStep(setup, config, triage.actionablePath, iteration, signal, runner);
      planned.push(...plan.slices.flatMap((slice) => slice.fingerprints));
      for (const slice of plan.slices) {
        writeFileSync(join(slice.worktree, "src", `${runKey}-${slice.fingerprints.join("-")}.fst`), `module M\nlet y = 2\n`);
        git(slice.worktree, "add", "-A");
        git(slice.worktree, "-c", "user.email=test@example.com", "-c", "user.name=Test", "commit", "-q", "-m", `repair ${slice.id}`);
      }
      const gate = await steps.gateStep(setup, config, plan, plan.slices.map(() => verified), iteration, signal, runner);
      const integration = await steps.integrateStep(setup, config, plan, gate, iteration, signal, runner);
      const publication = await steps.publishStep(setup, config, plan, gate, integration, integration.worktree ? integrationVerdict : null, iteration, signal, runner);
      const persisted = await steps.persistStep(setup, config, plan, gate, integration, publication, iteration);
      worktrees.push(...plan.slices.map((slice) => slice.worktree), ...(integration.worktree ? [integration.worktree] : []));
      iterations.push({ triage, plan, gate, integration, publication, persisted, state: readState(stateDir) });
    }
    await steps.finalizeStep(setup, config, { status: "completed", stopReason: "test", iterations: [], investigation: { run: false, reason: "", digest: "" }, verified: 0, attempted: 0 }, [...new Set(worktrees)], signal, runner);
    const commands = readFileSync(join(setup.runDir, "commands.jsonl"), "utf8").split(/\r?\n/).filter(Boolean).map((line) => JSON.parse(line) as CommandLogEntry);
    return { ...(iterations[0] as (typeof iterations)[number]), iterations, commands, setup, state: readState(stateDir) };
  }

  const remoteBranches = () => git(repo, "ls-remote", "--heads", "origin").split(/\r?\n/).filter(Boolean).map((line) => line.split("refs/heads/")[1]);
  const contains = (ref: string, commit: string) => {
    try {
      execFileSync("git", ["merge-base", "--is-ancestor", commit, ref], { cwd: repo });
      return true;
    } catch {
      return false;
    }
  };
  const seed = (state: WorkflowState) => {
    mkdirSync(stateDir, { recursive: true });
    writeJsonAtomic(join(stateDir, "state.json"), state);
  };
  return { repo, stateDir, prs, git, run, inputs, setupFor, remoteBranches, contains, seed };
}

describe("verified work that is not published live", () => {
  test("is recorded as integrated and pending, not resolved, with no remote mutation", async () => {
    const env = environment();
    const first = await env.run("r1", "dry-run", [finding("f1")]);
    expect(first.gate.verified).toBe(1);
    expect(first.publication.executed).toBe(false);
    expect(first.commands.filter((entry) => entry.mutating)).toEqual([]);
    expect(env.remoteBranches()).toEqual(["main"]);
    expect(first.state.findings.f1?.status).toBe("integrated");
    expect(first.state.pendingPublications).toEqual([
      expect.objectContaining({ runKey: "r1", branch: first.integration.branch, head: first.integration.head, fingerprints: ["f1"] }),
    ]);
    // Report cursors advance in a real (non-dryRun) run: the findings are retained in state.
    expect(Object.keys(first.state.processedReports)).toEqual(["pulse-run:r1-1"]);
    // The integrated finding is not repaired again.
    const second = await env.run("r2", "dry-run", [finding("f1")]);
    expect(second.triage).toMatchObject({ actionable: 0, skipped: { integrated: 1 }, pendingPublications: 1 });
    expect(second.state.pendingPublications.map((entry) => entry.runKey)).toEqual(["r1"]);
  }, 120_000);

  test("is published by a later live run without new findings, then resolved and cleared", async () => {
    const env = environment();
    const first = await env.run("r1", "dry-run", [finding("f1")]);
    const second = await env.run("r2", "live", [finding("f1")]);
    expect(second.triage.actionable).toBe(0);
    expect(second.integration.pendingMerged).toEqual(["r1"]);
    expect(second.publication).toMatchObject({ executed: true, action: "new-branch", branch: "fstar-proof-checking/1" });
    expect(env.remoteBranches()).toContain("fstar-proof-checking/1");
    env.git(env.repo, "fetch", "-q", "origin");
    expect(env.contains("refs/remotes/origin/fstar-proof-checking/1", first.integration.head as string)).toBe(true);
    expect(env.prs).toHaveLength(1);
    expect(second.state.findings.f1?.status).toBe("resolved");
    expect(second.state.pendingPublications).toEqual([]);
    expect(second.state.publication).toMatchObject({ activeBranch: "fstar-proof-checking/1", prNumber: 100 });
  }, 120_000);

  test("after the active PR was merged, pending work goes to a new branch and PR", async () => {
    const env = environment([{ number: 100, state: "MERGED", url: "u100", head: "fstar-proof-checking/1" }]);
    env.git(env.repo, "push", "-q", "origin", "main:refs/heads/fstar-proof-checking/1");
    env.seed({ ...emptyState(), publication: { activeBranch: "fstar-proof-checking/1", prNumber: 100, prUrl: "u100", sequence: 1, history: [] } });
    await env.run("r1", "dry-run", [finding("f1")]);
    const second = await env.run("r2", "live", []);
    expect(second.publication).toMatchObject({ executed: true, action: "new-branch", branch: "fstar-proof-checking/2" });
    expect(env.prs.map((pr) => [pr.number, pr.state, pr.head])).toEqual([[100, "MERGED", "fstar-proof-checking/1"], [101, "OPEN", "fstar-proof-checking/2"]]);
    expect(second.state.publication).toMatchObject({ activeBranch: "fstar-proof-checking/2", prNumber: 101, sequence: 2 });
    expect(second.state.publication.history.map((entry) => entry.state)).toEqual(["MERGED"]);
    expect(second.state.findings.f1?.status).toBe("resolved");
    expect(second.state.pendingPublications).toEqual([]);
  }, 120_000);

  test("a pending integration whose local branch is gone stays pending with a reason", async () => {
    const env = environment();
    const base = emptyState();
    env.seed({
      ...base,
      findings: { f9: { fingerprint: "f9", kind: "partial-rule", theory: "arrays", rule: "rewrite", detail: "x", status: "integrated", attempts: 0, firstSeen: "t", lastSeen: "t", evidenceDigest: "d" } },
      pendingPublications: [{ runKey: "gone", branch: "fstar-proof-checking/integration/gone", head: "0123456789abcdef0123456789abcdef01234567", fingerprints: ["f9"], slices: ["arrays-repair"], recordedAt: "t" }],
    });
    const result = await env.run("r3", "live", []);
    expect(result.integration.pendingMerged).toEqual([]);
    expect(result.integration.pendingFailed).toEqual([{ runKey: "gone", reason: expect.stringMatching(/branch fstar-proof-checking\/integration\/gone is missing/) }]);
    expect(result.publication.executed).toBe(false);
    expect(result.commands.filter((entry) => entry.mutating)).toEqual([]);
    expect(result.state.findings.f9?.status).toBe("integrated");
    expect(result.state.pendingPublications).toEqual([expect.objectContaining({ runKey: "gone", lastError: expect.stringMatching(/missing/) })]);
    expect(env.remoteBranches()).toEqual(["main"]);
  }, 120_000);
});

describe("integration across iterations of one run", () => {
  const oneSlicePerIteration = { coreBudget: 4, coresPerSlice: 4, maxFindingsPerSlice: 1 };
  const alpha = { ...finding("fp-alpha"), affectedProofs: 5 };
  const beta = { ...finding("fp-beta"), affectedProofs: 1 };

  test("a merge whose integration verification failed does not leak into the next iteration's pending head", async () => {
    const env = environment();
    const failed: VerifierVerdict = { ...verified, verdict: "unverified", summary: "merged build failed" };
    const result = await env.run("r1", "dry-run", [alpha, beta], { integrationVerdicts: [failed, verified], overrides: oneSlicePerIteration });
    const [first, second] = result.iterations;
    expect(first?.plan.slices.map((slice) => slice.fingerprints)).toEqual([["fp-alpha"]]);
    expect(first?.publication.integrationVerified).toBe(false);
    expect(second?.plan.slices.map((slice) => slice.fingerprints)).toEqual([["fp-beta"]]);
    expect(second?.publication.integrationVerified).toBe(true);
    expect(result.state.findings["fp-alpha"]?.status).toBe("unverified");
    expect(result.state.findings["fp-beta"]?.status).toBe("integrated");
    const head = second?.integration.head as string;
    expect(result.state.pendingPublications).toEqual([expect.objectContaining({ runKey: "r1", head, fingerprints: ["fp-beta"] })]);
    const tree = env.git(env.repo, "ls-tree", "-r", "--name-only", head);
    expect(tree).toContain("src/r1-fp-beta.fst");
    expect(tree).not.toContain("src/r1-fp-alpha.fst");
    const body = readFileSync(join(result.setup.runDir, "iter-2", "pr-body.md"), "utf8");
    expect(body).toContain("fp-beta");
    expect(body).not.toContain("fp-alpha");
  }, 120_000);

  test("verified integrations of one run accumulate in one pending entry whose head contains exactly them", async () => {
    const env = environment();
    const result = await env.run("r1", "dry-run", [alpha, beta], { integrationVerdicts: [verified, verified], overrides: oneSlicePerIteration });
    const second = result.iterations[1];
    const head = second?.integration.head as string;
    expect(result.state.pendingPublications).toHaveLength(1);
    expect(result.state.pendingPublications[0]).toMatchObject({ runKey: "r1", head });
    expect([...(result.state.pendingPublications[0]?.fingerprints ?? [])].sort()).toEqual(["fp-alpha", "fp-beta"]);
    const tree = env.git(env.repo, "ls-tree", "-r", "--name-only", head);
    expect(tree).toContain("src/r1-fp-alpha.fst");
    expect(tree).toContain("src/r1-fp-beta.fst");
    const body = readFileSync(join(result.setup.runDir, "iter-2", "pr-body.md"), "utf8");
    expect(body).toContain("fp-alpha");
    expect(body).toContain("fp-beta");
  }, 120_000);

  test("a soundness concern from the integration verifier blocks the live push", async () => {
    const env = environment();
    const concerned: VerifierVerdict = { ...verified, soundnessConcerns: ["minor: the merged build relies on assume_ in a helper"] };
    const result = await env.run("r1", "live", [finding("f1")], { integrationVerdicts: [concerned] });
    expect(result.publication).toMatchObject({ integrationVerified: false, executed: false });
    expect(result.commands.filter((entry) => entry.mutating)).toEqual([]);
    expect(env.remoteBranches()).toEqual(["main"]);
    expect(env.prs).toEqual([]);
    expect(result.state.findings.f1?.status).not.toBe("resolved");
    expect(result.state.pendingPublications).toEqual([]);
  }, 120_000);
});

describe("dry-run workflow runs never touch state", () => {
  test("state.json is byte-identical after the step sequence of a dryRun run", async () => {
    const env = environment();
    await env.run("r1", "dry-run", [finding("f1")]);
    const path = join(env.stateDir, "state.json");
    const before = readFileSync(path);
    const setup = { ...env.setupFor("dry"), toolchain: { opam: false, opamSwitch: "fstar53", candidates: {}, available: false, missing: ["F*"] } };
    const options = { ...env.inputs("live"), dryRun: true, investigate: true };
    const findingsPath = join(setup.runDir, "findings.json");
    writeFileSync(findingsPath, JSON.stringify([finding("f2")]));
    const source: steps.SourceSummary = { findingsPath, total: 1, byKind: {}, byTheory: {}, localScans: { "local-scan:ocaml:x": { offset: 5, cases: 5, mode: "interactive" } }, carried: [], diagnostics: [], reports: [{ key: "pulse-run:dry-1", directory: setup.runDir, artifacts: [], missing: [] }] };
    const recorded = await steps.recordSourcesStep(setup, options, source);
    const triage = steps.triageStep(setup, options, findingsPath, 1, []);
    const plan = await steps.planStep(setup, options, triage.actionablePath, 1, signal);
    const gate = await steps.gateStep(setup, options, plan, [], 1, signal);
    const integration = await steps.integrateStep(setup, options, plan, gate, 1, signal);
    const publication = await steps.publishStep(setup, options, plan, gate, integration, null, 1, signal);
    const persisted = await steps.persistStep(setup, options, plan, gate, integration, publication, 1);
    await steps.finalizeStep(setup, options, { status: "completed", stopReason: "dry", iterations: [], investigation: steps.selectInvestigation(setup, options, source), verified: 0, attempted: 0 }, [], signal);
    expect(recorded.committed).toBe(false);
    expect(persisted.committed).toBe(false);
    expect(integration.pendingMerged).toEqual([]);
    expect(readFileSync(path).equals(before)).toBe(true);
    expect(existsSync(join(env.stateDir, "state.lock"))).toBe(false);
  }, 120_000);
});

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
  const inputs = (publish: steps.WorkflowInputs["publish"]): steps.WorkflowInputs => ({
    pulseRunIds: [], pulseBranch: "main", maxReports: 1, reportPaths: [], localCorpora: [], localCaseLimit: 0, ocamlChecker: "", cherryChecker: "",
    fstarExe: "", cherryFstarExe: "", theories: [], maxIterations: 1, coreBudget: 32, coresPerSlice: 4, maxFindingsPerSlice: 2, publish, dryRun: false,
    investigate: false, stateDir, repo: "Z3Prover/z3", remote: "origin", baseRef: "main", prBase: "main", branchPrefix: "fstar-proof-checking", bugReportRepo: "FStarLang/FStar",
  });
  const setupFor = (runKey: string): steps.RunSetup => {
    const runDir = join(stateDir, "runs", runKey);
    mkdirSync(runDir, { recursive: true });
    return {
      repoRoot: repo, stateDir, runKey, runDir, worktreeRoot: join(stateDir, "worktrees"), startedAt: new Date().toISOString(),
      toolchain: { pwsh: true, opam: true, available: true, missing: [] },
    };
  };

  /** One iteration exactly as the workflow entry sequences it, with scripted repair and verify stages. */
  async function run(runKey: string, publish: steps.WorkflowInputs["publish"], findings: Finding[]) {
    const setup = setupFor(runKey);
    const options = inputs(publish);
    const findingsPath = join(setup.runDir, "findings.json");
    writeFileSync(findingsPath, JSON.stringify(findings));
    const source: steps.SourceSummary = {
      findingsPath, total: findings.length, byKind: {}, byTheory: {}, localScans: {}, diagnostics: [],
      reports: [{ key: `pulse-run:${runKey}-1`, directory: setup.runDir, artifacts: [], missing: [] }],
    };
    const triage = steps.triageStep(setup, options, findingsPath, 1, []);
    const plan = await steps.planStep(setup, options, triage.actionablePath, 1, signal, runner);
    for (const slice of plan.slices) {
      writeFileSync(join(slice.worktree, "src", `${runKey}.fst`), `module ${runKey.toUpperCase()}\nlet y = 2\n`);
      git(slice.worktree, "add", "-A");
      git(slice.worktree, "-c", "user.email=test@example.com", "-c", "user.name=Test", "commit", "-q", "-m", `repair ${slice.id}`);
    }
    const gate = await steps.gateStep(setup, options, plan, plan.slices.map(() => verified), 1, signal, runner);
    const integration = await steps.integrateStep(setup, options, plan, gate, 1, signal, runner);
    const publication = await steps.publishStep(setup, options, plan, gate, integration, integration.worktree ? verified : null, 1, signal, runner);
    const persisted = await steps.persistStep(setup, options, source, plan, gate, integration, publication, 1);
    const worktrees = [...plan.slices.map((slice) => slice.worktree), ...(integration.worktree ? [integration.worktree] : [])];
    await steps.finalizeStep(setup, options, { status: "completed", stopReason: "test", iterations: [], investigation: { run: false, reason: "", digest: "" }, verified: gate.verified, attempted: plan.slices.length }, worktrees, signal, runner);
    const commands = readFileSync(join(setup.runDir, "commands.jsonl"), "utf8").split(/\r?\n/).filter(Boolean).map((line) => JSON.parse(line) as CommandLogEntry);
    return { triage, plan, gate, integration, publication, persisted, commands, state: readState(stateDir) };
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

describe("dry-run workflow runs never touch state", () => {
  test("state.json is byte-identical after the step sequence of a dryRun run", async () => {
    const env = environment();
    await env.run("r1", "dry-run", [finding("f1")]);
    const path = join(env.stateDir, "state.json");
    const before = readFileSync(path);
    const setup = { ...env.setupFor("dry"), toolchain: { pwsh: false, opam: false, available: false, missing: ["F*"] } };
    const options = { ...env.inputs("live"), dryRun: true, investigate: true };
    const findingsPath = join(setup.runDir, "findings.json");
    writeFileSync(findingsPath, JSON.stringify([finding("f2")]));
    const source: steps.SourceSummary = { findingsPath, total: 1, byKind: {}, byTheory: {}, localScans: { "local-scan:ocaml:x": { offset: 5, cases: 5, mode: "interactive" } }, diagnostics: [], reports: [{ key: "pulse-run:dry-1", directory: setup.runDir, artifacts: [], missing: [] }] };
    const triage = steps.triageStep(setup, options, findingsPath, 1, []);
    const plan = await steps.planStep(setup, options, triage.actionablePath, 1, signal);
    const gate = await steps.gateStep(setup, options, plan, [], 1, signal);
    const integration = await steps.integrateStep(setup, options, plan, gate, 1, signal);
    const publication = await steps.publishStep(setup, options, plan, gate, integration, null, 1, signal);
    const persisted = await steps.persistStep(setup, options, source, plan, gate, integration, publication, 1);
    await steps.finalizeStep(setup, options, { status: "completed", stopReason: "dry", iterations: [], investigation: steps.selectInvestigation(setup, options, source), verified: 0, attempted: 0 }, [], signal);
    expect(persisted.committed).toBe(false);
    expect(integration.pendingMerged).toEqual([]);
    expect(readFileSync(path).equals(before)).toBe(true);
    expect(existsSync(join(env.stateDir, "state.lock"))).toBe(false);
  }, 120_000);
});

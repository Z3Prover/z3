/**
 * Open-PR-aware sourcing. A run fetches its base once (read-only) and pins it to one commit that
 * every step uses; sourcing snapshots the open PRs that change fstar/ (read-only), and triage
 * annotates actionable findings with the PRs they overlap. PR data is metadata: it changes no
 * status and never releases a policy hold or a candidate. git runs for real against scratch
 * repositories with a local bare "origin"; gh is scripted.
 */
import { afterAll, beforeAll, describe, expect, spyOn, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { registerAtomicHostModules } from "../lib/atomic-host.ts";
import { spawnRunner, type CommandLogEntry, type CommandResult, type CommandRunner } from "../lib/command.ts";
import type { VerifierVerdict } from "../lib/gate.ts";
import type { Finding } from "../lib/reports.ts";
import { emptyState, readState, recordSeen, writeJsonAtomic } from "../lib/state.ts";
import * as steps from "../lib/steps.ts";
import type { ToolchainReport } from "../lib/toolchain.ts";

const signal = new AbortController().signal;
const fakeToolchain: ToolchainReport = { pwsh: "pwsh", opam: true, opamSwitch: "fstar53", candidates: {}, available: true, missing: [] };
const verified: VerifierVerdict = {
  verdict: "verified", toolchainAvailable: true, commands: [{ command: "build and test the checker", exitCode: 0, phase: "final" }],
  resolvedFingerprints: [], soundnessConcerns: [], summary: "scripted verifier",
};
const ok = (stdout = ""): CommandResult => ({ code: 0, stdout, stderr: "" });

let prompts: typeof import("../lib/prompts.ts");
let probe: { mockRestore(): void };
beforeAll(async () => {
  // The prompts import Atomic's host-provided SDK; the toolchain probe is replaced so no test reaches WSL, opam or F*.
  await registerAtomicHostModules();
  prompts = await import("../lib/prompts.ts");
  probe = spyOn(await import("../lib/toolchain.ts"), "probeToolchain").mockImplementation(async () => fakeToolchain);
}, 120_000);
afterAll(() => probe.mockRestore());

const git = (cwd: string, ...args: string[]) => execFileSync("git", ["-c", "user.email=test@example.com", "-c", "user.name=Test", ...args], { cwd, encoding: "utf8" }).trim();

/**
 * A repository whose `origin/main` is stale: the bare origin has moved on to `fresh` since the last
 * fetch (`stale`). The origin also carries `refs/pull/11348/head`, an open PR that changes the
 * declaration `Z3BvWord.lemma_append_number`.
 */
function environment() {
  const root = mkdtempSync(join(tmpdir(), "fpc-openpr-"));
  const repo = join(root, "repo");
  const upstream = join(root, "upstream");
  const origin = join(root, "origin.git");
  const stateDir = join(root, "state");
  mkdirSync(join(repo, "fstar"), { recursive: true });
  git(root, "init", "-q", "--bare", "-b", "main", origin);
  git(repo, "init", "-q", "-b", "main");
  writeFileSync(join(repo, "fstar", "Z3BvWord.fst"), "module Z3BvWord\n\nlet lemma_append_number (x: nat) : unit = ()\n\nlet other = 1\n");
  git(repo, "add", "-A");
  git(repo, "commit", "-q", "-m", "init");
  git(repo, "remote", "add", "origin", origin);
  git(repo, "push", "-q", "origin", "main");
  git(repo, "fetch", "-q", "origin");
  const stale = git(repo, "rev-parse", "origin/main");
  git(root, "clone", "-q", origin, upstream);
  writeFileSync(join(upstream, "fstar", "Upstream.fst"), "module Upstream\n");
  git(upstream, "add", "-A");
  git(upstream, "commit", "-q", "-m", "upstream moves on");
  git(upstream, "push", "-q", "origin", "main");
  const fresh = git(upstream, "rev-parse", "HEAD");
  git(upstream, "checkout", "-q", "-b", "pr");
  // The PR changes `lemma_append_number` (a local `let` inside it is not a declaration of its own).
  writeFileSync(join(upstream, "fstar", "Z3BvWord.fst"), "module Z3BvWord\n\nlet lemma_append_number (x: nat) : unit =\n  let y = x in\n  assert (y >= 0)\n\nlet other = 1\n");
  mkdirSync(join(upstream, "fstar", "audits", "pr-11348"), { recursive: true });
  writeFileSync(join(upstream, "fstar", "audits", "pr-11348", "notes.md"), "audit\n");
  git(upstream, "add", "-A");
  git(upstream, "commit", "-q", "-m", "PR: speed up lemma_append_number");
  git(upstream, "push", "-q", "origin", "HEAD:refs/pull/11348/head");
  const prHead = git(upstream, "rev-parse", "HEAD");
  const inputs = (overrides: Partial<steps.WorkflowInputs> = {}): steps.WorkflowInputs => ({
    pulseRunIds: [], pulseBranch: "main", maxReports: 1, reportPaths: [], localCorpora: [], localCaseLimit: 0, ocamlChecker: "", cherryChecker: "",
    fstarExe: "", cherryFstarExe: "", wslDistro: "", opamRoot: "", opamSwitch: "fstar53", pwshExe: "", theories: [], maxIterations: 1, coreBudget: 8, coresPerSlice: 4,
    maxFindingsPerSlice: 2, publish: "none", dryRun: false, investigate: false, stateDir, repo: "Z3Prover/z3", remote: "origin", baseRef: "origin/main", prBase: "main",
    branchPrefix: "fstar-proof-checking", bugReportRepo: "FStarLang/FStar", ...overrides,
  });
  return { root, repo, upstream, origin, stateDir, stale, fresh, prHead, inputs };
}

/** gh rows as `gh pr list --json number,title,headRefName,headRefOid,baseRefName,url,files` prints them. */
function ghRows(prHead: string) {
  const row = (number: number, headRefName: string, head: string, paths: string[], title = `PR ${number}`) => ({
    number, title, headRefName, headRefOid: head, baseRefName: "main", url: `https://github.com/Z3Prover/z3/pull/${number}`,
    files: paths.map((path) => ({ path, additions: 1, deletions: 0 })),
  });
  return [
    row(11354, "fix/11347-array-map-coherence", "a".repeat(40), ["fstar/audits/pr-11354/README.md", "fstar/audits/pr-11354/replay.json", "src/smt/theory_array_full.cpp"], "Fix array-map equalities"),
    row(11348, "automation/pulse-checker-continuous", prHead, [
      "fstar/Z3BvWord.fst", "fstar/cherry_runtime/tests.cpp", "fstar/tools/checker_modules.json", "fstar/OCAML_CHECKER_REPORT.md",
      "fstar/audits/pr-11348/notes.md", "src/cmd_context/basic_cmds.cpp",
    ], "F*: improve checker coverage, startup, and proof compilation"),
    row(11351, "fstar-proof-checking-workflow", "b".repeat(40), ["fstar/workflow/README.md", "fstar/workflow/lib/steps.ts"]),
    row(11353, "fix/wasm-tactic-registration", "c".repeat(40), ["src/api/js/src/high-level.ts"]),
    row(11360, "fstar-proof-checking/3", "d".repeat(40), ["fstar/Z3BvWord.fst"]),
  ];
}

/** git runs for real; `gh pr list` answers with `rows` (or `gh`), and every command is recorded. */
function recordingRunner(rows: unknown, options: { gh?: CommandRunner; failFetchOf?: string } = {}) {
  const calls: Array<readonly string[]> = [];
  const runner: CommandRunner = async (argv, commandOptions) => {
    calls.push(argv);
    if (argv[0] === "gh") return options.gh ? options.gh(argv, commandOptions) : argv[1] === "pr" && argv[2] === "list" ? ok(JSON.stringify(rows)) : ok("[]");
    if (options.failFetchOf && argv[1] === "fetch" && argv.some((arg) => arg.includes(options.failFetchOf as string))) {
      return { code: 128, stdout: "", stderr: "fatal: unable to access 'https://github.com/Z3Prover/z3/': Could not resolve host: github.com" };
    }
    return spawnRunner(argv, commandOptions);
  };
  return { runner, calls };
}

function finding(fingerprint: string, overrides: Partial<Finding> = {}): Finding {
  return {
    fingerprint, kind: "partial-rule", theory: "bitvectors", checker: "ocaml", rule: "rewrite", detail: `family ${fingerprint}`,
    affectedProofs: 2, obligations: 3, soleFamilyProofs: 1, examples: ["QF_BV/a.smt2"], evidence: ["results.jsonl"], sources: ["pulse-run:1-1"], ...overrides,
  };
}

const slowDeclaration = (fingerprint: string, rule: string) => finding(fingerprint, {
  kind: "slow-obligation", checker: "fstar-build", rule, detail: "process_one_decl took 3000 ms (> 2000 ms)", milliseconds: 3000, examples: [], affectedProofs: 1, obligations: 1, soleFamilyProofs: 0,
});

const commandsOf = (runDir: string) => readFileSync(join(runDir, "commands.jsonl"), "utf8").split(/\r?\n/).filter(Boolean).map((line) => JSON.parse(line) as CommandLogEntry);

describe("pinned base", () => {
  test("preflight fetches the base read-only and pins it; worktrees, the gate and integration all use that commit", async () => {
    const env = environment();
    const { runner, calls } = recordingRunner([]);
    const setup = await steps.preflight(env.inputs(), env.repo, signal, runner);
    expect(calls).toContainEqual(["git", "fetch", "--no-tags", "origin", "+refs/heads/main:refs/remotes/origin/main"]);
    expect(setup.baseSha).toBe(env.fresh);
    expect(setup.baseStale).toBeUndefined();
    expect(JSON.parse(readFileSync(join(setup.runDir, "setup.json"), "utf8")).setup.baseSha).toBe(env.fresh);

    // origin/main moves again mid-run: the run keeps the commit it pinned.
    writeFileSync(join(env.upstream, "late.txt"), "late\n");
    git(env.upstream, "checkout", "-q", "main");
    git(env.upstream, "add", "-A");
    git(env.upstream, "commit", "-q", "-m", "late");
    git(env.upstream, "push", "-q", "origin", "main");
    git(env.repo, "fetch", "-q", "origin");
    expect(git(env.repo, "rev-parse", "origin/main")).not.toBe(env.fresh);

    const findingsPath = join(setup.runDir, "findings.json");
    writeFileSync(findingsPath, JSON.stringify([finding("f1")]));
    const triage = steps.triageStep(setup, env.inputs(), findingsPath, 1, []);
    const plan = await steps.planStep(setup, env.inputs(), triage.actionablePath, 1, signal, runner);
    const [slice] = plan.slices;
    if (!slice) throw new Error("expected one slice");
    expect(git(slice.worktree, "rev-parse", "HEAD")).toBe(env.fresh);
    writeFileSync(join(slice.worktree, "fstar", "Fix.fst"), "module Fix\n");
    git(slice.worktree, "add", "-A");
    git(slice.worktree, "commit", "-q", "-m", "repair");
    const gate = await steps.gateStep(setup, env.inputs(), plan, [verified], 1, signal, runner);
    expect(gate.verified).toBe(1);
    const integration = await steps.integrateStep(setup, env.inputs(), plan, gate, 1, signal, runner);
    expect(integration.base).toBe(env.fresh);

    const worktreeAdds = calls.filter((argv) => argv.includes("worktree") && argv.includes("add"));
    expect(worktreeAdds.map((argv) => argv.at(-1))).toEqual([env.fresh, env.fresh]);
    expect(calls).toContainEqual(["git", "diff", "--no-color", `${env.fresh}...HEAD`]);
    expect(calls.filter((argv) => argv[1] === "fetch")).toHaveLength(1);
    expect(commandsOf(setup.runDir).filter((entry) => entry.mutating)).toEqual([]);
  }, 120_000);

  test("a failed fetch does not fall back silently: the run proceeds on the last fetched commit and records it as stale", async () => {
    const env = environment();
    const { runner } = recordingRunner([], { failFetchOf: "refs/heads/main" });
    const setup = await steps.preflight(env.inputs(), env.repo, signal, runner);
    expect(setup.baseSha).toBe(env.stale);
    expect(setup.baseStale).toBe(true);
    expect(setup.baseNote).toMatch(/fetching origin\/main failed.*Could not resolve host.*may be stale/);
    expect(JSON.parse(readFileSync(join(setup.runDir, "setup.json"), "utf8")).setup).toMatchObject({ baseSha: env.stale, baseStale: true });
    const final = await steps.finalizeStep(setup, env.inputs({ dryRun: true }), { status: "completed", stopReason: "test", iterations: [], investigation: { run: false, reason: "", digest: "" }, verified: 0, attempted: 0 }, [], signal, runner);
    expect(JSON.parse(readFileSync(final.evidencePath, "utf8")).base).toMatchObject({ ref: "origin/main", sha: env.stale, stale: true });
    const prompt = prompts.repairPrompt({
      sliceId: "s", theory: "bitvectors", focus: "repair", worktree: env.repo, branch: "b", baseRef: setup.baseSha ?? "", cores: 4,
      findingsPath: "f.json", sliceDir: env.root, toolchain: fakeToolchain, ...(setup.baseNote ? { baseNote: setup.baseNote } : {}),
    });
    expect(prompt).toContain(`Base note: ${setup.baseNote}`);
  }, 120_000);

  test("a dry run fetches nothing but still records the commit it would use", async () => {
    const env = environment();
    const { runner, calls } = recordingRunner([]);
    const setup = await steps.preflight(env.inputs({ dryRun: true }), env.repo, signal, runner);
    expect(calls.filter((argv) => argv[1] === "fetch")).toEqual([]);
    expect(setup.baseSha).toBe(env.stale);
    expect(setup.baseStale).toBeUndefined();
  }, 120_000);
});

describe("open-PR snapshot", () => {
  test("keeps PRs that change fstar/, with checker sources apart from audit-only and workflow files, and pins each to its head", async () => {
    const env = environment();
    const { runner, calls } = recordingRunner(ghRows(env.prHead));
    const setup = await steps.preflight(env.inputs(), env.repo, signal, runner);
    const source = await steps.sourceFindings(setup, env.inputs(), signal, runner);
    const snapshot = source.openPrs as any;
    expect(snapshot.status).toBe("available");
    expect(snapshot.prs.map((pr: any) => [pr.number, pr.fstar])).toEqual([[11348, "sources"], [11354, "audit-only"]]);
    const [sources, auditOnly] = snapshot.prs;
    expect(sources).toMatchObject({
      head: env.prHead,
      fstarSources: ["fstar/Z3BvWord.fst", "fstar/cherry_runtime/tests.cpp", "fstar/tools/checker_modules.json"],
      fstarAuditOnly: ["fstar/OCAML_CHECKER_REPORT.md", "fstar/audits/pr-11348/notes.md"],
      otherFiles: ["src/cmd_context/basic_cmds.cpp"],
      localRef: "refs/fstar-proof-checking/prs/11348",
      declarations: ["Z3BvWord.lemma_append_number"],
    });
    expect(auditOnly).toMatchObject({ fstarSources: [], fstarAuditOnly: ["fstar/audits/pr-11354/README.md", "fstar/audits/pr-11354/replay.json"], otherFiles: ["src/smt/theory_array_full.cpp"] });
    expect(auditOnly.localRef).toBeUndefined();
    expect(snapshot.ignored.map((item: any) => item.number).sort()).toEqual([11351, 11353, 11360]);
    // Only the source PR's head is fetched, read-only, into the private namespace; nothing is pushed or merged.
    expect(calls.filter((argv) => argv[1] === "fetch" && argv.some((arg) => arg.includes("refs/pull/")))).toEqual([
      ["git", "fetch", "--no-tags", "origin", "+refs/pull/11348/head:refs/fstar-proof-checking/prs/11348"],
    ]);
    expect(git(env.repo, "rev-parse", "refs/fstar-proof-checking/prs/11348")).toBe(env.prHead);
    expect(calls.some((argv) => ["merge", "cherry-pick", "push", "checkout"].includes(argv[1] as string))).toBe(false);
    expect(JSON.parse(readFileSync(join(setup.runDir, "open-prs.json"), "utf8"))).toEqual(snapshot);
    await steps.recordSourcesStep(setup, env.inputs(), source);
    expect(JSON.parse(readFileSync(join(setup.runDir, "sources-recorded.json"), "utf8")).openPrs.prs.map((pr: any) => [pr.number, pr.head])).toEqual([[11348, env.prHead], [11354, "a".repeat(40)]]);
  }, 120_000);

  test("a failing gh is recorded as unavailable and sourcing continues", async () => {
    const env = environment();
    const log = join(env.root, "build.log");
    writeFileSync(log, "Z3BvWord.lemma_append_number, profiled FStarC.TypeChecker.Tc.process_one_decl: 3000 ms\n");
    // Only the PR listing fails; the Pulse run listing still answers (no runs).
    const failing = (fail: CommandRunner): CommandRunner => async (argv, options) => (argv[1] === "pr" ? fail(argv, options) : ok("[]"));
    for (const gh of [
      failing(async () => ({ code: 1, stdout: "", stderr: "HTTP 502: Bad Gateway (https://api.github.com/graphql)" })),
      failing(async () => {
        throw new Error("gh: command not found");
      }),
    ]) {
      const { runner } = recordingRunner([], { gh });
      const setup = await steps.preflight(env.inputs(), env.repo, signal, runner);
      const source = await steps.sourceFindings(setup, env.inputs({ reportPaths: [log] }), signal, runner);
      expect(source.total).toBe(1);
      expect(source.openPrs).toMatchObject({ status: "unavailable" });
      expect((source.openPrs as any).error).toMatch(/HTTP 502|command not found/);
      expect(JSON.parse(readFileSync(join(setup.runDir, "open-prs.json"), "utf8")).status).toBe("unavailable");
      expect(source.diagnostics.some((line) => line.startsWith("Open PRs unavailable"))).toBe(true);
    }
  }, 120_000);
});

describe("overlap annotations", () => {
  const snapshotWith = (head: string, prs: number[] = [11348]) => ({
    status: "available" as const, at: "2026-10-26T17:00:00Z", repo: "Z3Prover/z3", base: "0".repeat(40), ignored: [],
    prs: [
      ...(prs.includes(11348) ? [{
        number: 11348, title: "F*: improve checker coverage", url: "u", headRefName: "automation/pulse-checker-continuous", head, baseRefName: "master", fstar: "sources" as const,
        fstarSources: ["fstar/Z3BvWord.fst", "fstar/cherry_runtime/tests.cpp"], fstarAuditOnly: ["fstar/audits/pr-11348/notes.md"], otherFiles: ["src/cmd_context/basic_cmds.cpp"],
        localRef: "refs/fstar-proof-checking/prs/11348", declarations: ["Z3BvWord.lemma_append_number"],
      }] : []),
      {
        number: 11354, title: "Fix array-map equalities", url: "u", headRefName: "fix", head: "a".repeat(40), baseRefName: "master", fstar: "audit-only" as const,
        fstarSources: [], fstarAuditOnly: ["fstar/audits/pr-11354/README.md"], otherFiles: ["src/smt/theory_array_full.cpp"],
      },
    ],
  });

  function triageEnv(findings: Finding[]) {
    const root = mkdtempSync(join(tmpdir(), "fpc-overlap-"));
    const stateDir = join(root, "state");
    const runDir = join(stateDir, "runs", "k");
    mkdirSync(runDir, { recursive: true });
    const setup: steps.RunSetup = { repoRoot: root, stateDir, runKey: "k", runDir, worktreeRoot: join(root, "wt"), startedAt: "t", toolchain: fakeToolchain, baseSha: "0".repeat(40) };
    const findingsPath = join(runDir, "findings.json");
    writeFileSync(findingsPath, JSON.stringify(findings));
    const inputs = { theories: [], dryRun: true, coreBudget: 8, coresPerSlice: 4, maxFindingsPerSlice: 2, branchPrefix: "fstar-proof-checking" } as unknown as steps.WorkflowInputs;
    return { setup, stateDir, findingsPath, inputs };
  }
  const actionableOf = (path: string) => JSON.parse(readFileSync(path, "utf8")) as Array<Finding & { prOverlap?: any[] }>;

  test("findings are annotated with the PRs they overlap, exact apart from potential, pinned to the head; a new head or a closed PR is re-evaluated", () => {
    const exact = slowDeclaration("exact", "Z3BvWord.lemma_append_number");
    const sameModule = slowDeclaration("module", "Z3BvWord.other");
    const elsewhere = slowDeclaration("elsewhere", "Z3Other.lemma");
    const rule = finding("rule");
    const { setup, findingsPath, inputs } = triageEnv([exact, sameModule, elsewhere, rule]);
    const head = "1".repeat(40);
    const byFingerprint = (snapshot: unknown, iteration: number) =>
      new Map(actionableOf(steps.triageStep(setup, inputs, findingsPath, iteration, [], snapshot as any).actionablePath).map((item) => [item.fingerprint, item.prOverlap]));
    const first = byFingerprint(snapshotWith(head), 1);
    expect(first.get("exact")).toEqual([{ pr: 11348, head, title: "F*: improve checker coverage", kind: "exact", files: ["fstar/Z3BvWord.fst"], declarations: ["Z3BvWord.lemma_append_number"] }]);
    expect(first.get("module")).toEqual([{ pr: 11348, head, title: "F*: improve checker coverage", kind: "potential", files: ["fstar/Z3BvWord.fst"] }]);
    expect(first.get("elsewhere")).toBeUndefined();
    // A finding without a module may need any checker source its slice can edit; audit-only PRs never overlap.
    expect(first.get("rule")).toEqual([{ pr: 11348, head, title: "F*: improve checker coverage", kind: "potential", files: ["fstar/Z3BvWord.fst", "fstar/cherry_runtime/tests.cpp"] }]);
    const moved = byFingerprint(snapshotWith("2".repeat(40)), 2);
    expect(moved.get("exact")?.map((item: any) => item.head)).toEqual(["2".repeat(40)]);
    const closed = byFingerprint(snapshotWith(head, []), 3);
    expect([...closed.values()].every((value) => value === undefined)).toBe(true);
    const unavailable = byFingerprint({ status: "unavailable", at: "t", repo: "Z3Prover/z3", error: "HTTP 502" }, 4);
    expect([...unavailable.values()].every((value) => value === undefined)).toBe(true);
  });

  test("policy-held and candidate findings stay excluded and unchanged, whatever the PR data", () => {
    const held = slowDeclaration("held", "Z3BvWord.lemma_append_number");
    const candidate = slowDeclaration("candidate", "Z3BvWord.lemma_append_number");
    const open = slowDeclaration("open", "Z3BvWord.lemma_append_number");
    const { setup, stateDir, findingsPath, inputs } = triageEnv([held, candidate, open]);
    const seen = recordSeen(emptyState(), [held, candidate, open], new Date("2026-10-26T10:00:00Z"));
    const records = seen.findings;
    writeJsonAtomic(join(stateDir, "state.json"), {
      ...seen,
      findings: {
        ...records,
        held: { ...records.held!, status: "provider_policy_blocked", providerBlock: { runKey: "r0", stage: "iter-1/x/repair", error: "cyber_policy", at: "2026-10-26T10:00:00Z" } },
        candidate: { ...records.candidate!, candidate: { runKey: "r0", branch: "fstar-proof-checking/work/r0/i1-bitvectors-performance", commit: "016756695" } },
      },
    });
    const before = readFileSync(join(stateDir, "state.json"));
    const triage = steps.triageStep(setup, inputs, findingsPath, 1, [], snapshotWith("1".repeat(40)));
    expect(triage.skipped).toEqual({ "provider-policy-blocked": 1, candidate: 1 });
    expect(actionableOf(triage.actionablePath).map((item) => [item.fingerprint, item.prOverlap?.[0]?.kind])).toEqual([["open", "exact"]]);
    expect(readFileSync(join(stateDir, "state.json")).equals(before)).toBe(true);
    expect(readState(stateDir).findings.held?.status).toBe("provider_policy_blocked");
    expect(readState(stateDir).findings.candidate?.candidate?.commit).toBe("016756695");
  });

  test("repair and verify prompts list the open PRs that touch the slice's files, exact apart from potential, and deny credit for PR coverage", async () => {
    const { setup, findingsPath, inputs } = triageEnv([slowDeclaration("exact", "Z3BvWord.lemma_append_number"), slowDeclaration("module", "Z3BvWord.other")]);
    const head = "1".repeat(40);
    const triage = steps.triageStep(setup, inputs, findingsPath, 1, [], snapshotWith(head));
    const plan = await steps.planStep(setup, inputs, triage.actionablePath, 1, signal);
    const [slice] = plan.slices;
    if (!slice) throw new Error("expected one slice");
    expect(slice.openPrs?.map((pr) => [pr.pr, pr.head])).toEqual([[11348, head]]);
    const input = {
      sliceId: slice.id, theory: slice.theory, focus: slice.focus, worktree: slice.worktree, branch: slice.branch, baseRef: setup.baseSha ?? "", cores: 4,
      findingsPath: slice.findingsPath, sliceDir: slice.sliceDir, toolchain: fakeToolchain, openPrs: slice.openPrs ?? [], remote: "origin",
    };
    const line = `- #11348 at ${head} "F*: improve checker coverage" — EXACT coverage: the PR changes the declaration of finding(s) exact (Z3BvWord.lemma_append_number); POTENTIAL overlap (same files only) for 1 other finding(s). Files: fstar/Z3BvWord.fst.`;
    for (const prompt of [prompts.repairPrompt(input), prompts.verifyPrompt({ ...input, reportPath: "r.md" })]) {
      expect(prompt).toContain(line);
      expect(prompt).toContain("git fetch origin +refs/pull/11348/head:refs/fstar-proof-checking/prs/11348");
      expect(prompt).toContain(`git diff ${"0".repeat(40)}...<ref> -- <files>`);
      expect(prompt).toContain("covered by open PR #<n> at <head>");
      expect(prompt).toContain("merged PR #11341");
    }
    expect(prompts.verifyPrompt({ ...input, reportPath: "r.md" })).toContain("is not verified in this run: an open PR's fix earns no ACCEPT credit here, so never list it in resolvedFingerprints");
    const unavailable = prompts.repairPrompt({ ...input, openPrs: [], openPrsNote: "unavailable: HTTP 502" });
    expect(unavailable).toContain("Open pull requests: no snapshot this run (unavailable: HTTP 502)");
    expect(existsSync(slice.findingsPath) && JSON.parse(readFileSync(slice.findingsPath, "utf8"))[0].prOverlap[0].head).toBe(head);
  }, 120_000);
});

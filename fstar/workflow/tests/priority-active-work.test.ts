/**
 * Priority theories and active-work reservations. `priorityTheories` (launcher flag
 * `--priority-theories`) moves actionable findings of those theories ahead of the others;
 * `<stateDir>/active-work.json` reserves findings, theories and files for other local work, which
 * triage skips and the stage prompts name. Neither touches policy-held or candidate findings,
 * and a malformed reservation file blocks instead of failing open.
 */
import { beforeAll, describe, expect, test } from "bun:test";
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { activeWorkFor, readActiveWork, type ActiveWork } from "../lib/active-work.ts";
import { registerAtomicHostModules } from "../lib/atomic-host.ts";
import type { Finding } from "../lib/reports.ts";
import { emptyState, readState, recordSeen, writeJsonAtomic } from "../lib/state.ts";
import * as steps from "../lib/steps.ts";
import type { ToolchainReport } from "../lib/toolchain.ts";

const launcher = join(import.meta.dir, "..", "continuity.ts");
const buildLog = join(import.meta.dir, "fixtures", "build-run-40280393373-1", "pulse-checker-build-report", "build.log");
const toolchain: ToolchainReport = { pwsh: "pwsh", opam: true, opamSwitch: "fstar53", candidates: {}, available: true, missing: [] };
const QFFF: ActiveWork = {
  branch: "fstar-qfff-priority-20261026", worktree: "C:/z3atomic-qfff-priority", owner: "60c9d927", createdAt: "2026-10-26T15:00:00Z",
  theories: ["finite-fields"], fingerprints: ["ff-reserved"], note: "focused QF_FF run",
};

let prompts: typeof import("../lib/prompts.ts");
beforeAll(async () => {
  await registerAtomicHostModules();
  prompts = await import("../lib/prompts.ts");
}, 120_000);

function finding(fingerprint: string, theory: Finding["theory"], affectedProofs: number, kind: Finding["kind"] = "partial-rule"): Finding {
  return {
    fingerprint, kind, theory, checker: "ocaml", rule: "rewrite", detail: `family ${fingerprint}`,
    affectedProofs, obligations: affectedProofs, soleFamilyProofs: 0, examples: [`${theory}/${fingerprint}.smt2`], evidence: ["results.jsonl"], sources: ["pulse-run:1-1"],
  };
}

/** A run directory with these findings sourced, and `state` and `activeWork` (raw file text) in its state directory. */
function triageEnv(findings: Finding[], options: { state?: (seen: ReturnType<typeof recordSeen>) => unknown; activeWork?: string } = {}) {
  const stateDir = mkdtempSync(join(tmpdir(), "fpc-priority-"));
  const runDir = join(stateDir, "runs", "k");
  mkdirSync(runDir, { recursive: true });
  if (options.state) writeJsonAtomic(join(stateDir, "state.json"), options.state(recordSeen(emptyState(), findings, new Date("2026-10-26T10:00:00Z"))));
  if (options.activeWork !== undefined) writeFileSync(join(stateDir, "active-work.json"), options.activeWork);
  const setup: steps.RunSetup = { repoRoot: stateDir, stateDir, runKey: "k", runDir, worktreeRoot: join(stateDir, "wt"), startedAt: "t", toolchain, activeWork: readActiveWork(stateDir) };
  const findingsPath = join(runDir, "findings.json");
  writeFileSync(findingsPath, JSON.stringify(findings));
  const triage = (priorityTheories?: Finding["theory"][], iteration = 1) => {
    const inputs = { theories: [], ...(priorityTheories ? { priorityTheories } : {}) } as unknown as steps.WorkflowInputs;
    const summary = steps.triageStep(setup, inputs, findingsPath, iteration, []);
    return { summary, order: (JSON.parse(readFileSync(summary.actionablePath, "utf8")) as Finding[]).map((item) => item.fingerprint) };
  };
  return { stateDir, triage };
}

describe("priority theories", () => {
  test("priority theories come first, each group in the usual order; without them the order is unchanged", () => {
    const findings = [
      finding("bv-crash", "bitvectors", 1, "crash"), finding("arrays-big", "arrays", 9), finding("ff-small", "finite-fields", 2),
      finding("ff-big", "finite-fields", 7), finding("uf-mid", "uf", 5),
    ];
    const { triage } = triageEnv(findings);
    const usual = triage().order;
    expect(usual).toEqual(["bv-crash", "arrays-big", "ff-big", "uf-mid", "ff-small"]);
    expect(triage([]).order).toEqual(usual);
    expect(triage(["finite-fields"], 2).order).toEqual(["ff-big", "ff-small", "bv-crash", "arrays-big", "uf-mid"]);
    expect(triage(["uf", "finite-fields"], 3).order).toEqual(["ff-big", "uf-mid", "ff-small", "bv-crash", "arrays-big"]);
  });

  test("policy-held, candidate and reserved findings stay excluded with their status unchanged", () => {
    const findings = [finding("ff-held", "finite-fields", 9), finding("ff-candidate", "finite-fields", 8), finding("ff-reserved", "finite-fields", 7), finding("ff-open", "finite-fields", 6), finding("arrays-open", "arrays", 5)];
    const { stateDir, triage } = triageEnv(findings, {
      state: (seen) => ({
        ...seen,
        findings: {
          ...seen.findings,
          "ff-held": { ...seen.findings["ff-held"]!, status: "provider_policy_blocked", providerBlock: { runKey: "r0", stage: "iter-1/finite-fields-repair/repair", error: "cyber_policy", at: "2026-10-26T10:00:00Z" } },
          "ff-candidate": { ...seen.findings["ff-candidate"]!, candidate: { runKey: "r0", branch: "fstar-proof-checking/work/r0/i1-finite-fields-repair", commit: "abc123" } },
        },
      }),
      // The reservation also names the held finding: the hold keeps precedence.
      activeWork: JSON.stringify([{ ...QFFF, fingerprints: ["ff-reserved", "ff-held"] }]),
    });
    const before = readFileSync(join(stateDir, "state.json"));
    const { summary, order } = triage(["finite-fields"]);
    expect(order).toEqual(["ff-open", "arrays-open"]);
    expect(summary.skipped).toEqual({ "provider-policy-blocked": 1, candidate: 1, "active-work fstar-qfff-priority-20261026": 1 });
    expect(readFileSync(join(stateDir, "state.json")).equals(before)).toBe(true);
    const state = readState(stateDir);
    expect([state.findings["ff-held"]?.status, state.findings["ff-candidate"]?.candidate?.commit, state.findings["ff-reserved"]?.status]).toEqual(["provider_policy_blocked", "abc123", "open"]);
  });
});

describe("active-work reservations", () => {
  const read = (text?: string) => {
    const stateDir = mkdtempSync(join(tmpdir(), "fpc-active-"));
    if (text !== undefined) writeFileSync(join(stateDir, "active-work.json"), text);
    return readActiveWork(stateDir);
  };

  test("a missing or empty file means no reservations; a valid file is read", () => {
    for (const text of [undefined, "", "  \n", "[]"]) expect(read(text)).toMatchObject({ ok: true, entries: [] });
    expect(read(JSON.stringify([QFFF]))).toMatchObject({ ok: true, entries: [QFFF] });
  });

  test("a malformed file is an error with the reason, never an empty list", () => {
    const cases: Array<[string, RegExp]> = [
      ["{not json", /JSON/],
      [JSON.stringify({ branch: "b" }), /expected a JSON array/],
      [JSON.stringify([{ ...QFFF, owner: undefined }]), /entry 0 needs a non-empty string "owner"/],
      [JSON.stringify([{ ...QFFF, createdAt: "yesterday" }]), /invalid createdAt/],
      [JSON.stringify([{ ...QFFF, theories: ["qf_ff"] }]), /unknown theories qf_ff/],
      [JSON.stringify([{ ...QFFF, fingerprints: "ff-reserved" }]), /"fingerprints" must be an array of strings/],
    ];
    for (const [text, reason] of cases) {
      const result = read(text);
      expect(result.ok).toBe(false);
      if (!result.ok) expect(result.error).toMatch(reason);
    }
  });

  test("repair and verify prompts list overlapping active work with the do-not-duplicate rule", () => {
    const arraysOnly: ActiveWork = { branch: "arrays-work", worktree: "C:/arrays", owner: "o", createdAt: "2026-10-26T15:00:00Z", theories: ["arrays"] };
    const runtime: ActiveWork = { branch: "runtime-work", worktree: "C:/runtime", owner: "o", createdAt: "2026-10-26T15:00:00Z", files: ["fstar/cherry_runtime/tests.cpp"] };
    const overlapping = activeWorkFor([QFFF, arraysOnly, runtime], "finite-fields");
    expect(overlapping.map((entry) => entry.branch)).toEqual(["fstar-qfff-priority-20261026", "runtime-work"]);
    const input = {
      sliceId: "finite-fields-repair", theory: "finite-fields", focus: "repair" as const, worktree: "W", branch: "B", baseRef: "0".repeat(40), cores: 4,
      findingsPath: "f.json", sliceDir: "D", toolchain, activeWork: overlapping,
    };
    for (const prompt of [prompts.repairPrompt(input), prompts.verifyPrompt({ ...input, reportPath: "r.md" })]) {
      expect(prompt).toContain("Active local work reserved in active-work.json that overlaps this slice (do not duplicate it; report the dependency):");
      expect(prompt).toContain("- branch fstar-qfff-priority-20261026 in worktree C:/z3atomic-qfff-priority (owner 60c9d927, since 2026-10-26T15:00:00Z): theories finite-fields; note: focused QF_FF run.");
      expect(prompt).toContain("- branch runtime-work in worktree C:/runtime (owner o, since 2026-10-26T15:00:00Z): files fstar/cherry_runtime/tests.cpp.");
      expect(prompt).toContain("if a finding depends on it, report the dependency (branch and worktree) instead of re-implementing it");
      expect(prompt).not.toContain("arrays-work");
    }
    expect(prompts.repairPrompt({ ...input, activeWork: [] })).not.toContain("Active local work");
  });
});

describe("launcher flags and reservations", () => {
  const cli = (...args: string[]) => {
    const result = spawnSync(process.execPath, [launcher, ...args], { encoding: "utf8" });
    return { code: result.status, stdout: result.stdout, stderr: result.stderr };
  };

  test("--priority-theories and --core-budget reach the launched run's inputs", () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-flags-"));
    const { code, stdout } = cli("--launch", "--dry-run", "--no-remote", "--state-dir", join(root, "state"), "--journal", join(root, "journal.sqlite"),
      "--build-log", buildLog, "--priority-theories", "finite-fields, arrays", "--core-budget", "8");
    const output = JSON.parse(stdout);
    expect(code).toBe(0);
    expect(output).toMatchObject({ launched: true, inputs: { priorityTheories: ["finite-fields", "arrays"], coreBudget: 8, dryRun: true } });
    const evidence = JSON.parse(readFileSync(output.result.evidence_path, "utf8"));
    expect(evidence.inputs).toMatchObject({ priorityTheories: ["finite-fields", "arrays"], coreBudget: 8 });
    expect(evidence.activeWork).toMatchObject({ entries: [] });
  }, 120_000);

  test("invalid flag values are rejected before anything runs", () => {
    const stateDir = join(mkdtempSync(join(tmpdir(), "fpc-flags-")), "state");
    const theory = cli("--check", "--no-remote", "--state-dir", stateDir, "--priority-theories", "qf_ff");
    expect(theory.code).toBe(1);
    expect(theory.stderr).toContain("--priority-theories takes theories from linear-arithmetic");
    const budget = cli("--check", "--no-remote", "--state-dir", stateDir, "--core-budget", "33");
    expect(budget.code).toBe(1);
    expect(budget.stderr).toContain("--core-budget must be an integer from 1 to 32, not 33");
    expect(existsSync(stateDir)).toBe(false);
  });

  test("a malformed active-work.json blocks the launch with exit 2 and changes nothing; --list-active-work shows the reason", () => {
    const stateDir = join(mkdtempSync(join(tmpdir(), "fpc-reserve-")), "state");
    mkdirSync(stateDir, { recursive: true });
    writeFileSync(join(stateDir, "active-work.json"), "[{\"branch\": \"fstar-qfff-priority-20261026\"");
    const launch = cli("--launch", "--dry-run", "--no-remote", "--state-dir", stateDir, "--build-log", buildLog);
    expect(launch.code).toBe(2);
    const output = JSON.parse(launch.stdout);
    expect(output.decision.retrigger).toBe(true);
    expect(output.launched).toBe(false);
    expect(output.blocked).toMatch(/^active-work\.json invalid: .+; fix or remove it$/);
    expect(existsSync(join(stateDir, "runs"))).toBe(false);
    expect(existsSync(join(stateDir, "state.json"))).toBe(false);
    const listed = cli("--list-active-work", "--state-dir", stateDir);
    expect(listed.code).toBe(2);
    expect(JSON.parse(listed.stdout).error).toMatch(/^active-work\.json invalid: /);
    writeFileSync(join(stateDir, "active-work.json"), JSON.stringify([QFFF]));
    const valid = cli("--list-active-work", "--state-dir", stateDir);
    expect(valid.code).toBe(0);
    expect(JSON.parse(valid.stdout).entries).toEqual([QFFF]);
  }, 120_000);
});

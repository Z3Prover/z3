/**
 * Local corpus scans run a prebuilt checker binary chosen by discovery, which can predate a merge.
 * Their evidence therefore dates from that binary's build time, not from the scan: a scan by a
 * checker built before a fix merged must not reopen the merged finding, and a scan by a checker of
 * unknown build time never counts as post-merge evidence. Each backend (OCaml, Cherry) uses its own
 * binary's time, in both scan modes (interactive z3test scripts and the batch harness).
 */
import { describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { CommandRunner } from "../lib/command.ts";
import type { Finding } from "../lib/reports.ts";
import { emptyState, readState, recordSeen, writeJsonAtomic } from "../lib/state.ts";
import * as steps from "../lib/steps.ts";

const signal = new AbortController().signal;
const DAY = 86_400_000;
const OCAML_BUILT = "2026-10-20T08:00:00.000Z";
const CHERRY_BUILT = "2026-10-22T09:30:00.000Z";

function setupFor(root: string, runKey: string, toolchain: Partial<steps.RunSetup["toolchain"]> = {}): steps.RunSetup {
  const stateDir = join(root, "state");
  const runDir = join(stateDir, "runs", runKey);
  mkdirSync(runDir, { recursive: true });
  return {
    repoRoot: root, stateDir, runKey, runDir, worktreeRoot: join(stateDir, "worktrees"), startedAt: "t",
    toolchain: {
      environment: { kind: "native", execArgv: [] }, python: "python3",
      ocamlChecker: "/opt/checker/checker", ocamlCheckerBuiltAt: OCAML_BUILT,
      cherryChecker: "/opt/checker/cherry/checker", cherryCheckerBuiltAt: CHERRY_BUILT,
      opam: true, opamSwitch: "fstar53", candidates: {}, available: true, missing: [], ...toolchain,
    },
  };
}

const inputsFor = (corpus: string) => ({
  pulseRunIds: [], pulseBranch: "", maxReports: 1, reportPaths: [], localCorpora: [corpus], localCaseLimit: 2, theories: [], coreBudget: 4, dryRun: false, repo: "Z3Prover/z3",
}) as unknown as steps.WorkflowInputs;

/** Every harness and checker invocation succeeds without findings. */
const quiet: CommandRunner = async (argv, options) => {
  const value = (flag: string) => argv[argv.indexOf(flag) + 1] as string;
  if (argv.includes("run") || argv.includes("diagnose") || argv.includes("report")) {
    if (argv.includes("--output")) {
      mkdirSync(value("--output"), { recursive: true });
      writeFileSync(join(value("--output"), "results.jsonl"), "");
    }
    return { code: 0, stdout: "", stderr: "" };
  }
  if (argv.includes("--interactive")) return { code: 0, stdout: "unsat\n", stderr: "" };
  throw new Error(`unexpected command ${argv.join(" ")} (${options.cwd ?? ""})`);
};

const partial = (examples: string[]): Finding => ({
  fingerprint: "f1", kind: "partial-rule", theory: "arrays", checker: "ocaml", rule: "rewrite", detail: "select-store",
  affectedProofs: examples.length, obligations: examples.length, soleFamilyProofs: examples.length, examples, evidence: [], sources: [],
});

describe("local scan evidence time", () => {
  test("each checker's scan records that checker's build time, in batch and interactive mode", async () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-scan-time-"));
    const batch = join(root, "bench", "inputs");
    const interactive = join(root, "z3test", "regressions", "smt2");
    for (const [dir, name] of [[join(batch, "QF_A"), "a1"], [interactive, "i1"]] as const) {
      mkdirSync(dir, { recursive: true });
      writeFileSync(join(dir, `${name}.smt2`), "(check-sat)\n");
    }
    for (const corpus of [batch, interactive]) {
      const source = await steps.sourceFindings(setupFor(root, `r-${corpus === batch ? "batch" : "interactive"}`), inputsFor(corpus), signal, quiet);
      const mode = corpus === batch ? "batch" : "interactive";
      expect(source.localScans[`local-scan:ocaml:${corpus}`]).toMatchObject({ mode, checkerBuiltAt: OCAML_BUILT });
      expect(source.localScans[`local-scan:cherry:${corpus}`]).toMatchObject({ mode, checkerBuiltAt: CHERRY_BUILT });
    }
  }, 60_000);

  test("a scan by a checker built before the merge keeps a merged finding; one built after the merge reopens it; an undated checker never does", async () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-scan-merge-"));
    const corpus = join(root, "bench", "inputs");
    const key = `local-scan:ocaml:${corpus}`;
    const mergedAt = new Date(Date.now() - 3 * DAY).toISOString();
    const before = partial(["QF_A/a1.smt2"]);
    const changed = { ...partial(["QF_A/a2.smt2", "QF_A/a3.smt2"]), sources: [key] };

    const seedMerged = (stateDir: string) => {
      const seen = recordSeen(emptyState(), [before], new Date(Date.now() - 5 * DAY));
      const record = seen.findings.f1;
      if (!record) throw new Error("seed failed");
      mkdirSync(stateDir, { recursive: true });
      writeJsonAtomic(join(stateDir, "state.json"), {
        ...seen,
        findings: { f1: { ...record, status: "merged", mergedAt, publishedOn: { branch: "fstar-proof-checking/1", prNumber: 7, prUrl: "u7", head: "abc", at: mergedAt } } },
      });
    };
    const scan = async (runKey: string, checkerBuiltAt: string | undefined) => {
      const setup = setupFor(root, runKey);
      seedMerged(setup.stateDir);
      const findingsPath = join(setup.runDir, "findings.json");
      writeFileSync(findingsPath, JSON.stringify([changed]));
      const source: steps.SourceSummary = {
        findingsPath, total: 1, byKind: {}, byTheory: {}, reports: [], carried: [], diagnostics: [],
        localScans: { [key]: { offset: 1, cases: 2, mode: "batch", ...(checkerBuiltAt ? { checkerBuiltAt } : {}) } },
      };
      await steps.recordSourcesStep(setup, inputsFor(corpus), source);
      return readState(setup.stateDir).findings.f1;
    };

    // The reviewers' probe: a pre-merge binary, scanned now, with a rotated window (changed examples).
    expect(await scan("pre-merge", new Date(Date.parse(mergedAt) - 2 * DAY).toISOString()))
      .toMatchObject({ status: "merged", keptReason: expect.stringMatching(/predates the merge/) });
    expect(await scan("undated", undefined))
      .toMatchObject({ status: "merged", keptReason: expect.stringMatching(/unknown build time/) });
    expect(await scan("post-merge", new Date(Date.parse(mergedAt) + DAY).toISOString()))
      .toMatchObject({ status: "open" });
  }, 60_000);
});

/**
 * Batch local corpora (C:/bench/inputs: one directory per logic) rotate across runs: every run
 * reaches every logic directory, later runs take the next files, and dry runs move nothing.
 * `run_checker_regressions.py` is emulated: it checks the sorted first `--max-cases` inputs below
 * `--corpus/--corpus-path`, exactly like its `discover`.
 */
import { describe, expect, test } from "bun:test";
import { lstatSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, relative } from "node:path";
import type { CommandRunner } from "../lib/command.ts";
import * as steps from "../lib/steps.ts";

const signal = new AbortController().signal;

function smt2Below(root: string): string[] {
  return readdirSync(root, { withFileTypes: true }).flatMap((entry) => {
    const path = join(root, entry.name);
    return entry.isDirectory() ? smt2Below(path) : entry.name.endsWith(".smt2") ? [path] : [];
  }).sort();
}

/** A fake harness that records which inputs each `run` checked (relative to the corpus root). */
function harness(checked: string[][], roots: string[] = []): CommandRunner {
  return async (argv) => {
    if (argv[0] === "gh") return { code: 0, stdout: "[]", stderr: "" };
    const value = (flag: string) => argv[argv.indexOf(flag) + 1] as string;
    if (argv[2] !== "run") return { code: 0, stdout: "", stderr: "" };
    const root = join(value("--corpus"), value("--corpus-path"));
    roots.push(root);
    const all = smt2Below(root);
    const max = Number(value("--max-cases"));
    const selected = max > 0 ? all.slice(0, max) : all;
    for (const file of selected) expect(lstatSync(file).isSymbolicLink()).toBe(false);
    checked.push(selected.map((file) => relative(root, file).replaceAll("\\", "/")));
    mkdirSync(value("--output"), { recursive: true });
    writeFileSync(join(value("--output"), "results.jsonl"), selected.map((file) => `${JSON.stringify({ path: relative(value("--corpus"), file).replaceAll("\\", "/"), outcome: "ACCEPT" })}\n`).join(""));
    return { code: 0, stdout: "", stderr: "" };
  };
}

describe("batch local corpus rotation", () => {
  test("every run reaches every logic directory, the next run takes the next files, and a dry run moves nothing", async () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-bench-"));
    const corpus = join(root, "bench", "inputs");
    const layout: Record<string, string[]> = { QF_A: ["a1", "a2", "a3"], QF_B: ["b1", "b2"], QF_C: ["nested/c1", "nested/c2"] };
    for (const [logic, names] of Object.entries(layout)) {
      for (const name of names) {
        mkdirSync(join(corpus, logic, name, ".."), { recursive: true });
        writeFileSync(join(corpus, logic, `${name}.smt2`), `; ${logic}/${name}\n(check-sat)\n`);
      }
    }
    const stateDir = join(root, "state");
    const setupFor = (runKey: string): steps.RunSetup => {
      const runDir = join(stateDir, "runs", runKey);
      mkdirSync(runDir, { recursive: true });
      return {
        repoRoot: root, stateDir, runKey, runDir, worktreeRoot: join(stateDir, "worktrees"), startedAt: "t",
        toolchain: { environment: { kind: "native", execArgv: [] }, python: "python3", ocamlChecker: "/opt/checker/checker", opam: true, opamSwitch: "fstar53", candidates: {}, available: true, missing: [] },
      };
    };
    const inputs = {
      pulseRunIds: [], pulseBranch: "", maxReports: 1, reportPaths: [], localCorpora: [corpus], localCaseLimit: 3, theories: [], coreBudget: 4, dryRun: false, repo: "Z3Prover/z3",
    } as unknown as steps.WorkflowInputs;

    const checked: string[][] = [];
    const roots: string[] = [];
    for (const runKey of ["r1", "r2"]) {
      const setup = setupFor(runKey);
      const source = await steps.sourceFindings(setup, inputs, signal, harness(checked, roots));
      await steps.recordSourcesStep(setup, inputs, source);
    }
    const [first, second] = checked;
    const logics = (files: string[] | undefined) => [...new Set((files ?? []).map((file) => file.split("/")[0]))].sort();
    expect(logics(first)).toEqual(["QF_A", "QF_B", "QF_C"]);
    expect(logics(second)).toEqual(["QF_A", "QF_B", "QF_C"]);
    expect(first).toHaveLength(3);
    expect(second).toHaveLength(3);
    expect((second ?? []).filter((file) => (first ?? []).includes(file))).toEqual([]);

    // The checked inputs are copies staged below each run directory, not the user's corpus.
    expect(roots.map((path) => relative(stateDir, path).replaceAll("\\", "/").split("/").slice(0, 2).join("/"))).toEqual(["runs/r1", "runs/r2"]);

    // A dry run executes nothing and leaves the recorded scan positions byte-identical.
    const before = readFileSync(join(stateDir, "state.json"));
    const dry = { ...inputs, dryRun: true } as steps.WorkflowInputs;
    const setup = setupFor("r3-dry");
    const source = await steps.sourceFindings(setup, dry, signal, harness(checked));
    const recorded = await steps.recordSourcesStep(setup, dry, source);
    expect(checked).toHaveLength(2);
    expect(recorded.committed).toBe(false);
    expect(readFileSync(join(stateDir, "state.json")).equals(before)).toBe(true);
  }, 120_000);
});

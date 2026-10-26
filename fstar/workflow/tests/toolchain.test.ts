/**
 * Toolchain discovery on a Windows host: the checker toolchain lives in a WSL distribution (not
 * necessarily the default one), with a custom OPAMROOT and Linux F*, Cherry and checker paths.
 */
import { describe, expect, test } from "bun:test";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnRunner, type CommandResult, type CommandRunner } from "../lib/command.ts";
import * as steps from "../lib/steps.ts";
import { buildCommand, probeToolchain, toEnvironmentPath } from "../lib/toolchain.ts";

const R = "/root/.local/share/z3-clause-proofs-4d52bf5f";
const utf16 = (text: string) => [...text].map((char) => `${char}\u0000`).join("");
const ok = (stdout = ""): CommandResult => ({ code: 0, stdout, stderr: "" });
const discovered = [
  `fstar\t${R}/fstar-ci-v2026.09.27/bin/fstar.exe\tF* 2026.09.27`,
  `cherry-fstar\t${R}/fstar-nightly-2026.10.23/bin/fstar.exe\tF* nightly-2026-10-23`,
  `opam\t${R}/opam\t5.3.0`,
  "pwsh\t/mnt/c/tools/linux-pwsh-7.5.4/pwsh\t7.5.4",
  "python\t/usr/bin/python3\tPython 3.14.4",
  `ocaml-checker\t${R}/published-checkers/pulse-checker-ocaml-linux-x86_64/checker\t1792797588`,
  `ocaml-checker\t${R}/ci-fixed-checker/checker\t1792834493`,
  `cherry-checker\t${R}/ci-fixed-checker/cherry/checker\t1792834636`,
].join("\n");

/** A Windows host whose default WSL distribution (docker-desktop) has no bash; Ubuntu has the toolchain. */
function windowsHost(calls: Array<{ argv: readonly string[]; input?: string }>, output = discovered): CommandRunner {
  return async (argv, options) => {
    calls.push({ argv, input: options.input });
    const command = argv.join(" ");
    if (command === "wsl --list --quiet") return ok(`\ufeff${utf16("docker-desktop\r\nUbuntu\r\n")}`);
    if (command === "wsl -d docker-desktop -e bash -c echo ok") return { code: 1, stdout: "", stderr: "execvpe(bash) failed: No such file or directory" };
    if (command === "wsl -d Ubuntu -e bash -c echo ok") return ok("ok\n");
    if (command === "wsl -d Ubuntu -e bash -s") return ok(`${output}\n`);
    return { code: 1, stdout: "", stderr: "", error: `not found: ${argv[0]}` };
  };
}

describe("toolchain discovery", () => {
  test("finds the WSL Ubuntu toolchain with a custom OPAMROOT, Linux F*, Cherry and checker builds", async () => {
    const calls: Array<{ argv: readonly string[]; input?: string }> = [];
    const report = await probeToolchain(windowsHost(calls), { platform: "win32" });
    expect(report).toMatchObject({
      environment: { kind: "wsl", distro: "Ubuntu", execArgv: ["wsl", "-d", "Ubuntu", "-e"] },
      fstar: `${R}/fstar-ci-v2026.09.27/bin/fstar.exe`,
      cherryFstar: `${R}/fstar-nightly-2026.10.23/bin/fstar.exe`,
      opam: true,
      opamRoot: `${R}/opam`,
      opamSwitch: "fstar53",
      ocamlVersion: "5.3.0",
      pwsh: "/mnt/c/tools/linux-pwsh-7.5.4/pwsh",
      // The most recently built checker wins over older published ones.
      ocamlChecker: `${R}/ci-fixed-checker/checker`,
      cherryChecker: `${R}/ci-fixed-checker/cherry/checker`,
      available: true,
      missing: [],
    });
    // The discovery script searches the known layouts and the custom opam roots for the requested switch.
    const script = calls.find((call) => call.input !== undefined)?.input ?? "";
    expect(script).toContain("z3-clause-proofs-*/opam");
    expect(script).toContain("SWITCH='fstar53'");
  });

  test("explicit inputs select the distribution and are passed to discovery", async () => {
    const calls: Array<{ argv: readonly string[]; input?: string }> = [];
    await probeToolchain(windowsHost(calls), { platform: "win32", wslDistro: "Ubuntu", opamRoot: "/opt/opam", ocamlChecker: "/srv/checker" });
    expect(calls.map((call) => call.argv.join(" "))).not.toContain("wsl --list --quiet");
    const script = calls.find((call) => call.input !== undefined)?.input ?? "";
    expect(script).toContain("OPAMROOT_OVERRIDE='/opt/opam'");
    expect(script).toContain("OCAML_CHECKER_OVERRIDE='/srv/checker'");
  });

  test("a missing PowerShell keeps the toolchain unavailable and names the input that fixes it", async () => {
    const report = await probeToolchain(windowsHost([], discovered.split("\n").filter((line) => !line.startsWith("pwsh")).join("\n")), { platform: "win32" });
    expect(report.available).toBe(false);
    expect(report.missing.join(" ")).toMatch(/PowerShell 7 \(pwsh\) in WSL Ubuntu.*pwshExe/);
  });

  test("a PowerShell that is found but crashes is reported as failing to run, with its error, not as missing", async () => {
    const crash = "Unhandled exception. System.IO.FileLoadException: The given assembly name was invalid.";
    const calls: Array<{ argv: readonly string[]; input?: string }> = [];
    const output = discovered.replace("pwsh\t/mnt/c/tools/linux-pwsh-7.5.4/pwsh\t7.5.4", `pwsh-failed\t/mnt/c/tools/linux-pwsh-7.5.4/pwsh\t${crash}`);
    const report = await probeToolchain(windowsHost(calls, output), { platform: "win32" });
    expect(report.available).toBe(false);
    const reason = report.missing.join(" ");
    expect(reason).toContain("/mnt/c/tools/linux-pwsh-7.5.4/pwsh");
    expect(reason).toMatch(/failed to run/);
    expect(reason).toContain("FileLoadException: The given assembly name was invalid");
    expect(reason).not.toMatch(/^PowerShell 7 \(pwsh\) in WSL Ubuntu for/);
    // The probe runs each candidate with an isolated cache and keeps its error output.
    const script = calls.find((call) => call.input !== undefined)?.input ?? "";
    const probe = script.split("\n").find((line) => line.includes("PSVersionTable")) ?? "";
    expect(probe).toContain("XDG_CACHE_HOME=");
    expect(probe).toContain("2>&1");
    expect(probe).toContain("pwsh-failed");
  });

  test("every build command runs PowerShell with its own cache directory", async () => {
    const report = await probeToolchain(windowsHost([]), { platform: "win32" });
    const one = buildCommand(report, { worktree: "C:\\wt\\slice-a", buildKey: "run-i1-arrays", cores: 4 });
    const two = buildCommand(report, { worktree: "C:\\wt\\slice-b", buildKey: "run-i1-bv", cores: 4 });
    const cache = (command: string) => /XDG_CACHE_HOME=("?)([^ "]+)\1/.exec(command)?.[2];
    expect(cache(one)).toContain("run-i1-arrays");
    expect(cache(two)).toContain("run-i1-bv");
    expect(one).toMatch(/DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1 XDG_CACHE_HOME=\S+ \S*\/mnt\/c\/tools\/linux-pwsh-7\.5\.4\/pwsh/);
  });

  // Opt-in: probes the host's real WSL toolchain (FSTAR_WORKFLOW_REAL_TOOLCHAIN=1); skipped by default so the suite stays hermetic.
  test.skipIf(process.env.FSTAR_WORKFLOW_REAL_TOOLCHAIN !== "1")("the real host toolchain is discovered", async () => {
    const report = await probeToolchain(spawnRunner, {});
    expect(report.missing).toEqual([]);
    expect(report.available).toBe(true);
  }, 600_000);

  test("local corpora run through the WSL checker with the scripts passed on stdin", async () => {
    const root = mkdtempSync(join(tmpdir(), "fpc-tc-"));
    const corpus = join(root, "regressions", "smt2");
    mkdirSync(corpus, { recursive: true });
    writeFileSync(join(corpus, "a.smt2"), "(assert false)\n(check-sat)\n");
    const runDir = join(root, "run");
    mkdirSync(runDir);
    const report = await probeToolchain(windowsHost([]), { platform: "win32" });
    const setup: steps.RunSetup = { repoRoot: root, stateDir: join(root, "state"), runKey: "k", runDir, worktreeRoot: join(root, "wt"), startedAt: "t", toolchain: report };
    const calls: Array<readonly string[]> = [];
    const runner: CommandRunner = async (argv) => {
      calls.push(argv);
      if (argv[0] === "gh") return ok("[]");
      return { code: 3, stdout: "; proof-check PARTIAL 1\n", stderr: "obligation\trewrite\t1\t0\tabc\n" };
    };
    const inputs = { pulseRunIds: [], pulseBranch: "", maxReports: 1, reportPaths: [], localCorpora: [corpus], localCaseLimit: 5, coreBudget: 4, dryRun: false, repo: "Z3Prover/z3" } as unknown as steps.WorkflowInputs;
    const source = await steps.sourceFindings(setup, inputs, new AbortController().signal, runner);
    const checkerCalls = calls.filter((argv) => argv[0] !== "gh");
    expect(checkerCalls.map((argv) => argv.slice(0, 5))).toEqual([
      ["wsl", "-d", "Ubuntu", "-e", `${R}/ci-fixed-checker/checker`],
      ["wsl", "-d", "Ubuntu", "-e", `${R}/ci-fixed-checker/cherry/checker`],
    ]);
    expect(source.byKind).toMatchObject({ "partial-rule": 1 });
  });

  test("host paths translate into the WSL mount", () => {
    expect(toEnvironmentPath({ kind: "wsl", distro: "Ubuntu", execArgv: [] }, "C:\\z3atomic\\fstar\\tools\\x.py")).toBe("/mnt/c/z3atomic/fstar/tools/x.py");
    expect(toEnvironmentPath({ kind: "native", execArgv: [] }, "/home/x")).toBe("/home/x");
  });
});

/**
 * Toolchain preflight. Proof checking needs F*, PowerShell for `build_ocaml_checker.ps1`, and
 * OCaml through opam (inside WSL on Windows hosts); Cherry is optional. Nothing is reported as
 * available unless the executable actually ran.
 */
import { existsSync } from "node:fs";
import type { CommandRunner } from "./command.js";

export type ToolchainReport = {
  readonly fstar?: string;
  readonly cherryFstar?: string;
  readonly pwsh: boolean;
  readonly python?: string;
  readonly opam: boolean;
  readonly ocamlChecker?: string;
  readonly cherryChecker?: string;
  /** True when F*, PowerShell and opam/OCaml all ran, so proofs can actually be checked. */
  readonly available: boolean;
  readonly missing: string[];
};

export interface ToolchainOptions {
  readonly fstarExe?: string;
  readonly cherryFstarExe?: string;
  readonly ocamlChecker?: string;
  readonly cherryChecker?: string;
  readonly signal?: AbortSignal;
}

/** The pinned F* release named by the repository's build documentation. */
export const PINNED_FSTAR = "v2026.09.27";

export async function probeToolchain(runner: CommandRunner, options: ToolchainOptions): Promise<ToolchainReport> {
  const run = (argv: string[]) => runner(argv, { timeoutMs: 60_000, signal: options.signal });
  const missing: string[] = [];
  const fstarCandidates = [options.fstarExe, process.env.FSTAR_EXE, "fstar.exe", "C:\\fstar\\fstar\\bin\\fstar.exe"]
    .filter((item): item is string => Boolean(item));
  let fstar: string | undefined;
  for (const candidate of fstarCandidates) {
    const result = await run([candidate, "--version"]);
    if (result.code === 0) {
      fstar = candidate;
      break;
    }
  }
  if (!fstar) missing.push(`F* ${PINNED_FSTAR}: set the fstarExe input or FSTAR_EXE, or put fstar.exe on PATH`);
  const cherryCandidate = options.cherryFstarExe ?? process.env.CHERRY_FSTAR_EXE;
  const cherryFstar = cherryCandidate && (await run([cherryCandidate, "--version"])).code === 0 ? cherryCandidate : undefined;
  const pwsh = (await run(["pwsh", "-NoProfile", "-Command", "$PSVersionTable.PSVersion.ToString()"])).code === 0;
  if (!pwsh) missing.push("PowerShell 7 (pwsh) for fstar/tools/build_ocaml_checker.ps1");
  const opamProbe = process.platform === "win32"
    ? ["wsl", "-e", "bash", "-lc", "opam --version && opam switch list --short | grep -qx fstar53"]
    : ["bash", "-lc", "opam --version && opam switch list --short | grep -qx fstar53"];
  const opam = (await run(opamProbe)).code === 0;
  if (!opam) missing.push(`OCaml 5.3 via opam switch fstar53${process.platform === "win32" ? " inside WSL" : ""}`);
  let python: string | undefined;
  for (const candidate of ["python3", "python"]) {
    if ((await run([candidate, "--version"])).code === 0) {
      python = candidate;
      break;
    }
  }
  if (!python) missing.push("Python 3 for fstar/tools/run_checker_regressions.py");
  const checker = (path: string | undefined) => (path && existsSync(path) ? path : undefined);
  return {
    fstar,
    cherryFstar,
    pwsh,
    python,
    opam,
    ocamlChecker: checker(options.ocamlChecker ?? process.env.Z3_FSTAR_CHECKER),
    cherryChecker: checker(options.cherryChecker ?? process.env.Z3_FSTAR_CHERRY_CHECKER),
    available: Boolean(fstar) && pwsh && opam,
    missing,
  };
}

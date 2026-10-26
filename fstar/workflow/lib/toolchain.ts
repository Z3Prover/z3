/**
 * Toolchain discovery. The checker builds and runs on Linux: directly on a Linux host, and inside
 * a WSL distribution on Windows hosts (the pipeline of `fstar/tools/build_ocaml_checker.ps1` and
 * `.github/workflows/pulse-checker-build.yml`). Discovery therefore selects a build environment
 * first (a WSL distribution that has bash), then probes it for the pinned F*, a Cherry-capable F*,
 * an opam root with the OCaml 5.3 switch, a Linux PowerShell for the build script, Python 3, and
 * already built OCaml/Cherry checker executables. Explicit inputs win; otherwise the known install
 * layouts are searched. Nothing is reported as available unless the executable actually ran.
 */
import type { CommandRunner } from "./command.js";

/** Where Linux toolchain commands run. */
export type BuildEnvironment = {
  readonly kind: "wsl" | "native";
  readonly distro?: string;
  /** argv prefix that runs one executable in the environment (empty on a Linux host). */
  readonly execArgv: readonly string[];
};

export type ToolchainReport = {
  readonly environment?: BuildEnvironment;
  /** Paths below are paths inside the build environment. */
  readonly fstar?: string;
  readonly fstarVersion?: string;
  readonly cherryFstar?: string;
  readonly cherryFstarVersion?: string;
  readonly opam: boolean;
  readonly opamRoot?: string;
  readonly opamSwitch: string;
  readonly ocamlVersion?: string;
  /** Linux PowerShell that runs `build_ocaml_checker.ps1` inside the environment. */
  readonly pwsh?: string;
  readonly python?: string;
  readonly ocamlChecker?: string;
  readonly cherryChecker?: string;
  /** Build (modification) time of the chosen checker executables: the time their scans' evidence dates from. */
  readonly ocamlCheckerBuiltAt?: string;
  readonly cherryCheckerBuiltAt?: string;
  /** Every candidate that discovery examined, with its version or modification time. */
  readonly candidates: Readonly<Record<string, readonly string[]>>;
  /** True when F*, the opam switch and PowerShell all ran, so the checker can be built and proofs checked. */
  readonly available: boolean;
  readonly missing: string[];
};

export interface ToolchainOptions {
  /** WSL distribution (Windows hosts); default `Z3_FSTAR_WSL_DISTRO`, else the first distribution with bash, Ubuntu first. */
  readonly wslDistro?: string;
  readonly fstarExe?: string;
  readonly cherryFstarExe?: string;
  readonly opamRoot?: string;
  readonly opamSwitch?: string;
  readonly pwshExe?: string;
  readonly ocamlChecker?: string;
  readonly cherryChecker?: string;
  readonly signal?: AbortSignal;
  /** Host platform; tests override it. */
  readonly platform?: NodeJS.Platform;
}

/** The pinned F* release named by the repository's build documentation and CI. */
export const PINNED_FSTAR = "v2026.09.27";
export const DEFAULT_OPAM_SWITCH = "fstar53";

/** Translate a host path into the build environment (`C:\x\y` → `/mnt/c/x/y` under WSL). */
export function toEnvironmentPath(environment: BuildEnvironment | undefined, path: string): string {
  if (environment?.kind !== "wsl") return path;
  const drive = /^([A-Za-z]):[\\/](.*)$/.exec(path);
  return drive?.[1] !== undefined ? `/mnt/${drive[1].toLowerCase()}/${(drive[2] ?? "").replaceAll("\\", "/")}` : path.replaceAll("\\", "/");
}

const quote = (value: string) => `'${value.replaceAll("'", `'\\''`)}'`;

/** Bash script that lists candidates as `kind<TAB>path<TAB>detail` lines. */
export function discoveryScript(options: ToolchainOptions): string {
  const opamSwitch = options.opamSwitch || DEFAULT_OPAM_SWITCH;
  return [
    "shopt -s nullglob",
    `FSTAR_OVERRIDE=${quote(options.fstarExe ?? "")}`,
    `CHERRY_OVERRIDE=${quote(options.cherryFstarExe ?? "")}`,
    `OPAMROOT_OVERRIDE=${quote(options.opamRoot ?? "")}`,
    `PWSH_OVERRIDE=${quote(options.pwshExe ?? "")}`,
    `OCAML_CHECKER_OVERRIDE=${quote(options.ocamlChecker ?? "")}`,
    `CHERRY_CHECKER_OVERRIDE=${quote(options.cherryChecker ?? "")}`,
    `SWITCH=${quote(opamSwitch)}`,
    "emit() { printf '%s\\t%s\\t%s\\n' \"$1\" \"$2\" \"$3\"; }",
    "version() { timeout 60 \"$1\" --version 2>/dev/null | head -n1 | tr -d '\\r'; }",
    "list() { local seen=; for item in \"$@\"; do [ -n \"$item\" ] || continue; case \" $seen \" in *\" $item \"*) continue;; esac; seen=\"$seen $item\"; printf '%s\\n' \"$item\"; done; }",
    "L=\"$HOME/.local/share\"; C=\"$HOME/.cache\"",
    "if [ -n \"$FSTAR_OVERRIDE\" ]; then fstars=(\"$FSTAR_OVERRIDE\"); else fstars=($(command -v fstar.exe) \"$L\"/z3-clause-proofs-*/fstar-ci-v*/bin/fstar.exe \"$C\"/z3-pulse-*/fstar/bin/fstar.exe /opt/fstar/bin/fstar.exe); fi",
    "while read -r f; do [ -x \"$f\" ] && emit fstar \"$f\" \"$(version \"$f\")\"; done < <(list \"${fstars[@]}\")",
    "if [ -n \"$CHERRY_OVERRIDE\" ]; then cherries=(\"$CHERRY_OVERRIDE\"); else cherries=(\"$L\"/z3-clause-proofs-*/fstar-nightly-*/bin/fstar.exe \"$C\"/z3-pulse-*/fstar-nightly*/bin/fstar.exe); fi",
    "while read -r f; do [ -x \"$f\" ] && emit cherry-fstar \"$f\" \"$(version \"$f\")\"; done < <(list \"${cherries[@]}\")",
    "if [ -n \"$OPAMROOT_OVERRIDE\" ]; then roots=(\"$OPAMROOT_OVERRIDE\"); else roots=(\"${OPAMROOT:-$HOME/.opam}\" \"$L\"/z3-clause-proofs-*/opam \"$C\"/z3-pulse-*/opam); fi",
    "if command -v opam >/dev/null; then while read -r r; do [ -d \"$r\" ] || continue; OPAMROOT=\"$r\" opam switch list --short 2>/dev/null | grep -qx \"$SWITCH\" || continue; emit opam \"$r\" \"$(OPAMROOT=\"$r\" timeout 120 opam exec --switch=\"$SWITCH\" -- ocamlc -version 2>/dev/null | tr -d '\\r')\"; done < <(list \"${roots[@]}\"); fi",
    "if [ -n \"$PWSH_OVERRIDE\" ]; then pwshes=(\"$PWSH_OVERRIDE\"); else pwshes=($(command -v pwsh) /opt/microsoft/powershell/7/pwsh \"$HOME\"/.dotnet/tools/pwsh /mnt/c/Users/*/.copilot/session-state/*/files/linux-pwsh-*/pwsh); fi",
    // Probe each PowerShell with a private cache (a corrupted ~/.cache/powershell crashes it) and keep its error output.
    "PWSH_CACHE=$(mktemp -d)",
    "while read -r p; do [ -x \"$p\" ] || continue; out=$(DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1 XDG_CACHE_HOME=\"$PWSH_CACHE\" timeout 60 \"$p\" -NoProfile -Command '$PSVersionTable.PSVersion.ToString()' 2>&1 | tr -d '\\r'); v=$(printf '%s\\n' \"$out\" | head -n1); if printf '%s' \"$v\" | grep -Eq '^[0-9]+\\.[0-9]+'; then emit pwsh \"$p\" \"$v\"; else emit pwsh-failed \"$p\" \"$(printf '%s' \"$out\" | tr '\\t\\n' '  ' | cut -c1-300)\"; fi; done < <(list \"${pwshes[@]}\")",
    "rm -rf \"$PWSH_CACHE\"",
    "p=$(command -v python3) && emit python \"$p\" \"$(\"$p\" --version 2>&1)\"",
    "if [ -n \"$OCAML_CHECKER_OVERRIDE\" ]; then ocamls=(\"$OCAML_CHECKER_OVERRIDE\"); else ocamls=(\"$L\"/z3-clause-proofs-*/ci-fixed-checker/checker \"$L\"/z3-clause-proofs-*/published-checkers/pulse-checker-ocaml-linux-x86_64/checker \"$L\"/z3-clause-proofs-*/checker/checker \"$C\"/z3-pulse-*/checker/checker \"$HOME\"/z3checker/checker); fi",
    "while read -r f; do [ -f \"$f\" ] && [ -x \"$f\" ] && emit ocaml-checker \"$f\" \"$(stat -c %Y \"$f\")\"; done < <(list \"${ocamls[@]}\")",
    "if [ -n \"$CHERRY_CHECKER_OVERRIDE\" ]; then cherrycs=(\"$CHERRY_CHECKER_OVERRIDE\"); else cherrycs=(\"$L\"/z3-clause-proofs-*/ci-fixed-checker/cherry/checker \"$L\"/z3-clause-proofs-*/published-checkers/pulse-checker-cherry-linux-x86_64/checker \"$L\"/z3-clause-proofs-*/cherry-checker/checker \"$HOME\"/z3checker/cherry/checker); fi",
    "while read -r f; do [ -f \"$f\" ] && [ -x \"$f\" ] && emit cherry-checker \"$f\" \"$(stat -c %Y \"$f\")\"; done < <(list \"${cherrycs[@]}\")",
    "exit 0",
    "",
  ].join("\n");
}

type Candidate = { readonly kind: string; readonly path: string; readonly detail: string };

export function parseDiscovery(stdout: string): Candidate[] {
  return stdout.split(/\r?\n/).flatMap((line) => {
    const [kind, path, detail] = line.split("\t");
    return kind && path ? [{ kind, path, detail: detail ?? "" }] : [];
  });
}

/** `wsl --list --quiet` prints UTF-16; strip NULs and BOMs. */
export function parseDistributions(stdout: string): string[] {
  return stdout.replace(/[\u0000\ufeff]/g, "").split(/\r?\n/).map((name) => name.trim()).filter(Boolean);
}

async function selectEnvironment(run: (argv: string[], input?: string) => ReturnType<CommandRunner>, options: ToolchainOptions, missing: string[]): Promise<BuildEnvironment | undefined> {
  if ((options.platform ?? process.platform) !== "win32") return { kind: "native", execArgv: [] };
  const requested = options.wslDistro || process.env.Z3_FSTAR_WSL_DISTRO;
  let distros: string[];
  if (requested) distros = [requested];
  else {
    const listed = parseDistributions((await run(["wsl", "--list", "--quiet"])).stdout);
    // Prefer Ubuntu (the distribution the build documentation uses); Docker's utility distributions have no bash.
    distros = [...listed.filter((name) => /^ubuntu/i.test(name)), ...listed.filter((name) => !/^ubuntu/i.test(name) && !/^docker-desktop/i.test(name))];
  }
  for (const distro of distros) {
    if ((await run(["wsl", "-d", distro, "-e", "bash", "-c", "echo ok"])).stdout.trim() === "ok") return { kind: "wsl", distro, execArgv: ["wsl", "-d", distro, "-e"] };
  }
  missing.push(requested
    ? `WSL distribution ${requested} with bash (from the wslDistro input or Z3_FSTAR_WSL_DISTRO)`
    : "a WSL distribution with bash (install Ubuntu, or set the wslDistro input or Z3_FSTAR_WSL_DISTRO)");
  return undefined;
}

export async function probeToolchain(runner: CommandRunner, options: ToolchainOptions): Promise<ToolchainReport> {
  const run = (argv: string[], input?: string) => runner(argv, { timeoutMs: 5 * 60_000, signal: options.signal, ...(input === undefined ? {} : { input }) });
  const missing: string[] = [];
  const opamSwitch = options.opamSwitch || DEFAULT_OPAM_SWITCH;
  const environment = await selectEnvironment(run, options, missing);
  if (!environment) return { opam: false, opamSwitch, candidates: {}, available: false, missing };
  const discovery = await run([...environment.execArgv, "bash", "-s"], discoveryScript({
    ...options,
    fstarExe: options.fstarExe || process.env.FSTAR_EXE,
    cherryFstarExe: options.cherryFstarExe || process.env.CHERRY_FSTAR_EXE,
    opamRoot: options.opamRoot || process.env.Z3_FSTAR_OPAMROOT,
    pwshExe: options.pwshExe || process.env.Z3_FSTAR_PWSH,
    ocamlChecker: options.ocamlChecker || process.env.Z3_FSTAR_CHECKER,
    cherryChecker: options.cherryChecker || process.env.Z3_FSTAR_CHERRY_CHECKER,
  }));
  const found = parseDiscovery(discovery.stdout);
  const candidates: Record<string, string[]> = {};
  for (const item of found) (candidates[item.kind] ??= []).push(item.detail ? `${item.path} (${item.detail})` : item.path);
  const of = (kind: string) => found.filter((item) => item.kind === kind);
  const pinned = PINNED_FSTAR.replace(/^v/, "");
  const fstar = of("fstar").find((item) => item.detail.includes(pinned)) ?? of("fstar").find((item) => item.detail.startsWith("F*"));
  const cherry = of("cherry-fstar").find((item) => item.detail.startsWith("F*"));
  const opam = of("opam").find((item) => item.detail.startsWith("5.3"));
  const pwsh = of("pwsh").find((item) => /^\d+\.\d+/.test(item.detail));
  const python = of("python").find((item) => item.detail.startsWith("Python 3"));
  // The most recently built checker executable is the best match for the current sources.
  const newest = (kind: string) => [...of(kind)].sort((left, right) => Number(right.detail) - Number(left.detail))[0];
  const builtAt = (kind: string) => {
    const seconds = Number(newest(kind)?.detail);
    return newest(kind)?.detail && Number.isFinite(seconds) ? new Date(seconds * 1000).toISOString() : undefined;
  };
  const where = environment.kind === "wsl" ? ` in WSL ${environment.distro}` : "";
  if (!fstar) missing.push(`F* ${PINNED_FSTAR}${where}: set the fstarExe input or FSTAR_EXE`);
  if (!opam) missing.push(`OCaml 5.3 via opam switch ${opamSwitch}${where}: set the opamRoot input or Z3_FSTAR_OPAMROOT`);
  if (!pwsh) {
    const failed = of("pwsh-failed");
    missing.push(failed.length > 0
      ? `PowerShell 7${where} found but failed to run (probed with a private XDG_CACHE_HOME and DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1): ${failed.map((item) => `${item.path}: ${item.detail || "no output"}`).join("; ")}. Repair or reinstall it, or set the pwshExe input or Z3_FSTAR_PWSH to a working PowerShell 7`
      : `PowerShell 7 (pwsh)${where} for fstar/tools/build_ocaml_checker.ps1: set the pwshExe input or Z3_FSTAR_PWSH`);
  }
  if (!python) missing.push(`Python 3${where} for fstar/tools/run_checker_regressions.py`);
  return {
    environment,
    fstar: fstar?.path,
    fstarVersion: fstar?.detail,
    cherryFstar: cherry?.path,
    cherryFstarVersion: cherry?.detail,
    opam: opam !== undefined,
    opamRoot: opam?.path,
    opamSwitch,
    ocamlVersion: opam?.detail,
    pwsh: pwsh?.path,
    python: python?.path,
    ocamlChecker: newest("ocaml-checker")?.path,
    cherryChecker: newest("cherry-checker")?.path,
    ocamlCheckerBuiltAt: builtAt("ocaml-checker"),
    cherryCheckerBuiltAt: builtAt("cherry-checker"),
    candidates,
    available: fstar !== undefined && opam !== undefined && pwsh !== undefined,
    missing,
  };
}

/** Shell prologue that selects the discovered opam switch. */
export function opamPrologue(toolchain: ToolchainReport): string {
  const root = toolchain.opamRoot ? `export OPAMROOT=${quote(toolchain.opamRoot)} && ` : "";
  return `${root}eval "$(opam env --switch=${toolchain.opamSwitch} --set-switch)"`;
}

/**
 * Exact command that builds and tests the checker from a worktree with private build directories.
 * PowerShell gets a private XDG_CACHE_HOME per build key, so concurrent slice builds never share
 * (or corrupt) its startup cache.
 */
export function buildCommand(toolchain: ToolchainReport, input: { readonly worktree: string; readonly buildKey: string; readonly cores: number }): string {
  const tree = toEnvironmentPath(toolchain.environment, input.worktree);
  const out = `$HOME/.cache/fstar-proof-checking/${input.buildKey}`;
  const script = [
    `cd ${quote(tree)}`,
    opamPrologue(toolchain),
    `mkdir -p "${out}/xdg-cache"`,
    [
      // Portable Linux PowerShell builds abort without ICU unless globalization is invariant.
      `DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1 XDG_CACHE_HOME="${out}/xdg-cache" ${quote(toolchain.pwsh ?? "pwsh")} -NoProfile -File fstar/tools/build_ocaml_checker.ps1`,
      `-FstarExe ${quote(toolchain.fstar ?? "fstar.exe")} -OpamSwitch ${toolchain.opamSwitch}`,
      `-Z3WindowsBuildDir "${out}/z3" -Z3BuildDir "${out}/z3-ocaml" -CacheDir "${out}/cache" -WslBuildDir "${out}/checker"`,
      `-BuildJobs ${input.cores} -RunTests`,
      ...(toolchain.cherryFstar ? [`-BuildCherry -CherryFstarExe ${quote(toolchain.cherryFstar)}`] : []),
    ].join(" "),
  ].join(" && ");
  return wrapInEnvironment(toolchain, script);
}

/** Wrap a bash command line so it runs in the build environment from a Windows or Linux host. */
export function wrapInEnvironment(toolchain: ToolchainReport, script: string): string {
  return toolchain.environment?.kind === "wsl"
    ? `wsl -d ${toolchain.environment.distro} -e bash -lc ${quote(script)}`
    : `bash -lc ${quote(script)}`;
}

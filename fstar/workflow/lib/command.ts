/**
 * Injectable external-command runner. Every external command issued by the workflow goes through
 * a runner so tests can substitute a fake and assert which commands (especially remote
 * mutations) were issued, and so each command has a finite timeout and honors cancellation.
 */
import { spawn } from "node:child_process";

export interface CommandResult {
  readonly code: number | null;
  readonly stdout: string;
  readonly stderr: string;
  /** Set when the process could not start (missing executable) or was killed. */
  readonly error?: string;
}

export interface CommandOptions {
  readonly cwd?: string;
  readonly timeoutMs: number;
  readonly signal?: AbortSignal;
  readonly input?: string;
  readonly env?: Readonly<Record<string, string>>;
}

export type CommandRunner = (argv: readonly string[], options: CommandOptions) => Promise<CommandResult>;

export interface CommandLogEntry {
  readonly argv: readonly string[];
  readonly cwd?: string;
  readonly code: number | null;
  readonly mutating: boolean;
}

const OUTPUT_LIMIT = 8 * 1024 * 1024;

/** Run a process with a deadline; never throws for non-zero exits or missing executables. */
export const spawnRunner: CommandRunner = (argv, options) =>
  new Promise((resolve) => {
    const [command, ...args] = argv;
    if (!command) {
      resolve({ code: null, stdout: "", stderr: "", error: "empty command" });
      return;
    }
    const controller = new AbortController();
    const onAbort = () => controller.abort();
    options.signal?.addEventListener("abort", onAbort, { once: true });
    const timer = setTimeout(() => controller.abort(), options.timeoutMs);
    let stdout = "";
    let stderr = "";
    let settled = false;
    const finish = (result: CommandResult) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      options.signal?.removeEventListener("abort", onAbort);
      resolve(result);
    };
    const child = spawn(command, args, {
      cwd: options.cwd,
      env: options.env ? { ...process.env, ...options.env } : process.env,
      signal: controller.signal,
      stdio: [options.input === undefined ? "ignore" : "pipe", "pipe", "pipe"],
      windowsHide: true,
    });
    child.stdout?.on("data", (chunk: Buffer) => {
      if (stdout.length < OUTPUT_LIMIT) stdout += chunk.toString("utf8");
    });
    child.stderr?.on("data", (chunk: Buffer) => {
      if (stderr.length < OUTPUT_LIMIT) stderr += chunk.toString("utf8");
    });
    if (options.input !== undefined) child.stdin?.end(options.input);
    child.on("error", (error) => {
      const reason = controller.signal.aborted
        ? options.signal?.aborted ? "cancelled" : `timed out after ${options.timeoutMs} ms`
        : error.message;
      finish({ code: null, stdout, stderr, error: reason });
    });
    child.on("close", (code) => {
      const reason = controller.signal.aborted
        ? options.signal?.aborted ? "cancelled" : `timed out after ${options.timeoutMs} ms`
        : undefined;
      finish({ code, stdout, stderr, ...(reason ? { error: reason } : {}) });
    });
  });

/**
 * Commands that change remote or shared state. Dry-run and `publish: none` modes must never issue
 * them; the command log records the classification so evidence can prove that.
 */
export function isRemoteMutation(argv: readonly string[]): boolean {
  const [tool, first, second] = argv;
  if (tool === "git") return first === "push";
  if (tool === "gh") {
    if (first === "api") {
      const methodIndex = argv.findIndex((arg) => arg === "-X" || arg === "--method");
      const method = methodIndex >= 0 ? (argv[methodIndex + 1] ?? "").toUpperCase() : undefined;
      // gh api switches to POST when request fields are present and no method is given.
      const hasFields = argv.some((arg) => /^(?:-f|-F|--field|--raw-field|--input)$/.test(arg));
      return method !== undefined ? method !== "GET" : hasFields;
    }
    return (first === "pr" || first === "issue" || first === "release" || first === "repo")
      && ["create", "edit", "close", "reopen", "merge", "comment", "delete"].includes(second ?? "");
  }
  return false;
}

/** Run a command and throw with its output when it fails. */
export async function runChecked(runner: CommandRunner, argv: readonly string[], options: CommandOptions): Promise<string> {
  const result = await runner(argv, options);
  if (result.code !== 0) {
    throw new Error(`${argv.join(" ")} failed (${result.error ?? `exit ${result.code}`})\n${(result.stderr || result.stdout).trim().slice(-4000)}`);
  }
  return result.stdout.trim();
}

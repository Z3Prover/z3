/** Git worktree helpers for slice isolation. All commands go through the injectable runner. */
import { existsSync } from "node:fs";
import { runChecked, type CommandRunner } from "./command.js";

export interface WorktreeRequest {
  readonly path: string;
  readonly branch: string;
  readonly base: string;
  readonly signal?: AbortSignal;
}

/** Create a worktree on a new branch, or reuse it when a resumed run already created it. */
export async function ensureWorktree(runner: CommandRunner, repoRoot: string, request: WorktreeRequest): Promise<{ created: boolean }> {
  const options = { cwd: repoRoot, timeoutMs: 10 * 60_000, signal: request.signal };
  if (existsSync(request.path)) {
    const current = await runChecked(runner, ["git", "-C", request.path, "rev-parse", "--abbrev-ref", "HEAD"], options);
    if (current !== request.branch) throw new Error(`${request.path} is checked out on ${current}, expected ${request.branch}`);
    return { created: false };
  }
  const exists = (await runner(["git", "show-ref", "--verify", "--quiet", `refs/heads/${request.branch}`], options)).code === 0;
  // The repository has benchmark paths longer than Windows' default 260-character limit.
  const git = ["git", "-c", "core.longpaths=true"];
  await runChecked(runner, exists
    ? [...git, "worktree", "add", request.path, request.branch]
    : [...git, "worktree", "add", "-b", request.branch, request.path, request.base], options);
  if (process.platform === "win32") await runChecked(runner, ["git", "-C", request.path, "config", "core.longpaths", "true"], options);
  return { created: true };
}

/** Remove a clean worktree (its branch and commits stay); dirty worktrees are kept for inspection. */
export async function removeCleanWorktree(runner: CommandRunner, repoRoot: string, path: string, signal?: AbortSignal): Promise<"removed" | "kept-dirty" | "absent"> {
  if (!existsSync(path)) return "absent";
  const result = await runner(["git", "worktree", "remove", path], { cwd: repoRoot, timeoutMs: 5 * 60_000, signal });
  return result.code === 0 ? "removed" : "kept-dirty";
}

/**
 * The head of `branch` when it carries commits that `base` does not; undefined when the branch is
 * missing or has none. Read-only (`rev-parse`, `rev-list`); other git failures throw.
 */
export async function committedBeyond(runner: CommandRunner, repoRoot: string, branch: string, base: string, signal?: AbortSignal): Promise<string | undefined> {
  const options = { cwd: repoRoot, timeoutMs: 60_000, signal };
  const head = await runner(["git", "rev-parse", "--verify", "--quiet", `refs/heads/${branch}^{commit}`], options);
  // --verify --quiet exits 1, silently, when the ref does not exist.
  if (head.code === 1 && !head.stdout.trim()) return undefined;
  if (head.code !== 0) throw new Error(`git rev-parse ${branch} failed in ${repoRoot}: ${(head.error ?? head.stderr).trim()}`);
  const commit = head.stdout.trim();
  const ahead = Number(await runChecked(runner, ["git", "rev-list", "--count", `${base}..${commit}`], options));
  return ahead > 0 ? commit : undefined;
}

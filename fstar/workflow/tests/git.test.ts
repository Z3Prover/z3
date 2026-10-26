import { describe, expect, test } from "bun:test";
import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnRunner } from "../lib/command.ts";
import { ensureWorktree, removeCleanWorktree } from "../lib/git.ts";

function scratchRepository(): string {
  const root = mkdtempSync(join(tmpdir(), "fpc-git-"));
  const git = (...args: string[]) => execFileSync("git", args, { cwd: root, encoding: "utf8" });
  git("init", "-q", "-b", "main");
  git("config", "user.email", "test@example.com");
  git("config", "user.name", "Test");
  // A path longer than 260 characters once nested under a worktree directory.
  const deep = join(root, "d".repeat(80), "e".repeat(80));
  execFileSync("git", ["-c", "core.longpaths=true", "config", "core.longpaths", "true"], { cwd: root });
  mkdirSync(deep, { recursive: true });
  writeFileSync(join(deep, `${"f".repeat(90)}.smt2`), "(check-sat)\n");
  git("add", "-A");
  git("commit", "-q", "-m", "init");
  // Like a default Windows clone of z3, the repository itself does not enable long paths.
  git("config", "--unset", "core.longpaths");
  return root;
}

describe("slice worktrees", () => {
  test("are created on their own branch with long paths, reused on resume, and removed when clean", async () => {
    const repo = scratchRepository();
    const path = join(repo, ".atomic", "fstar-proof-checking", "worktrees", "20261026T101500Z-abcd-i1-bitvectors-repair");
    const request = { path, branch: "fstar-proof-checking/work/r/i1-bitvectors-repair", base: "main" };
    expect(await ensureWorktree(spawnRunner, repo, request)).toEqual({ created: true });
    expect(execFileSync("git", ["-C", path, "rev-parse", "--abbrev-ref", "HEAD"], { encoding: "utf8" }).trim()).toBe(request.branch);
    expect(await ensureWorktree(spawnRunner, repo, request)).toEqual({ created: false });
    await expect(ensureWorktree(spawnRunner, repo, { ...request, branch: "other" })).rejects.toThrow(/expected other/);
    expect(await removeCleanWorktree(spawnRunner, repo, path)).toBe("removed");
    expect(existsSync(path)).toBe(false);
    expect(execFileSync("git", ["branch", "--list", request.branch], { cwd: repo, encoding: "utf8" })).toContain(request.branch);
  }, 60_000);
});

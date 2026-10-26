import { describe, expect, test } from "bun:test";
import { execFileSync, spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnRunner } from "../lib/command.ts";
import { ensureWorktree, removeCleanWorktree } from "../lib/git.ts";
import { worktreePrologue, type ToolchainReport } from "../lib/toolchain.ts";

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

// Linux git under WSL must be able to use the worktrees Windows git creates: the checker build runs `git rev-parse HEAD` in them.
const distro = process.env.Z3_FSTAR_WSL_DISTRO || "Ubuntu";
const wslReady = process.platform === "win32"
  && spawnSync("wsl", ["-d", distro, "-e", "bash", "-c", "git --version"], { encoding: "utf8", timeout: 60_000 }).status === 0;

describe("slice worktrees under WSL", () => {
  test.skipIf(!wslReady)("Linux git resolves the worktree's HEAD through the generated prologue", async () => {
    const repo = scratchRepository();
    const path = join(repo, ".atomic", "fstar-proof-checking", "worktrees", "20261026T101500Z-abcd-i1-bitvectors-performance");
    const branch = "fstar-proof-checking/work/r/i1-bitvectors-performance";
    await ensureWorktree(spawnRunner, repo, { path, branch, base: "main" });
    execFileSync("git", ["-C", path, "commit", "-q", "--allow-empty", "-m", "slice work"]);
    const toolchain: ToolchainReport = {
      environment: { kind: "wsl", distro, execArgv: ["wsl", "-d", distro, "-e"] }, opam: false, opamSwitch: "fstar53", candidates: {}, available: false, missing: [],
    };
    const script = `${worktreePrologue(toolchain, path)} && git rev-parse HEAD && git rev-parse --abbrev-ref HEAD`;
    const linux = spawnSync("wsl", ["-d", distro, "-e", "bash", "-lc", script], { encoding: "utf8", timeout: 120_000 });
    expect({ code: linux.status, stderr: linux.stderr }).toEqual({ code: 0, stderr: "" });
    const head = execFileSync("git", ["-C", path, "rev-parse", "HEAD"], { encoding: "utf8" }).trim();
    expect(linux.stdout.trim().split(/\r?\n/)).toEqual([head, branch]);
  }, 180_000);
});

import { describe, expect, test } from "bun:test";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import type { CommandOptions, CommandResult, CommandRunner } from "../lib/command.ts";
import { isRemoteMutation } from "../lib/command.ts";
import { executePublication, fileBugReports, gatherPublicationFacts, planPublication } from "../lib/publish.ts";
import type { PublicationState } from "../lib/state.ts";

interface FakeRemote {
  branches: Set<string>;
  prs: Array<{ number: number; state: "OPEN" | "MERGED" | "CLOSED"; url: string; head: string }>;
  issues: Array<{ number: number; url: string; body: string }>;
}

/** A scripted git/gh stand-in that models a remote and records every command. */
function fakeRunner(remote: FakeRemote) {
  const calls: string[][] = [];
  const ok = (stdout = ""): CommandResult => ({ code: 0, stdout, stderr: "" });
  const runner: CommandRunner = async (argv: readonly string[], _options: CommandOptions) => {
    calls.push([...argv]);
    const [tool, a, b] = argv;
    if (tool === "git" && a === "ls-remote") {
      const branch = argv[argv.length - 1] ?? "";
      return ok(remote.branches.has(branch) ? `abc123\trefs/heads/${branch}\n` : "");
    }
    if (tool === "git" && a === "push") {
      const ref = argv[argv.length - 1] ?? "";
      remote.branches.add(ref.replace(/^HEAD:refs\/heads\//, ""));
      return ok();
    }
    if (tool === "gh" && a === "pr" && b === "list") {
      const head = argv[argv.indexOf("--head") + 1];
      const state = argv[argv.indexOf("--state") + 1];
      const rows = remote.prs.filter((pr) => pr.head === head && (state === "all" || pr.state.toLowerCase() === state));
      return ok(JSON.stringify(rows.map(({ number, state: prState, url }) => ({ number, state: prState, url }))));
    }
    if (tool === "gh" && a === "pr" && b === "create") {
      const head = argv[argv.indexOf("--head") + 1] ?? "";
      const number = 100 + remote.prs.length;
      const url = `https://github.com/Z3Prover/z3/pull/${number}`;
      remote.prs.push({ number, state: "OPEN", url, head });
      return ok(`${url}\n`);
    }
    if (tool === "gh" && a === "issue" && b === "list") {
      const search = argv[argv.indexOf("--search") + 1] ?? "";
      const marker = search.replace(/ in:body$/, "").replaceAll('"', "");
      return ok(JSON.stringify(remote.issues.filter((issue) => issue.body.includes(marker)).map(({ number, url }) => ({ number, url }))));
    }
    if (tool === "gh" && a === "issue" && b === "create") {
      const number = 7000 + remote.issues.length;
      const url = `https://github.com/FStarLang/FStar/issues/${number}`;
      remote.issues.push({ number, url, body: readFileSync(argv[argv.indexOf("--body-file") + 1] ?? "", "utf8") });
      return ok(`${url}\n`);
    }
    throw new Error(`unexpected command ${argv.join(" ")}`);
  };
  return { runner, calls };
}

const options = { repo: "Z3Prover/z3", remote: "origin", prefix: "fstar-proof-checking", base: "master", cwd: "C:/integration", timeoutMs: 1000 };
const empty: PublicationState = { sequence: 0, history: [] };
const active = (prNumber?: number): PublicationState => ({ activeBranch: "fstar-proof-checking/1", prNumber, sequence: 1, history: [] });
const body = () => {
  const path = join(mkdtempSync(join(tmpdir(), "fpc-pub-")), "body.md");
  writeFileSync(path, "Evidence");
  return path;
};

async function publishOnce(state: PublicationState, remote: FakeRemote, mode: "live" | "dry-run") {
  const fake = fakeRunner(remote);
  const facts = await gatherPublicationFacts(fake.runner, state, options);
  const plan = planPublication(state, facts, { prefix: options.prefix, hasChanges: true });
  const result = await executePublication(fake.runner, plan, { ...options, mode, title: "F* proof checker improvements", bodyFile: body() });
  return { plan, result, calls: fake.calls };
}

describe("publication lifecycle", () => {
  test("the first publication creates a branch and one PR", async () => {
    const remote: FakeRemote = { branches: new Set(), prs: [], issues: [] };
    const { plan, result } = await publishOnce(empty, remote, "live");
    expect(plan.action.kind).toBe("new-branch");
    expect(result.state.activeBranch).toBe("fstar-proof-checking/1");
    expect(result.state.prNumber).toBe(100);
    expect(remote.prs).toHaveLength(1);
  });

  test("an open PR keeps receiving pushes on the same branch without a second PR", async () => {
    const remote: FakeRemote = { branches: new Set(["fstar-proof-checking/1"]), prs: [{ number: 100, state: "OPEN", url: "u100", head: "fstar-proof-checking/1" }], issues: [] };
    const { plan, result, calls } = await publishOnce(active(100), remote, "live");
    expect(plan.action).toMatchObject({ kind: "push-existing", branch: "fstar-proof-checking/1" });
    expect(calls.filter((call) => call[0] === "git" && call[1] === "push")).toHaveLength(1);
    expect(calls.some((call) => call[1] === "pr" && call[2] === "create")).toBe(false);
    expect(result.state.activeBranch).toBe("fstar-proof-checking/1");
  });

  test("after a merge the next update goes to a new branch and a new PR", async () => {
    const remote: FakeRemote = { branches: new Set(["fstar-proof-checking/1"]), prs: [{ number: 100, state: "MERGED", url: "u100", head: "fstar-proof-checking/1" }], issues: [] };
    const { plan, result } = await publishOnce(active(100), remote, "live");
    expect(plan.action).toMatchObject({ kind: "new-branch", branch: "fstar-proof-checking/2" });
    expect(result.state).toMatchObject({ activeBranch: "fstar-proof-checking/2", prNumber: 101, sequence: 2 });
    expect(result.state.history.map((entry) => entry.state)).toEqual(["MERGED"]);
  });

  test("a deleted branch starts a new branch and PR", async () => {
    const remote: FakeRemote = { branches: new Set(), prs: [{ number: 100, state: "CLOSED", url: "u100", head: "fstar-proof-checking/1" }], issues: [] };
    const { plan } = await publishOnce(active(100), remote, "live");
    expect(plan.action).toMatchObject({ kind: "new-branch", branch: "fstar-proof-checking/2" });
  });

  test("a PR closed without merging while its branch exists blocks with an actionable reason", async () => {
    const remote: FakeRemote = { branches: new Set(["fstar-proof-checking/1"]), prs: [{ number: 100, state: "CLOSED", url: "u100", head: "fstar-proof-checking/1" }], issues: [] };
    const { plan, calls } = await publishOnce(active(100), remote, "live");
    expect(plan.action.kind).toBe("blocked");
    expect(plan.action.reason).toMatch(/closed without merging/);
    expect(calls.some(isRemoteMutation)).toBe(false);
  });

  test("re-running after a push whose PR creation was interrupted reuses the branch and creates exactly one PR", async () => {
    const remote: FakeRemote = { branches: new Set(["fstar-proof-checking/1"]), prs: [], issues: [] };
    const first = await publishOnce(active(), remote, "live");
    expect(first.plan.action.kind).toBe("push-and-open-pr");
    const second = await publishOnce(first.result.state, remote, "live");
    expect(second.plan.action.kind).toBe("push-existing");
    expect(remote.prs).toHaveLength(1);
  });

  test("a new branch name already taken on the remote is skipped", async () => {
    const remote: FakeRemote = { branches: new Set(["fstar-proof-checking/1", "fstar-proof-checking/2"]), prs: [{ number: 100, state: "MERGED", url: "u100", head: "fstar-proof-checking/1" }], issues: [] };
    const { plan } = await publishOnce(active(100), remote, "live");
    expect(plan.action).toMatchObject({ kind: "new-branch", branch: "fstar-proof-checking/3" });
  });

  test("dry-run publication issues read-only commands only and leaves state unchanged", async () => {
    for (const state of [empty, active(100)]) {
      const remote: FakeRemote = { branches: new Set(["fstar-proof-checking/1"]), prs: [{ number: 100, state: "MERGED", url: "u100", head: "fstar-proof-checking/1" }], issues: [] };
      const { result, calls } = await publishOnce(state, remote, "dry-run");
      expect(calls.filter(isRemoteMutation)).toEqual([]);
      expect(result.state).toEqual(state);
      expect(result.executed).toBe(false);
      expect(remote.prs).toHaveLength(1);
    }
  });

  test("without remote facts (dry-run workflow) the plan is computed from state and no command runs", async () => {
    const fake = fakeRunner({ branches: new Set(), prs: [], issues: [] });
    const plan = planPublication(active(100), { known: false, branchExists: false, prs: [], freeBranch: "fstar-proof-checking/2" }, { prefix: options.prefix, hasChanges: true });
    const result = await executePublication(fake.runner, plan, { ...options, mode: "dry-run", title: "t", bodyFile: body() });
    expect(plan.action.kind).toBe("push-existing");
    expect(fake.calls).toEqual([]);
    expect(result.executed).toBe(false);
  });

  test("nothing is published without verified changes", () => {
    const plan = planPublication(active(100), { known: true, branchExists: true, prs: [], freeBranch: "x" }, { prefix: options.prefix, hasChanges: false });
    expect(plan.action.kind).toBe("nothing-to-publish");
  });
});

describe("crash bug reports", () => {
  const drafts = () => [{ fingerprint: "abc", title: "Cherry checker crashes (SIGSEGV) on QF_BV", bodyFile: body() }];

  test("live filing searches for the fingerprint marker first and never duplicates", async () => {
    const remote: FakeRemote = { branches: new Set(), prs: [], issues: [] };
    const first = fakeRunner(remote);
    const filed = await fileBugReports(first.runner, drafts(), { repo: "FStarLang/FStar", mode: "live", timeoutMs: 1000 });
    expect(filed[0]).toMatchObject({ fingerprint: "abc", action: "created" });
    const second = fakeRunner(remote);
    const again = await fileBugReports(second.runner, drafts(), { repo: "FStarLang/FStar", mode: "live", timeoutMs: 1000 });
    expect(again[0]).toMatchObject({ action: "existing", url: filed[0]?.url });
    expect(remote.issues).toHaveLength(1);
  });

  test("dry-run filing only searches", async () => {
    const remote: FakeRemote = { branches: new Set(), prs: [], issues: [] };
    const fake = fakeRunner(remote);
    const planned = await fileBugReports(fake.runner, drafts(), { repo: "FStarLang/FStar", mode: "dry-run", timeoutMs: 1000 });
    expect(planned[0]?.action).toBe("would-create");
    expect(fake.calls.filter(isRemoteMutation)).toEqual([]);
    expect(remote.issues).toEqual([]);
  });
});

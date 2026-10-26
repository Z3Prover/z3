/**
 * Open pull requests that change the F* checker: a read-only snapshot taken at source time, and
 * its overlap with actionable findings. This is metadata, not a gate: it never changes a finding's
 * status, never releases a policy hold or a candidate, and never merges, cherry-picks or pushes a
 * PR. Heads are fetched read-only into `refs/fstar-proof-checking/prs/<n>` so stages can inspect
 * them, and every overlap is pinned to the head commit the snapshot saw, so each run re-evaluates
 * it from a fresh snapshot (a new head, a close or a merge is picked up by the next run).
 */
import type { CommandRunner } from "./command.js";
import type { Finding } from "./reports.js";

export type OpenPr = {
  readonly number: number;
  readonly title: string;
  readonly url: string;
  readonly headRefName: string;
  /** The head commit this snapshot, and every overlap derived from it, is pinned to. */
  readonly head: string;
  readonly baseRefName: string;
  /** `sources` when the PR changes fstar/ files a repair slice may edit; `audit-only` when its fstar/ change is audits or reports only. */
  readonly fstar: "sources" | "audit-only";
  /** fstar/ checker sources: F* modules, fstar/ocaml_runtime, fstar/cherry_runtime, fstar/tools and other non-report files. */
  readonly fstarSources: string[];
  /** fstar/ audit and report files (fstar/audits/**, Markdown). */
  readonly fstarAuditOnly: string[];
  /** Files outside fstar/, for example solver code under src/. */
  readonly otherFiles: string[];
  /** gh lists at most 100 files per PR; when it hit that cap the lists may be incomplete. */
  readonly filesTruncated?: boolean;
  /** The read-only local copy of the head, when it was fetched and matched `head`. */
  readonly localRef?: string;
  /** F* declarations (`Module.name`) whose definitions the PR's diff changes relative to the run's base. */
  readonly declarations?: string[];
  /** Why the head was not fetched, or did not match `head`. */
  readonly fetchError?: string;
};

export type OpenPrSnapshot =
  | {
    readonly status: "available";
    readonly at: string;
    readonly repo: string;
    /** The pinned base the PR diffs were taken against. */
    readonly base: string;
    readonly prs: OpenPr[];
    /** Open PRs left out: no fstar/ change outside fstar/workflow, or this workflow's own branches. */
    readonly ignored: Array<{ readonly number: number; readonly reason: string }>;
  }
  | { readonly status: "unavailable"; readonly at: string; readonly repo: string; readonly error: string }
  | { readonly status: "skipped"; readonly at: string; readonly repo: string; readonly reason: string };

/**
 * A finding's overlap with one open PR, pinned to the PR's head. `exact`: the PR's diff changes the
 * finding's own declaration. `potential`: the PR only changes files the finding's slice may edit
 * (the declaration's module, or, for findings without one, any checker source).
 */
export type PrOverlap = {
  readonly pr: number;
  readonly head: string;
  readonly title: string;
  readonly kind: "exact" | "potential";
  readonly files: string[];
  /** For `exact`: the declarations the PR's diff changes. */
  readonly declarations?: string[];
};

/** A finding as triage hands it to planning, annotated with the open PRs it overlaps. */
export type AnnotatedFinding = Finding & { readonly prOverlap?: PrOverlap[] };

/** An open PR that overlaps a slice's findings: its pinned head, the files it shares with them, and any exact declaration matches. */
export type SliceOpenPr = {
  readonly pr: number;
  readonly head: string;
  readonly title: string;
  /** The read-only local copy of the head the workflow fetches (`refs/fstar-proof-checking/prs/<n>`). */
  readonly ref: string;
  readonly files: string[];
  /** Findings whose own declaration the PR changes, with those declarations. */
  readonly exact: Array<{ readonly fingerprint: string; readonly declarations: string[] }>;
  /** Findings that only share files with the PR. */
  readonly potential: string[];
};

type GhPr = {
  number: number;
  title: string;
  headRefName: string;
  headRefOid: string;
  baseRefName: string;
  url: string;
  files?: Array<{ path: string }> | null;
};

const GH_FILE_LIMIT = 100;

/** Which part of the snapshot a changed path belongs to. */
export function classifyPrFile(path: string): "workflow" | "audit" | "source" | "other" {
  if (!path.startsWith("fstar/")) return "other";
  if (path.startsWith("fstar/workflow")) return "workflow";
  if (path.startsWith("fstar/audits/") || /\.md$/i.test(path)) return "audit";
  return "source";
}

/** Classify `gh pr list --json ...,files` rows; PRs without an fstar/ change outside the workflow, and this workflow's own branches, are ignored. */
export function classifyOpenPrs(rows: readonly GhPr[], options: { readonly branchPrefix: string }): { prs: OpenPr[]; ignored: Array<{ number: number; reason: string }> } {
  const prs: OpenPr[] = [];
  const ignored: Array<{ number: number; reason: string }> = [];
  for (const row of [...rows].sort((left, right) => left.number - right.number)) {
    if (options.branchPrefix && row.headRefName.startsWith(`${options.branchPrefix}/`)) {
      ignored.push({ number: row.number, reason: `this workflow's own branch ${row.headRefName}` });
      continue;
    }
    const paths = (row.files ?? []).map((file) => file.path);
    const byClass = (kind: ReturnType<typeof classifyPrFile>) => paths.filter((path) => classifyPrFile(path) === kind).sort();
    const fstarSources = byClass("source");
    const fstarAuditOnly = byClass("audit");
    if (fstarSources.length + fstarAuditOnly.length === 0) {
      ignored.push({ number: row.number, reason: paths.some((path) => classifyPrFile(path) === "workflow") ? "changes only fstar/workflow under fstar/" : "changes no fstar/ files" });
      continue;
    }
    prs.push({
      number: row.number, title: row.title, url: row.url, headRefName: row.headRefName, head: row.headRefOid, baseRefName: row.baseRefName,
      fstar: fstarSources.length > 0 ? "sources" : "audit-only", fstarSources, fstarAuditOnly, otherFiles: byClass("other"),
      ...(paths.length >= GH_FILE_LIMIT ? { filesTruncated: true } : {}),
    });
  }
  return { prs, ignored };
}

const DECLARATION = /^(?:\[@@[^\]]*\]\s*)?(?:(?:inline_for_extraction|noextract|private|unfold|irreducible|noeq|abstract|assume|ghost)\s+)*(?:let|val|type|and)\s+(?:rec\s+)?\(?([A-Za-z_][A-Za-z0-9_']*)/;

/** Top-level declarations a unified diff (`git diff -U0`) changes: changed declaration lines and the enclosing declaration of each hunk. Indented (local) `let`s do not count. */
export function changedDeclarations(diff: string): string[] {
  const found = new Set<string>();
  let module: string | undefined;
  for (const line of diff.split(/\r?\n/)) {
    const file = /^\+\+\+ b\/(?:.*\/)?([A-Za-z0-9_.]+)\.fsti?$/.exec(line);
    if (file?.[1]) {
      module = file[1];
      continue;
    }
    if (line.startsWith("--- ") || line.startsWith("+++ ") || !module) continue;
    const text = line.startsWith("@@") ? (/^@@[^@]*@@ ?(.*)$/.exec(line)?.[1] ?? "") : /^[+-]/.test(line) ? line.slice(1) : "";
    const name = DECLARATION.exec(text)?.[1];
    if (name) found.add(`${module}.${name}`);
  }
  return [...found].sort();
}

export type SnapshotOptions = {
  readonly repo: string;
  readonly remote: string;
  readonly branchPrefix: string;
  /** The run's pinned base commit. */
  readonly base: string;
  readonly cwd: string;
  readonly signal?: AbortSignal;
  readonly now?: Date;
};

const describeFailure = (argv: readonly string[], result: { code: number | null; stdout: string; stderr: string; error?: string }) =>
  `${argv.slice(0, 3).join(" ")} failed (${result.error ?? `exit ${result.code}`}): ${(result.stderr || result.stdout).trim().slice(-600)}`;

/**
 * Snapshot the repository's open PRs that change fstar/ (read-only `gh pr list`), then fetch the
 * head of each PR that changes checker sources into `refs/fstar-proof-checking/prs/<n>` (read-only
 * for the remote) and record the declarations its diff changes. A failing `gh` yields an
 * `unavailable` snapshot with the error; a failing head fetch is recorded on that PR. Never throws
 * for command failures: the snapshot is metadata, not a gate.
 */
export async function snapshotOpenPrs(runner: CommandRunner, options: SnapshotOptions): Promise<OpenPrSnapshot> {
  const at = (options.now ?? new Date()).toISOString();
  const argv = ["gh", "pr", "list", "--repo", options.repo, "--state", "open", "--json", "number,title,headRefName,headRefOid,baseRefName,url,files", "--limit", "100"];
  let rows: GhPr[];
  try {
    const result = await runner(argv, { cwd: options.cwd, timeoutMs: 120_000, signal: options.signal });
    if (result.code !== 0) return { status: "unavailable", at, repo: options.repo, error: describeFailure(argv, result) };
    rows = JSON.parse(result.stdout) as GhPr[];
    if (!Array.isArray(rows)) throw new Error("gh pr list did not return a JSON array");
  } catch (error) {
    return { status: "unavailable", at, repo: options.repo, error: error instanceof Error ? error.message : String(error) };
  }
  const classified = classifyOpenPrs(rows, options);
  const prs: OpenPr[] = [];
  const git = { cwd: options.cwd, timeoutMs: 5 * 60_000, signal: options.signal };
  for (const pr of classified.prs) {
    if (pr.fstar !== "sources") {
      prs.push(pr);
      continue;
    }
    const localRef = `refs/fstar-proof-checking/prs/${pr.number}`;
    try {
      const fetchArgv = ["git", "fetch", "--no-tags", options.remote, `+refs/pull/${pr.number}/head:${localRef}`];
      const fetched = await runner(fetchArgv, git);
      if (fetched.code !== 0) throw new Error(describeFailure(fetchArgv, fetched));
      const resolved = (await runner(["git", "rev-parse", "--verify", "--quiet", `${localRef}^{commit}`], git)).stdout.trim();
      // The PR moved between the listing and the fetch: overlaps stay pinned to the listed head.
      if (resolved !== pr.head) throw new Error(`fetched head ${resolved || "(none)"} is not the listed head ${pr.head}; the PR changed during the snapshot`);
      const modules = pr.fstarSources.filter((path) => /\.fsti?$/.test(path));
      const diffArgv = ["git", "diff", "-U0", "--no-color", `${options.base}...${localRef}`, "--", ...modules];
      const diff = modules.length === 0 ? { code: 0, stdout: "", stderr: "" } : await runner(diffArgv, git);
      if (diff.code !== 0) throw new Error(describeFailure(diffArgv, diff));
      prs.push({ ...pr, localRef, declarations: changedDeclarations(diff.stdout) });
    } catch (error) {
      prs.push({ ...pr, fetchError: error instanceof Error ? error.message : String(error) });
    }
  }
  return { status: "available", at, repo: options.repo, base: options.base, prs, ignored: classified.ignored };
}

/** The F* module a finding is about, when it names one: build findings carry `Module.declaration` (or the module's file). */
function findingModule(finding: Finding): string | undefined {
  if (finding.checker !== "fstar-build") return undefined;
  const fromFile = /(?:^|[\\/])([A-Za-z0-9_.]+)\.fsti?(?:\(|$)/.exec(finding.location ?? finding.rule)?.[1];
  return fromFile ?? (/^([A-Z][A-Za-z0-9_]*)\./.exec(finding.rule)?.[1]);
}

/**
 * The open PRs a finding overlaps, pinned to their heads. A finding that names an F* module
 * overlaps the PRs that change that module's files (`exact` when the PR changes its declaration);
 * any other finding overlaps every PR that changes checker sources, because its slice may edit any
 * of them. Audit-only PRs never overlap. Pure: callers apply it only to findings that already
 * passed triage, so it can neither release nor hold a finding.
 */
export function prOverlapsFor(finding: Finding, snapshot: OpenPrSnapshot | undefined): PrOverlap[] {
  if (!snapshot || snapshot.status !== "available") return [];
  const module = findingModule(finding);
  const overlaps: PrOverlap[] = [];
  for (const pr of snapshot.prs) {
    if (pr.fstar !== "sources") continue;
    if (module === undefined) {
      overlaps.push({ pr: pr.number, head: pr.head, title: pr.title, kind: "potential", files: pr.fstarSources });
      continue;
    }
    const files = pr.fstarSources.filter((path) => new RegExp(`(?:^|/)${module.replace(/\./g, "\\.")}\\.fsti?$`).test(path));
    if (files.length === 0) continue;
    const exact = (pr.declarations ?? []).filter((name) => name === finding.rule);
    overlaps.push({
      pr: pr.number, head: pr.head, title: pr.title, kind: exact.length > 0 ? "exact" : "potential", files,
      ...(exact.length > 0 ? { declarations: exact } : {}),
    });
  }
  return overlaps;
}

/** The open PRs a slice's annotated findings overlap, one entry per PR (pinned to the head the snapshot saw). */
export function sliceOpenPrs(findings: readonly AnnotatedFinding[]): SliceOpenPr[] {
  const byPr = new Map<number, { pr: number; head: string; title: string; files: Set<string>; exact: SliceOpenPr["exact"]; potential: string[] }>();
  for (const finding of findings) {
    for (const overlap of finding.prOverlap ?? []) {
      const entry = byPr.get(overlap.pr) ?? { pr: overlap.pr, head: overlap.head, title: overlap.title, files: new Set<string>(), exact: [], potential: [] };
      for (const file of overlap.files) entry.files.add(file);
      if (overlap.kind === "exact") entry.exact.push({ fingerprint: finding.fingerprint, declarations: overlap.declarations ?? [] });
      else entry.potential.push(finding.fingerprint);
      byPr.set(overlap.pr, entry);
    }
  }
  return [...byPr.values()].sort((left, right) => left.pr - right.pr).map((entry) => ({
    pr: entry.pr, head: entry.head, title: entry.title, ref: `refs/fstar-proof-checking/prs/${entry.pr}`, files: [...entry.files].sort(), exact: entry.exact, potential: entry.potential,
  }));
}

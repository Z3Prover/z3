/**
 * Deterministic soundness gate for slice candidates. A candidate is `verified` only when an
 * independent verifier ran the real toolchain successfully and the diff introduces no admits,
 * assumptions, lax checking, or raised global proof budgets. Model self-report alone never
 * passes the gate, and an unavailable toolchain always yields `unverified`.
 */
import { runChecked, type CommandRunner } from "./command.js";
import type { SliceOutcome } from "./state.js";

/** Structured verdict returned by the fresh verifier stage (schema in `schemas.ts`). */
export type VerifierVerdict = {
  readonly verdict: "verified" | "unverified" | "rejected";
  readonly toolchainAvailable: boolean;
  readonly commands: ReadonlyArray<{ readonly command: string; readonly exitCode: number; readonly phase: "baseline" | "exploratory" | "final" }>;
  readonly resolvedFingerprints: readonly string[];
  readonly soundnessConcerns: readonly string[];
  readonly summary: string;
};

export interface ScanFinding {
  readonly file: string;
  readonly line: string;
  readonly pattern: string;
}

export interface UnsoundnessScan {
  readonly violations: ScanFinding[];
  readonly warnings: ScanFinding[];
}

const UNSOUND_PATTERNS: ReadonlyArray<readonly [RegExp, string]> = [
  [/\badmit\b/, "admit"],
  [/\btadmit\b/, "tadmit"],
  [/\badmit_smt_queries\b/, "admit_smt_queries"],
  [/\bassume\s+val\b/, "assume val"],
  [/\bassume\s*\(/, "assume ("],
  [/--lax\b/, "lax"],
];

/** Remove string literals and single-line comments so prose about admits is not flagged. */
function codeOnly(line: string): string {
  return line
    .replace(/"(?:[^"\\]|\\.)*"/g, (literal) => (/--(?:admit_smt_queries|lax)\b/.test(literal) ? literal : '""'))
    .replace(/\(\*.*?\*\)/g, " ")
    .replace(/\/\/.*$/, "");
}

const RLIMIT = /#(set|push)-options\s+"[^"]*--z3rlimit\s+(\d+)/;

/** Scan the added lines of a unified diff. */
export function scanDiffForUnsoundness(diff: string): UnsoundnessScan {
  const violations: ScanFinding[] = [];
  const warnings: ScanFinding[] = [];
  const removedGlobal = new Map<string, number>();
  const addedGlobal: Array<{ file: string; line: string; value: number }> = [];
  let file = "";
  for (const raw of diff.split(/\r?\n/)) {
    const header = /^\+\+\+ b\/(.+)$/.exec(raw);
    if (header?.[1]) {
      file = header[1];
      continue;
    }
    if (raw.startsWith("---") || raw.startsWith("+++")) continue;
    const added = raw.startsWith("+");
    const removed = raw.startsWith("-");
    if (!added && !removed) continue;
    const text = raw.slice(1);
    const rlimit = RLIMIT.exec(text);
    if (rlimit?.[1] && rlimit[2]) {
      const value = Number(rlimit[2]);
      if (rlimit[1] === "set") {
        if (removed) removedGlobal.set(file, Math.max(removedGlobal.get(file) ?? 0, value));
        else addedGlobal.push({ file, line: text, value });
      } else if (added && value > 5) {
        warnings.push({ file, line: text.trim(), pattern: "local z3rlimit increase" });
      }
    }
    if (!added || !/\.(?:fsti?|ps1|py|json|ml)$/.test(file)) continue;
    const code = codeOnly(text);
    for (const [pattern, label] of UNSOUND_PATTERNS) {
      if (pattern.test(code)) {
        violations.push({ file, line: text.trim(), pattern: label });
        break;
      }
    }
  }
  for (const item of addedGlobal) {
    // F*'s default rlimit is 5; a module-wide value above the one it replaces raises the global budget.
    if (item.value > (removedGlobal.get(item.file) ?? 5)) {
      violations.push({ file: item.file, line: item.line.trim(), pattern: "increased global z3rlimit" });
    }
  }
  return { violations, warnings };
}

export interface SliceGateInput {
  readonly scan: UnsoundnessScan;
  readonly changedFiles: number;
  readonly uncommitted: boolean;
  readonly verifier: VerifierVerdict | undefined;
  /** Result of the workflow's own toolchain preflight. */
  readonly toolchainAvailable: boolean;
}

export interface SliceGateOutcome {
  readonly status: SliceOutcome;
  readonly reasons: string[];
}

export function decideSliceOutcome(input: SliceGateInput): SliceGateOutcome {
  if (input.scan.violations.length > 0) {
    return { status: "rejected", reasons: input.scan.violations.map((item) => `${item.file}: ${item.pattern} (${item.line})`) };
  }
  if (input.changedFiles === 0) return { status: "no-change", reasons: ["the slice produced no committed changes"] };
  const reasons: string[] = [];
  if (input.uncommitted) reasons.push("the worktree has uncommitted changes");
  const verifier = input.verifier;
  if (!verifier) return { status: "unverified", reasons: [...reasons, "the independent verifier returned no verdict"] };
  if (verifier.verdict === "rejected") return { status: "rejected", reasons: [...reasons, `verifier rejected: ${verifier.summary}`] };
  if (!input.toolchainAvailable || !verifier.toolchainAvailable) reasons.push("the F*/OCaml/Cherry toolchain was unavailable, so nothing was proof-checked");
  const finals = verifier.commands.filter((command) => command.phase === "final");
  if (finals.length === 0) reasons.push("no final validation command was recorded");
  const failed = finals.filter((command) => command.exitCode !== 0);
  if (failed.length > 0) reasons.push(`final validation failed: ${failed.map((command) => `${command.command} (exit ${command.exitCode})`).join("; ")}`);
  if (verifier.verdict !== "verified") reasons.push(`verifier verdict ${verifier.verdict}: ${verifier.summary}`);
  return reasons.length === 0 ? { status: "verified", reasons: [verifier.summary] } : { status: "unverified", reasons };
}

export interface SliceChanges {
  readonly diff: string;
  readonly changedFiles: number;
  readonly uncommitted: boolean;
  readonly head: string;
}

/** Collect the committed diff of a slice branch against its base, and whether it is dirty. */
export async function collectSliceChanges(runner: CommandRunner, worktree: string, base: string, signal?: AbortSignal): Promise<SliceChanges> {
  const options = { cwd: worktree, timeoutMs: 120_000, signal };
  const diff = await runChecked(runner, ["git", "diff", "--no-color", `${base}...HEAD`], options);
  const names = await runChecked(runner, ["git", "diff", "--name-only", `${base}...HEAD`], options);
  const status = await runChecked(runner, ["git", "status", "--porcelain"], options);
  const head = await runChecked(runner, ["git", "rev-parse", "HEAD"], options);
  return { diff, changedFiles: names === "" ? 0 : names.split(/\r?\n/).length, uncommitted: status !== "", head };
}

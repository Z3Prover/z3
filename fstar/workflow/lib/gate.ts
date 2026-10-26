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

/**
 * F* escape hatches: `admit`/`tadmit` and their variants (admit_all, admitP, admit_dump, tadmit_t,
 * admit_smt_queries, …), `magic`, `unsafe_coerce`, and every `assume` (val, type, new type, an
 * expression, Prims' `_assume` and Pulse's `assume_`), also qualified (`Pulse.Lib.Core.assume_`).
 * A name only counts when it is a whole identifier (`_` and `'` are identifier characters), so
 * `admitted`, `assumed` or `my_assume` pass.
 */
const NOT_IDENT_BEFORE = "(?<![A-Za-z0-9_'])";
const NOT_IDENT_AFTER = "(?![A-Za-z0-9_'])";
const identifier = (pattern: string) => new RegExp(`${NOT_IDENT_BEFORE}${pattern}${NOT_IDENT_AFTER}`);
const FSTAR_ESCAPES: ReadonlyArray<readonly [RegExp, string]> = [
  [identifier("_?t?admit(?:[A-Z_][A-Za-z0-9_']*)?"), "admit"],
  [identifier("magic"), "magic"],
  [identifier("unsafe_coerce"), "unsafe_coerce"],
  [identifier("_?assume_?"), "assume"],
];

/** OCaml escape hatches in the hand-written runtime (`fstar/ocaml_runtime`) and other OCaml sources. */
const OCAML_ESCAPES: ReadonlyArray<readonly [RegExp, string]> = [
  [identifier("Obj\\.(?:magic|repr|obj)"), "Obj.magic"],
];

/** Unsound or budget-raising F* options, wherever they appear (pragmas, Makefiles, scripts, CI and build configs). */
const OPTION_ESCAPES: ReadonlyArray<readonly [RegExp, string]> = [
  [/\badmit_smt_queries\b/, "admit_smt_queries"],
  [/--admit_except\b/, "--admit_except"],
  [/--lax\b/, "--lax"],
  [/--z3rlimit_factor\b/, "--z3rlimit_factor"],
  [/--__no_positivity\b/, "--__no_positivity"],
];

const FSTAR_SOURCE = /\.(?:fsti?|fsx)$/;
const HASH_COMMENTS = /(?:^|\/)(?:Makefile|GNUmakefile|CMakeLists\.txt|Dockerfile)$|\.(?:mk|sh|bash|py|ps1|psm1|ya?ml|toml|cmake|cfg|ini|txt)$/;
const ML_SOURCE = /\.mli?$/;
/** A character literal: `'a'`, `'"'`, `'\''`, `'\\'`, `'\n'`, `'\x41'`, `'\u0041'`, `'\065'`. */
const CHAR_LITERAL = /^'(?:[^'\\\r\n]|\\(?:[\\'"ntrbf0 ]|x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|[0-9]{3}))'/;

/**
 * Strip comments (nested `(* *)` across lines; `//` in F*), character literals, and string literals
 * that carry no option. A `'` inside or after an identifier (`x'`) or before a type variable (`'a`)
 * is not a literal.
 */
function sourceCode(line: string, depthIn: number, lineComments: boolean): { code: string; depth: number } {
  let depth = depthIn;
  let code = "";
  for (let index = 0; index < line.length; index += 1) {
    const pair = line.slice(index, index + 2);
    if (pair === "(*") {
      depth += 1;
      index += 1;
    } else if (depth > 0 && pair === "*)") {
      depth -= 1;
      index += 1;
    } else if (depth > 0) {
      continue;
    } else if (lineComments && pair === "//") {
      break;
    } else if (line[index] === "'" && !/[A-Za-z0-9_']/.test(line[index - 1] ?? "") && CHAR_LITERAL.test(line.slice(index))) {
      code += "' '";
      index += (CHAR_LITERAL.exec(line.slice(index))?.[0].length ?? 1) - 1;
    } else if (line[index] === '"') {
      const literal = /^"(?:[^"\\]|\\.)*"?/.exec(line.slice(index))?.[0] ?? '"';
      code += OPTION_ESCAPES.some(([pattern]) => pattern.test(literal)) || /--z3rlimit\b/.test(literal) ? literal : '""';
      index += literal.length - 1;
    } else {
      code += line[index];
    }
  }
  return { code, depth };
}

function otherCode(file: string, line: string): string {
  if (HASH_COMMENTS.test(file)) return line.replace(/(^|\s)#.*$/, "$1");
  return line;
}

const PRAGMA = /#(set|reset|push)-options\s+"([^"]*)"/;
const RLIMIT = /--z3rlimit\s+(\d+)/;

/**
 * Scan the added lines of a unified diff for unsound escapes. Every changed text file is scanned:
 * F* sources for escape hatches and options, OCaml sources for `Obj.magic`/`Obj.repr`/`Obj.obj`,
 * other files (Makefiles, scripts, CI and build configs) for unsound options and raised rlimits in
 * build flags. Comments, character and string literals, and removed lines are ignored. A
 * module-wide `--z3rlimit` (`#set-options`/`#reset-options`, or a build flag) above the value it
 * replaces (F*'s default 5) is a violation; a local `#push-options` raise is a warning.
 */
export function scanDiffForUnsoundness(diff: string): UnsoundnessScan {
  const violations: ScanFinding[] = [];
  const warnings: ScanFinding[] = [];
  const removedGlobal = new Map<string, number>();
  const addedGlobal: Array<{ file: string; line: string; value: number }> = [];
  let file = "";
  let depth = 0;
  for (const raw of diff.split(/\r?\n/)) {
    const header = /^\+\+\+ (?:b\/(.+)|\/dev\/null)$/.exec(raw);
    if (header) {
      file = header[1] ?? "";
      depth = 0;
      continue;
    }
    if (raw.startsWith("diff --git ") || raw.startsWith("--- ")) continue;
    if (raw.startsWith("@@")) {
      depth = 0;
      continue;
    }
    const added = raw.startsWith("+");
    const removed = raw.startsWith("-");
    if (!file || (!added && !removed && !raw.startsWith(" "))) continue;
    const text = raw.slice(1);
    const fstar = FSTAR_SOURCE.test(file);
    const ocaml = ML_SOURCE.test(file);
    let code: string;
    if (fstar || ocaml) {
      // Comment depth follows the new file (context and added lines).
      const stripped = sourceCode(text, removed ? 0 : depth, fstar);
      if (!removed) depth = stripped.depth;
      code = stripped.code;
    } else {
      code = otherCode(file, text);
    }
    if (!added && !removed) continue;
    const pragma = PRAGMA.exec(code);
    const rlimit = RLIMIT.exec(pragma?.[2] ?? (fstar ? "" : code));
    if (rlimit?.[1]) {
      const value = Number(rlimit[1]);
      if (pragma?.[1] === "push") {
        if (added && value > 5) warnings.push({ file, line: text.trim(), pattern: "local z3rlimit increase" });
      } else if (removed) {
        removedGlobal.set(file, Math.max(removedGlobal.get(file) ?? 0, value));
      } else {
        addedGlobal.push({ file, line: text, value });
      }
    }
    if (!added) continue;
    const match = [...(fstar ? FSTAR_ESCAPES : []), ...(ocaml ? OCAML_ESCAPES : []), ...OPTION_ESCAPES].find(([pattern]) => pattern.test(code));
    if (match) violations.push({ file, line: text.trim(), pattern: match[0].exec(code)?.[0] ?? match[1] });
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
  // Any soundness concern blocks acceptance, whatever severity the verifier gave it.
  if (verifier.soundnessConcerns.length > 0) reasons.push(`verifier soundness concerns: ${verifier.soundnessConcerns.join("; ")}`);
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

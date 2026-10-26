/**
 * Normalize Pulse checker reports (the `pulse-checker-report-*`, `pulse-checker-cherry-report-*`
 * and `pulse-checker-build-report` artifacts, or local directories in the same format written by
 * `fstar/tools/run_checker_regressions.py`) into deduplicated findings.
 */
import { createHash } from "node:crypto";
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { basename, join, relative } from "node:path";
import { classifyTheory, type Theory } from "./theories.js";

export type FindingKind =
  | "partial-rule"
  | "rejected"
  | "crash"
  | "check-timeout"
  | "build-timeout"
  | "slow-obligation";

export type CheckerKind = "ocaml" | "cherry" | "fstar-build";

export interface Finding {
  /** Stable deduplication key, independent of which report produced the finding. */
  readonly fingerprint: string;
  readonly kind: FindingKind;
  readonly theory: Theory;
  readonly checker: CheckerKind;
  /** Proof rule, F* declaration, or crash signature. */
  readonly rule: string;
  /** Obligation fingerprint, error excerpt, or other identifying detail. */
  readonly detail: string;
  readonly logic?: string;
  readonly affectedProofs: number;
  readonly obligations: number;
  readonly soleFamilyProofs: number;
  readonly milliseconds?: number;
  readonly location?: string;
  /** Representative inputs (corpus-relative SMT-LIB paths), at most six. */
  readonly examples: string[];
  /** Report files or directories that support the finding. */
  readonly evidence: string[];
  readonly sources: string[];
}

export interface NormalizedReports {
  readonly findings: Finding[];
  /** Human-readable notes about skipped or malformed inputs; never silently dropped. */
  readonly diagnostics: string[];
}

export interface NormalizeOptions {
  /** Identifier recorded on every finding, e.g. `pulse-run:40244844124-1` or `local:C:/bench/inputs`. */
  readonly source: string;
  /** Slow-obligation threshold in milliseconds; the instructions use "more than 2s". */
  readonly slowThresholdMs?: number;
}

export const SLOW_OBLIGATION_MS = 2000;
const MAX_EXAMPLES = 6;

interface ResultRow {
  readonly path: string;
  readonly outcome: string;
  readonly returncode?: number | null;
  readonly logic?: string;
  readonly verdict?: string;
  readonly matches_original?: boolean;
  readonly diagnostic_error?: string;
  readonly diagnostics?: {
    readonly obligations?: ReadonlyArray<{ rule: string; count: number; fingerprint: string }>;
  };
}

function digest(...parts: string[]): string {
  return createHash("sha256").update(parts.join("\u0000")).digest("hex").slice(0, 20);
}

/** Read a JSON-lines file, tolerating one truncated final record as the Python harness does. */
export function readJsonLines(path: string, diagnostics: string[]): ResultRow[] {
  const lines = readFileSync(path, "utf8").split(/\r?\n/);
  const rows: ResultRow[] = [];
  lines.forEach((line, index) => {
    if (line.trim() === "") return;
    try {
      rows.push(JSON.parse(line) as ResultRow);
    } catch {
      const isLast = lines.slice(index + 1).every((rest) => rest.trim() === "");
      if (!isLast) throw new Error(`Malformed JSON record ${index + 1} in ${path}`);
      diagnostics.push(`Incomplete final record in ${path}; raw log retained.`);
    }
  });
  return rows;
}

function logicOf(row: { path: string; logic?: string }, logics: ReadonlyMap<string, string>): string | undefined {
  if (row.logic) return row.logic;
  const known = logics.get(row.path);
  if (known) return known;
  const first = row.path.split("/", 1)[0] ?? "";
  return /^(?:QF_)?[A-Z]+$/.test(first) ? first : undefined;
}

function checkerOf(directory: string): CheckerKind {
  return /cherry/i.test(directory) ? "cherry" : "ocaml";
}

/** Every directory at or below `root` (depth ≤ 3) that holds a `results.jsonl` or `build.log`. */
function reportDirectories(root: string): string[] {
  const found: string[] = [];
  const visit = (directory: string, depth: number) => {
    const names = readdirSync(directory);
    if (names.includes("results.jsonl") || names.includes("build.log")) found.push(directory);
    if (depth >= 3) return;
    for (const name of names.sort()) {
      if (name === "logs" || name === "diagnostic-logs" || name === "inputs") continue;
      const child = join(directory, name);
      if (statSync(child).isDirectory()) visit(child, depth + 1);
    }
  };
  if (existsSync(root) && statSync(root).isDirectory()) visit(root, 0);
  return found;
}

function makeFinding(fields: Omit<Finding, "fingerprint" | "sources"> & { key: string[] }, source: string): Finding {
  const { key, ...rest } = fields;
  return { ...rest, fingerprint: digest(...key), sources: [source], examples: rest.examples.slice(0, MAX_EXAMPLES) };
}

function regressionFindings(directory: string, root: string, options: NormalizeOptions, diagnostics: string[]): Finding[] {
  const checker = checkerOf(relative(root, directory) || basename(directory));
  const results = readJsonLines(join(directory, "results.jsonl"), diagnostics);
  const logics = new Map<string, string>();
  for (const row of results) {
    const logic = logicOf(row, new Map());
    if (logic) logics.set(row.path, logic);
  }
  const findings: Finding[] = [];
  const groups = new Map<string, { rows: ResultRow[]; kind: FindingKind; rule: string; logic?: string }>();
  const group = (key: string, kind: FindingKind, rule: string, row: ResultRow, logic?: string) => {
    const entry = groups.get(key) ?? { rows: [], kind, rule, logic };
    entry.rows.push(row);
    groups.set(key, entry);
  };
  for (const row of results) {
    const logic = logicOf(row, logics);
    if (row.outcome === "CRASH" || row.outcome === "ERROR" || row.outcome === "PROTOCOL_ERROR") {
      const rule = row.outcome === "CRASH" ? `exit ${row.returncode ?? "signal"}` : row.outcome.toLowerCase();
      group(`crash|${checker}|${rule}|${logic ?? ""}`, "crash", rule, row, logic);
    } else if (row.outcome === "TIMEOUT") {
      group(`check-timeout|${checker}|${logic ?? ""}`, "check-timeout", "whole-case timeout", row, logic);
    } else if (row.outcome === "REJECT") {
      group(`rejected|${checker}|${row.path}`, "rejected", "REJECT", row, logic);
    }
  }
  for (const [key, entry] of groups) {
    findings.push(makeFinding({
      key: key.split("|"),
      kind: entry.kind,
      theory: classifyTheory({ logic: entry.logic, rule: entry.kind === "rejected" ? "" : undefined }),
      checker,
      rule: entry.rule,
      detail: entry.kind === "rejected" ? `checker rejected the UNSAT proof of ${entry.rows[0]?.path}` : "",
      logic: entry.logic,
      affectedProofs: entry.rows.length,
      obligations: 0,
      soleFamilyProofs: 0,
      examples: entry.rows.map((row) => row.path),
      evidence: [join(directory, "results.jsonl")],
    }, options.source));
  }

  // Partial proofs: one finding per (rule, obligation fingerprint) family, as in obligation_coverage().
  const diagnosticsPath = join(directory, "diagnostics.jsonl");
  const diagnosed = new Set<string>();
  if (existsSync(diagnosticsPath)) {
    const families = new Map<string, { rule: string; detail: string; obligations: number; proofs: number; sole: number; examples: string[]; logics: Set<string> }>();
    for (const row of readJsonLines(diagnosticsPath, diagnostics)) {
      if (!row.matches_original || row.diagnostic_error) continue;
      const obligations = row.diagnostics?.obligations ?? [];
      if (obligations.length === 0) continue;
      diagnosed.add(row.path);
      const distinct = new Set(obligations.map((item) => `${item.rule}\u0000${item.fingerprint}`));
      for (const item of obligations) {
        const key = `${item.rule}\u0000${item.fingerprint}`;
        const family = families.get(key) ?? { rule: item.rule, detail: item.fingerprint, obligations: 0, proofs: 0, sole: 0, examples: [], logics: new Set<string>() };
        family.obligations += item.count;
        family.proofs += 1;
        family.sole += distinct.size === 1 ? 1 : 0;
        family.examples.push(row.path);
        const logic = logicOf(row, logics);
        if (logic) family.logics.add(logic);
        families.set(key, family);
      }
    }
    for (const family of families.values()) {
      const logic = family.logics.size === 1 ? [...family.logics][0] : undefined;
      findings.push(makeFinding({
        key: ["partial-rule", family.rule, family.detail],
        kind: "partial-rule",
        theory: classifyTheory({ rule: family.rule, detail: family.detail, logic }),
        checker,
        rule: family.rule,
        detail: family.detail,
        logic,
        affectedProofs: family.proofs,
        obligations: family.obligations,
        soleFamilyProofs: family.sole,
        examples: family.examples,
        evidence: [diagnosticsPath],
      }, options.source));
    }
  }
  const undiagnosed = results.filter((row) => row.outcome === "PARTIAL" && !diagnosed.has(row.path));
  const byLogic = new Map<string, ResultRow[]>();
  for (const row of undiagnosed) {
    const logic = logicOf(row, logics) ?? "";
    byLogic.set(logic, [...(byLogic.get(logic) ?? []), row]);
  }
  for (const [logic, rows] of byLogic) {
    diagnostics.push(`${rows.length} PARTIAL result(s) in ${directory} (${logic || "unknown logic"}) have no matching diagnostics; recorded as undiagnosed.`);
    findings.push(makeFinding({
      key: ["partial-rule", "undiagnosed", checker, logic],
      kind: "partial-rule",
      theory: classifyTheory({ logic }),
      checker,
      rule: "undiagnosed",
      detail: "PARTIAL verdict without --diagnostics obligation families",
      logic: logic || undefined,
      affectedProofs: rows.length,
      obligations: rows.reduce((sum, row) => sum + Number(row.verdict?.split(" ")[1] ?? 0), 0),
      soleFamilyProofs: 0,
      examples: rows.map((row) => row.path),
      evidence: [join(directory, "results.jsonl")],
    }, options.source));
  }
  return findings;
}

export interface BuildLogSummary {
  readonly slow: Array<{ declaration: string; milliseconds: number }>;
  readonly timeouts: Array<{ location: string; file: string; declaration?: string; message: string }>;
  readonly verifiedModules: string[];
}

const PROFILED = /^(\S+), profiled FStarC\.TypeChecker\.Tc\.process_one_decl:\s*(\d+(?:\.\d+)?) ms\s*$/;
const ERROR_HEADER = /^\* Error (\d+) at ([^()]+)\((\d+,\d+-\d+,\d+)\):\s*$/;

/**
 * Parse an F* build log produced by `build_ocaml_checker.ps1` (`--timing --message_format human`).
 * Per-declaration times come from `process_one_decl` profiling lines; proof timeouts are F*
 * errors whose explanation says "The SMT query timed out".
 */
export function parseBuildLog(text: string, thresholdMs = SLOW_OBLIGATION_MS): BuildLogSummary {
  const lines = text.replace(/\u001b\[[0-9;]*m/g, "").split(/\r?\n/);
  const slow: BuildLogSummary["slow"] = [];
  const timeouts: Array<{ location: string; file: string; declaration?: string; message: string }> = [];
  const verifiedModules: string[] = [];
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index] ?? "";
    const verifying = /^Verifying (\S+)$/.exec(line);
    if (verifying?.[1]) verifiedModules.push(verifying[1]);
    const profiled = PROFILED.exec(line);
    if (profiled?.[1] && profiled[2]) {
      const declaration = profiled[1];
      const milliseconds = Number(profiled[2]);
      for (const timeout of timeouts) {
        const module = timeout.file.replace(/\.fsti?$/, "");
        if (timeout.declaration === undefined && declaration.startsWith(`${module}.`)) timeout.declaration = declaration;
      }
      if (milliseconds > thresholdMs) slow.push({ declaration, milliseconds });
      continue;
    }
    const header = ERROR_HEADER.exec(line);
    if (header?.[2] && header[3]) {
      const explanation: string[] = [];
      for (let next = index + 1; next < lines.length && /^\s/.test(lines[next] ?? ""); next += 1) {
        explanation.push((lines[next] ?? "").trim());
      }
      const timedOut = explanation.find((item) => /SMT query timed out|canceled|cancelled/i.test(item));
      if (timedOut) {
        timeouts.push({ location: `${header[2]}(${header[3]})`, file: header[2], message: timedOut.replace(/^- /, "") });
      }
    }
  }
  return { slow, timeouts, verifiedModules };
}

/** Build-timeout and slow-declaration findings from one F* build log (any file name). */
export function buildLogFindings(logPath: string, options: NormalizeOptions): Finding[] {
  const parsed = parseBuildLog(readFileSync(logPath, "utf8"), options.slowThresholdMs);
  const findings: Finding[] = [];
  const timedOut = new Set<string>();
  for (const timeout of parsed.timeouts) {
    const declaration = timeout.declaration ?? timeout.file;
    timedOut.add(declaration);
    const module = timeout.file.replace(/\.fsti?$/, "");
    findings.push(makeFinding({
      key: ["build-timeout", declaration],
      kind: "build-timeout",
      theory: classifyTheory({ module }),
      checker: "fstar-build",
      rule: declaration,
      detail: timeout.message,
      location: timeout.location,
      affectedProofs: 1,
      obligations: 1,
      soleFamilyProofs: 0,
      examples: [],
      evidence: [logPath],
    }, options.source));
  }
  for (const item of parsed.slow) {
    if (timedOut.has(item.declaration)) continue;
    const module = item.declaration.split(".", 1)[0] ?? "";
    findings.push(makeFinding({
      key: ["slow-obligation", item.declaration],
      kind: "slow-obligation",
      theory: classifyTheory({ module }),
      checker: "fstar-build",
      rule: item.declaration,
      detail: `process_one_decl took ${item.milliseconds} ms (> ${options.slowThresholdMs ?? SLOW_OBLIGATION_MS} ms)`,
      milliseconds: item.milliseconds,
      affectedProofs: 1,
      obligations: 1,
      soleFamilyProofs: 0,
      examples: [],
      evidence: [logPath],
    }, options.source));
  }
  return findings;
}

/** Merge findings that share a fingerprint, accumulating counts and evidence. */
export function mergeFindings(findings: readonly Finding[]): Finding[] {
  const merged = new Map<string, Finding>();
  for (const finding of findings) {
    const previous = merged.get(finding.fingerprint);
    if (!previous) {
      merged.set(finding.fingerprint, { ...finding, examples: [...finding.examples], evidence: [...finding.evidence], sources: [...finding.sources] });
      continue;
    }
    const union = (left: string[], right: string[]) => [...new Set([...left, ...right])];
    merged.set(finding.fingerprint, {
      ...previous,
      affectedProofs: previous.affectedProofs + finding.affectedProofs,
      obligations: previous.obligations + finding.obligations,
      soleFamilyProofs: previous.soleFamilyProofs + finding.soleFamilyProofs,
      milliseconds: Math.max(previous.milliseconds ?? 0, finding.milliseconds ?? 0) || undefined,
      examples: union(previous.examples, finding.examples).slice(0, MAX_EXAMPLES),
      evidence: union(previous.evidence, finding.evidence),
      sources: union(previous.sources, finding.sources),
    });
  }
  return [...merged.values()];
}

/** Normalize every report directory below `root` (an artifact download or a local report). */
export function normalizeReportTree(root: string, options: NormalizeOptions): NormalizedReports {
  const diagnostics: string[] = [];
  const findings: Finding[] = [];
  const directories = reportDirectories(root);
  if (directories.length === 0) diagnostics.push(`No results.jsonl or build.log found under ${root}.`);
  for (const directory of directories) {
    if (existsSync(join(directory, "results.jsonl"))) findings.push(...regressionFindings(directory, root, options, diagnostics));
    if (existsSync(join(directory, "build.log"))) findings.push(...buildLogFindings(join(directory, "build.log"), options));
  }
  return { findings: mergeFindings(findings), diagnostics };
}

/** Digest of the identifying evidence (rule, detail, examples); a change re-opens a blocked finding. */
export function evidenceDigest(finding: Finding): string {
  return digest(finding.kind, finding.rule, finding.detail, ...[...finding.examples].sort());
}

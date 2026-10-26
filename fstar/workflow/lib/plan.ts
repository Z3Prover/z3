/**
 * Split actionable findings into principled theory slices and allocate the 32-core budget.
 * Each slice gets its own git worktree and branch; slices run concurrently, so the sum of their
 * cores never exceeds the budget.
 */
import { join } from "node:path";
import type { Finding, FindingKind } from "./reports.js";
import type { Theory } from "./theories.js";

/** The machine budget stated in the instructions ("You have 32 cores"). */
export const MAX_CORES = 32;

export type SliceFocus = "crash" | "soundness" | "performance" | "repair";

export interface Slice {
  readonly id: string;
  readonly theory: Theory;
  readonly focus: SliceFocus;
  readonly findings: Finding[];
  readonly cores: number;
  readonly branch: string;
  readonly worktree: string;
}

export interface SlicePlan {
  readonly slices: Slice[];
  readonly concurrency: number;
  readonly totalCores: number;
  readonly coreBudget: number;
  /** Actionable findings left for a later iteration or run. */
  readonly deferred: string[];
}

export interface PlanOptions {
  readonly coreBudget: number;
  /** Minimum cores per slice; determines how many slices fit in the budget. */
  readonly coresPerSlice: number;
  readonly maxFindingsPerSlice: number;
  readonly runKey: string;
  readonly iteration: number;
  readonly worktreeRoot: string;
  readonly branchPrefix: string;
}

const FOCUS: Record<FindingKind, SliceFocus> = {
  crash: "crash",
  rejected: "soundness",
  "build-timeout": "performance",
  "slow-obligation": "performance",
  "check-timeout": "performance",
  "partial-rule": "repair",
};

export function sliceFocus(kind: FindingKind): SliceFocus {
  return FOCUS[kind];
}

/** Plan slices from findings that are already sorted by priority. */
export function planSlices(findings: readonly Finding[], options: PlanOptions): SlicePlan {
  const budget = Math.max(1, Math.min(MAX_CORES, Math.floor(options.coreBudget)));
  const perSlice = Math.max(1, Math.min(budget, Math.floor(options.coresPerSlice)));
  const maxSlices = Math.max(1, Math.floor(budget / perSlice));
  const groups = new Map<string, { theory: Theory; focus: SliceFocus; findings: Finding[] }>();
  const deferred: string[] = [];
  for (const finding of findings) {
    const focus = sliceFocus(finding.kind);
    const id = `${finding.theory}-${focus}`;
    const group = groups.get(id);
    if (!group && groups.size >= maxSlices) {
      deferred.push(finding.fingerprint);
      continue;
    }
    const target = group ?? { theory: finding.theory, focus, findings: [] };
    if (target.findings.length >= options.maxFindingsPerSlice) {
      deferred.push(finding.fingerprint);
      continue;
    }
    target.findings.push(finding);
    groups.set(id, target);
  }
  const cores = groups.size === 0 ? 0 : Math.max(1, Math.floor(budget / groups.size));
  const slices = [...groups.entries()].map(([id, group]): Slice => ({
    id,
    theory: group.theory,
    focus: group.focus,
    findings: group.findings,
    cores,
    branch: `${options.branchPrefix}/work/${options.runKey}/i${options.iteration}-${id}`,
    worktree: join(options.worktreeRoot, `${options.runKey}-i${options.iteration}-${id}`),
  }));
  return { slices, concurrency: slices.length, totalCores: cores * slices.length, coreBudget: budget, deferred };
}

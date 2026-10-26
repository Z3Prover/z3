/**
 * Theory classification for proof-checker findings. The instructions require work to be split
 * by the SMT theory involved, covering linear and non-linear arithmetic, UF, arrays, datatypes,
 * bit-vectors, finite fields, floating point, and quantifier instantiation/binding steps.
 */

export const THEORIES = [
  "linear-arithmetic",
  "nonlinear-arithmetic",
  "uf",
  "arrays",
  "datatypes",
  "bitvectors",
  "finite-fields",
  "floating-point",
  "quantifiers",
  "other",
] as const;

export type Theory = (typeof THEORIES)[number];

export interface TheoryEvidence {
  readonly rule?: string;
  readonly detail?: string;
  readonly logic?: string;
  /** F* module name for build findings, e.g. `Z3BvWord`. */
  readonly module?: string;
}

const QUANTIFIER_RULES = new Set([
  "quant-inst", "quant-intro", "sk", "pull-quant", "push-quant", "elim-unused", "der", "nnf-pos", "nnf-neg",
  "lambda", "bind", "beta",
]);

/** Operators that identify a theory in an obligation fingerprint (`op:Sort(...)`). */
const OPERATOR_THEORIES: ReadonlyArray<readonly [RegExp, Theory]> = [
  [/\bff\.|FiniteField|:FF\b/, "finite-fields"],
  [/\bfp\.|\bto_fp\b|FloatingPoint|RoundingMode|:FP\b/, "floating-point"],
  [/\bbv[a-z]*:|\bextract:|\bconcat:|\bbv2(?:nat|int):|\bint2bv:|BitVec/, "bitvectors"],
  [/\b(?:store|select|const-array|map):|Array\[/, "arrays"],
  [/\bis-[A-Za-z]|\baccessor|\bconstructor|Datatype/, "datatypes"],
  [/\b(?:forall|exists|lambda)\b/, "quantifiers"],
];

/** Module-name keywords used for F* build findings (slow declarations, proof timeouts). */
const MODULE_THEORIES: ReadonlyArray<readonly [RegExp, Theory]> = [
  [/FiniteField|Ff[A-Z]|Qfff/, "finite-fields"],
  [/Fpa|Mpf|Float|Fp[A-Z]|Rounding/, "floating-point"],
  [/Bv|BitVec/, "bitvectors"],
  [/Array/, "arrays"],
  [/Datatype|Adt/, "datatypes"],
  [/Quantifier|Skolem|Binder|Lambda|Der\b|DestructiveEquality|Nnf/, "quantifiers"],
  [/Nla|Monomial|Power|NonLinear|Nlsat/, "nonlinear-arithmetic"],
  [/Lp|Farkas|Linear|Integer|Arith/, "linear-arithmetic"],
  [/Congruence|Euf|Uf[A-Z]|ObservationalEquality|Equality/, "uf"],
];

function logicTheory(logic: string): Theory | undefined {
  const upper = logic.toUpperCase();
  const name = upper.replace(/^QF_/, "");
  if (/FF/.test(name)) return "finite-fields";
  if (/FP/.test(name)) return "floating-point";
  if (/BV/.test(name)) return "bitvectors";
  if (/^A|AX/.test(name)) return "arrays";
  if (/DT/.test(name)) return "datatypes";
  if (/N[IR]A/.test(name)) return "nonlinear-arithmetic";
  if (!upper.startsWith("QF_") && name !== "") return "quantifiers";
  if (/L[IR]A|IDL|RDL|LIRA/.test(name)) return "linear-arithmetic";
  if (/UF/.test(name)) return "uf";
  return undefined;
}

/**
 * Classify a finding into one theory slice. Rule names are the strongest signal, then operators
 * in the obligation fingerprint, then the benchmark logic, then the F* module name.
 */
export function classifyTheory(evidence: TheoryEvidence): Theory {
  const rule = evidence.rule ?? "";
  if (QUANTIFIER_RULES.has(rule) || rule.startsWith("quant")) return "quantifiers";
  if (rule.startsWith("assumed:nlsat") || rule.startsWith("arith/lp-monomial") || rule.startsWith("nla")) {
    return "nonlinear-arithmetic";
  }
  if (rule.startsWith("arith/") || rule === "farkas") return "linear-arithmetic";
  const detail = evidence.detail ?? "";
  // The outermost operator of a rewrite or lemma decides between mixed theories (store over bvadd is an array step).
  const head = detail.replace(/^(?:eq|holds)\(/, "").split(/[(,]/, 1)[0] ?? "";
  for (const [pattern, theory] of OPERATOR_THEORIES) if (pattern.test(head)) return theory;
  for (const [pattern, theory] of OPERATOR_THEORIES) if (pattern.test(detail)) return theory;
  const fromLogic = evidence.logic ? logicTheory(evidence.logic) : undefined;
  if (fromLogic) return fromLogic;
  if (evidence.module) {
    for (const [pattern, theory] of MODULE_THEORIES) if (pattern.test(evidence.module)) return theory;
  }
  return "other";
}

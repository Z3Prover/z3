# Neuro-Formal Audits of Z3 Source Code

[Overview](README.md) | [Formalization](FORMALIZATION.md) | [Proof checking](PROOF_CHECKING.md)

## Purpose and scope

This activity examines selected Z3 C++ implementations using the
[formalized SMT theories](FORMALIZATION.md). An audit identifies semantic
obligations in the source, proves the corresponding laws in F*, and
records the correspondence, findings, and exclusions in a report.
It can confirm a rule, expose a bug, validate a fix, or refute a proposed
bug by showing that the actual branch conditions rule out the witness.

Source audits are independent of the proof-checker activity. Auditing code
that produces or checks proofs is still a source audit; it does not require
running the verified checker on proofs. Conversely, a proof checker can
use a formalized law without relying on an audit of its C++ implementation.

These are scoped audits, not a machine-checked refinement of all Z3 C++
code. Reports distinguish proved semantic properties from source-level
inspection, implementation bookkeeping, deferred cases, and trust
boundaries. Consult each report for detailed coverage and verification
results rather than treating a report link as blanket verification.

## Theory implementations and rewriters

| Subject | Report | Main formalization/proof modules |
|---|---|---|
| Prime finite fields: declarations, rewriting, solvers, and tactics | [Finite fields](FINITE_FIELD_REPORT.md) | [`Z3FiniteFieldTheory.fst`](Z3FiniteFieldTheory.fst), [`Z3FiniteFieldSearch.fst`](Z3FiniteFieldSearch.fst) |
| Sequence rewrites, regex membership/algebra, derivatives, and axioms | [Sequences and regex](SEQ_REWRITER_REPORT.md) | [`Z3SeqRewrites.fst`](Z3SeqRewrites.fst), [`Z3SeqDerive.fst`](Z3SeqDerive.fst), [`Z3RegexMembership.fst`](Z3RegexMembership.fst), [`Z3RegexRewrites.fst`](Z3RegexRewrites.fst), [`Z3SeqAxioms.fst`](Z3SeqAxioms.fst), [`Z3SeqIndexOf.fst`](Z3SeqIndexOf.fst), [`Z3StoiTheory.fst`](Z3StoiTheory.fst) |
| Nested sequence extraction and concrete-string `indexof` width | [Extract/index audit](SEQ_REWRITER_EXTRACT_REPORT.md) | [`Z3SeqRewriterExtract.fst`](Z3SeqRewriterExtract.fst), [`Z3SeqRewriterIndex.fst`](Z3SeqRewriterIndex.fst) |
| Sequence equation solving and length coherence | [Sequence equation solver](SEQ_EQ_SOLVER_REPORT.md) | [`Z3SeqEqSolver.fst`](Z3SeqEqSolver.fst) |
| Regex AST information and nullable computation | [Regex/AST audit](REGEX_REPORT.md) | [`Z3RegexInfo.fst`](Z3RegexInfo.fst) |
| Floating-point rewriter and FP-to-BV converter | [Floating point](FPA_REPORT.md) | [`Z3FpaRewrites.fst`](Z3FpaRewrites.fst), [`Z3FpaConverter.fst`](Z3FpaConverter.fst) |
| FP rounding, conversions, NaNs, and model construction | [FP rounding follow-ups](FPA_ROUNDING_AUDIT.md) | [`Z3FpaRoundingAudit.fst`](Z3FpaRoundingAudit.fst), [`Z3FpaRoundingBits.fst`](Z3FpaRoundingBits.fst), [`Z3FpaZeroSign.fst`](Z3FpaZeroSign.fst), [`Z3FpaNanCongruence.fst`](Z3FpaNanCongruence.fst), [`Z3FpaNanWrap.fst`](Z3FpaNanWrap.fst), [`Z3FpaToRealSign.fst`](Z3FpaToRealSign.fst) |
| Arbitrary-precision MPF library | [MPF library](MPF_REPORT.md) | [`Z3MpfTheory.fst`](Z3MpfTheory.fst), [`Z3MpfRound.fst`](Z3MpfRound.fst), [`Z3MpfExact.fst`](Z3MpfExact.fst) |
| Denormal `round_to_integral` bug | [Round-to-integral audit](FP_ROUND_TO_INTEGRAL_REPORT.md) | [`Z3MpfRoundToIntegral.fst`](Z3MpfRoundToIntegral.fst) |
| Non-linear arithmetic solver lemmas | [NLA lemmas and real-analysis assumptions](NL_ARITH_REPORT.md) | [`Z3NlArith.fst`](Z3NlArith.fst) |
| Boolean and arithmetic rewriters | [Boolean/arithmetic rewriters](BOOL_ARITH_REWRITER_REPORT.md) | [`Z3BoolRewriter.fst`](Z3BoolRewriter.fst), [`Z3ArithRewriter.fst`](Z3ArithRewriter.fst), [`Z3ArithRewriterPower.fst`](Z3ArithRewriterPower.fst), [`Z3ArithRewriterCast.fst`](Z3ArithRewriterCast.fst), [`Z3ArithRewriterOrder.fst`](Z3ArithRewriterOrder.fst) |
| Bit-vector rewrites and overflow predicates | [Bit-vector rewriter](BV_REWRITER_REPORT.md) | [`Z3BvTheory.fst`](Z3BvTheory.fst), [`Z3BvRewriter.fst`](Z3BvRewriter.fst) |
| Datatype recognizers, accessors, updates, and equality | [Datatype rewriter](DATATYPE_REWRITER_REPORT.md) | [`Z3DatatypeTheory.fst`](Z3DatatypeTheory.fst) |
| Arrays, maps, and set operations | [Array rewriter](ARRAY_REWRITER_REPORT.md) | [`Z3ArrayTheory.fst`](Z3ArrayTheory.fst) |
| Theory-rewriter plugin survey and finite sets | [Other theory rewriters](OTHER_TH_REWRITER_REPORT.md) | [`Z3FiniteSetTheory.fst`](Z3FiniteSetTheory.fst) |
| Pseudo-Boolean coefficient transformations | [Pseudo-Boolean rewriter](PB_REWRITER_REPORT.md) | [`Z3PbTheory.fst`](Z3PbTheory.fst) |
| Recursive-function unfolding termination | [Recursive-function rewriter](RECFUN_REWRITER_REPORT.md) | [`Z3RecfunTheory.fst`](Z3RecfunTheory.fst) |

## Preprocessing and proof infrastructure

These reports audit transformations and proof-producing/checking C++
infrastructure. Their formalized inference rules are also useful to the
independent [proof-checking activity](PROOF_CHECKING.md).

| Subject | Report | Main modules |
|---|---|---|
| Quantifier distribution and substitution congruence; preprocessor survey | [Simplifiers](SIMPLIFIERS_REPORT.md) | [`Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst) |
| Monotone real-variable elimination, equisatisfiability, and well-formed model reconstruction | [Monotone elimination](ELIM_MONOTONE_REPORT.md) | [`Z3ElimMonotone.fst`](Z3ElimMonotone.fst) |
| Restoration of eliminated symbols and model-converter semantics | [Model reconstruction](MODEL_RECONSTRUCTION_REPORT.md) | [`Z3ModelReconstructionTheory.fst`](Z3ModelReconstructionTheory.fst) |
| Universal instantiation and array/set-indicator witnesses | [Leibniz simplifier](LEIBNIZ_SIMPLIFIER_REPORT.md) | [`Z3LeibnizTheory.fst`](Z3LeibnizTheory.fst) |
| `rewriter_def.h` proof production and proof smart constructors | [Rewriter proofs](PROOF_REWRITER_REPORT.md) | [`Z3ProofTheory.fst`](Z3ProofTheory.fst) |
| `smt_justification.cpp`, unit resolution, modus ponens, and elimination rules | [Proof justifications](PROOF_JUSTIFICATIONS_REPORT.md) | [`Z3ProofJustifications.fst`](Z3ProofJustifications.fst) |
| Preprocessing proof rules and pipeline composition | [Preprocessing proofs](PREPROCESSING_PROOFS_REPORT.md) | [`Z3PreprocessingProofTheory.fst`](Z3PreprocessingProofTheory.fst) |
| Proof production versus omission across rewriters, simplifiers, tactics, and SMT | [Proof-omission audit](PROOF_OMISSION_AUDIT.md) | Source catalogue and follow-up fixes; no separate theory module |
| Arithmetic proof-checker preconditions and Farkas certificates | [LRA Farkas report](LRA_FARKAS_REPORT.md) | [`Z3LraFarkasTheory.fst`](Z3LraFarkasTheory.fst) |

## Focused pull-request audits

| Change | Report | Proof module |
|---|---|---|
| #11159: RTN selection in real-to-float conversion | [RTN selector audit](PR_11159_RTN_SELECT_REPORT.md) | [`Z3FpaRTNSelect.fst`](Z3FpaRTNSelect.fst) |
| #11160: floating-point rounding for extreme integer exponents | [Extreme-exponent audit](PR_11160_MPF_EXTREME_EXP_REPORT.md) | [`Z3MpfExtremeExp.fst`](Z3MpfExtremeExp.fst) |
| #11162: array-theory give-up for uninterpreted uses of lambdas | [Array give-up audit](PR_11162_ARRAY_GIVEUP_REPORT.md) | [`Z3ArrayGiveUp.fst`](Z3ArrayGiveUp.fst) |
| #11164: ground-index array equality and MBQI | [Ground-index equality audit](PR_11164_ARRAY_GROUND_INDEX_EQ_REPORT.md) | [`Z3ArrayGroundIndexEq.fst`](Z3ArrayGroundIndexEq.fst) |
| #11165: provably out-of-range substring offsets | [Sequence extract audit](PR_11165_SEQ_EXTRACT_LENGTH_PRODUCT_REPORT.md) | [`Z3SeqExtractLengthProduct.fst`](Z3SeqExtractLengthProduct.fst) |
| #11180: exponentiation preprocessing, counterexamples to original bounds, and corrected real-exponent clauses | [Exponentiation audit and scope correction to the original NLA power proofs](PR_11180_POWER_REPORT.md) | [`Z3PowerPreprocessing.fst`](Z3PowerPreprocessing.fst), [`Z3PowerSaturation.fst`](Z3PowerSaturation.fst) |
| #11296 / issue #11295: branch-dependent store-index deduplication in array conflicts | [Array index-dependency audit](PR_11296_ARRAY_INDEX_DEPENDENCIES_REPORT.md) | [`Z3ArrayIndexDependencies.fst`](Z3ArrayIndexDependencies.fst) |

For proof-leaf tagging experiments and checker coverage measurements,
see [proof-checking experiments](PROOF_CHECKING.md#experiments-and-coverage).

# Verified Checking of Z3 Proofs

[Overview](README.md) | [Formalization](FORMALIZATION.md) | [Source audits](SOURCE_AUDITS.md)

## Purpose and guarantees

This activity develops verified checkers for Z3 proof steps and
certificates using the [formalized semantics and lemmas](FORMALIZATION.md).
It is independent of source auditing: the subject is a proof supplied as
input, not the correctness of the C++ implementation that produced it.

The development includes pure proof calculi, executable Pulse checkers,
semantic rewrite recognizers, direct native proof marshaling, and a
standalone OCaml executable accepting SMT-LIB. These cover different
fragments and should not be read as a claim that every Z3 proof is fully
checked. The in-memory Pulse developments are independent of the native
CLI and are not linked into that executable.

In particular, a well-formed equational derivation is semantically sound
only when its rewrite leaves are justified. Verified matchers discharge
recognized leaves using theory lemmas. Partial checking retains unmatched
leaves as explicit obligations; clausal rules classified as `Trusted`
likewise remain obligations, not automatically proved facts. Reports state
the assumptions and rule coverage of each path. The [arithmetic certificate
report](ARITHMETIC_CERTIFICATE_REPORT.md) documents a remaining
semantic-model contract inhabitance gap: the conditional semantic theorems
are not an unconditional end-to-end SMT-LIB soundness theorem.

## Modules and architecture

The following groups describe the main components, not a strict layering
of all imports.

| Component | Modules and role |
|---|---|
| Shared semantic foundation | [`Z3AstTheory.fst`](Z3AstTheory.fst) supplies expressions, well-formedness, and evaluation; [`Z3ValueTheory.fst`](Z3ValueTheory.fst) supplies concrete values and operator tags. |
| Equational calculus | [`Z3ProofTheory.fst`](Z3ProofTheory.fst) defines proof terms, `fact`/`facts_of`, leaf obligations, and soundness. [`Z3ProofJustifications.fst`](Z3ProofJustifications.fst) handles modus ponens, unit resolution, and elimination rules. |
| Preprocessing rules | [`Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst) and [`Z3PreprocessingProofTheory.fst`](Z3PreprocessingProofTheory.fst) formalize substitution, quantifier/connective laws, kernel rules, and pipeline composition. These rule families are not all implemented in Pulse. |
| Concrete interpretations | [`Z3InterpretedProofChecker.fst`](Z3InterpretedProofChecker.fst) combines semantic interpretations, with [`Z3ArrayInterp.fst`](Z3ArrayInterp.fst), [`Z3SeqInterp.fst`](Z3SeqInterp.fst), and [`Z3BvInterp.fst`](Z3BvInterp.fst) as theory companions. |
| Rewrite verification | [`Z3PatternMatchedProofChecker.fst`](Z3PatternMatchedProofChecker.fst) recognizes rewrite schemas and proves matching leaves sound; unmatched leaves can be collected as remaining obligations. |
| Rewrite synthesis | [`Z3ArrayEmbed.fst`](Z3ArrayEmbed.fst), [`Z3SeqEmbed.fst`](Z3SeqEmbed.fst), [`Z3BoolEmbed.fst`](Z3BoolEmbed.fst), [`Z3BvEmbed.fst`](Z3BvEmbed.fst), and [`Z3CoreEmbed.fst`](Z3CoreEmbed.fst) compute rewritten expressions via `apply_lemma_x`, `apply_lemmas`, and `is_rewrite`. This complements verification of a supplied expression pair. |
| Clausal/resolution calculus | [`Z3ResolutionProofTheory.fst`](Z3ResolutionProofTheory.fst) embeds equational proofs via `REq` and adds propositional/clausal rules, hypotheses, lemmas, and explicit trusted obligations. [`Z3ResolutionProofCheckerTests.fst`](Z3ResolutionProofCheckerTests.fst) exercises this calculus. |
| Full-DAG kernel | [`Z3UnifiedProof.fst`](Z3UnifiedProof.fst) uses checked premise judgments rather than synthetic rewrite/trusted leaves in the legacy recursive proof types. Supporting modules include [`Z3ObservationalEquality.fst`](Z3ObservationalEquality.fst), [`Z3Commutativity.fst`](Z3Commutativity.fst), [`Z3BooleanRewrite.fst`](Z3BooleanRewrite.fst), and [`Z3ArrayLemma.fst`](Z3ArrayLemma.fst). Observational equality is a separate judgment, not object-language equality. |
| Imperative checking | [`Z3PulseProofChecker.fst`](Z3PulseProofChecker.fst) and [`Z3PulseJustificationChecker.fst`](Z3PulseJustificationChecker.fst) implement equational and justification specifications in Pulse, including verified heap mutation and traversal counts; [`Z3PulseProofCheckerTests.fst`](Z3PulseProofCheckerTests.fst) includes acceptance/rejection examples. |
| LRA certificates | [`Z3LraFarkasTheory.fst`](Z3LraFarkasTheory.fst), [`Z3PulseLraChecker.fst`](Z3PulseLraChecker.fst), [`Z3PulseLraCheckerTests.fst`](Z3PulseLraCheckerTests.fst), and [`Z3PulseLraCheckerParsed.fst`](Z3PulseLraCheckerParsed.fst) provide a separate Farkas-certificate theory/checker path. |
| Integrated arithmetic certificates | [`Z3LinearArithmeticTheory.fst`](Z3LinearArithmeticTheory.fst), [`Z3LinearArithmeticAst.fst`](Z3LinearArithmeticAst.fst), and [`Z3LinearArithmeticEmbed.fst`](Z3LinearArithmeticEmbed.fst) provide exact polynomial operations, certificate checking, and the AST semantic bridge used by the unified kernel. |
| Typed proof documents | [`Z3ProofDocument.fst`](Z3ProofDocument.fst) performs transport-independent definition, scope, input, and topological validation; [`Z3ProofIndex.fst`](Z3ProofIndex.fst) supplies persistent caches. |
| Native Z3 integration | [`Z3Native.fsti`](Z3Native.fsti) and [`ocaml_runtime/Z3Native.ml`](ocaml_runtime/Z3Native.ml) expose foreign API views; [`Z3NativeProof.fst`](Z3NativeProof.fst) marshals expressions and proof DAGs directly into checker datatypes. |

## Reports

| Topic | Report |
|---|---|
| Equational proof calculus and soundness of smart constructors | [Rewriter proof theory](PROOF_REWRITER_REPORT.md) |
| Modus ponens, unit resolution, and elimination rules | [Proof justifications](PROOF_JUSTIFICATIONS_REPORT.md) |
| Preprocessing rules and composition | [Preprocessing proof theory](PREPROCESSING_PROOFS_REPORT.md) |
| Pulse implementations, concrete interpretations, verified matchers, and partial checking | [Pulse proof checker](PULSE_PROOF_CHECKER_REPORT.md) |
| Clausal/resolution rules and explicit trusted leaves | [Resolution checker](RESOLUTION_CHECKER_REPORT.md), [rule-by-rule scope](RESOLUTION_CHECKER_SCOPE.md) |
| Executable Farkas checking and real-proof parsing | [LRA Farkas checker](LRA_FARKAS_REPORT.md) |
| Exact arithmetic certificates in the unified kernel, coverage, and remaining formal limits | [Arithmetic certificate integration](ARITHMETIC_CERTIFICATE_REPORT.md) |
| Historical JSON interface, now removed | [Archived JSON interface](JSON_PROOF_CHECKER_REPORT.md) |
| Extraction, runtime shim, native executable, and measurements | [Standalone OCaml checker](OCAML_CHECKER_REPORT.md) |

Some reports also examine Z3's source implementation of the corresponding
rules. Those source-audit results are distinct from the semantic guarantees
of checking an input proof.

## Extraction and execution

The executable reads SMT-LIB, solves with statically linked Z3 and its
official OCaml bindings, and checks the resulting proof in one process.
There is no Python exporter, JSON document, external solver process, or
runtime F* invocation in this path.

From this directory, in a Windows C++20 developer PowerShell:

```powershell
.\tools\build_ocaml_checker.ps1 -RunTests
'(declare-const p Bool)(assert p)(assert (not p))' |
  wsl -e bash -c '~/z3checker/checker --stats'
```

Every build first builds and installs Windows Z3 from this checkout.
F* verification, Pulse tests, and extraction explicitly use the installed
`build\install\bin\z3.exe` and its detected `--z3version`, without disabling
version checks. `-Z3WindowsBuildDir` and `-Z3InstallDir` change the build
directory and installation prefix; `-CacheDir` selects the proof cache.
The WSL producer and official OCaml bindings are also rebuilt and installed
before linking from that installation. `-RunTests` verifies the F*/Pulse
regressions and runs native bridge and CLI tests after these installation
steps. See the [toolchain instructions](OCAML_CHECKER_REPORT.md).

[`Z3NativeProof.fst`](Z3NativeProof.fst) uses native AST identities for
expression/sort caches; declaration caches also include application arity.
Worklists traverse shared expression/proof DAGs without recursively
unfolding them, and repeated expressions reuse allocated algebraic values.
Native owners remain alive for the cache lifetime so Z3 cannot recycle
cached identities.

The build script links extracted code with static Z3, its official OCaml
bindings, Zarith, and the handwritten [`ocaml_runtime`](ocaml_runtime)
shim. Native interoperability, parsing/API views, ownership, extraction,
the compiler, and runtime remain trust boundaries; no theorem proves
correspondence of the foreign API to Z3's semantics.

An obligation-free closed false root produces `ACCEPT`; unsupported leaves
remain `PARTIAL`, and unsupported judgment shapes reject rather than being
relabeled or trusted. See the [executable report](OCAML_CHECKER_REPORT.md)
for prerequisites, exit codes, statistics, timeouts, and formal limits.

[`tools/test_native_checker.py`](tools/test_native_checker.py) and
[`tools/test_native_bridge.ml`](tools/test_native_bridge.ml) exercise the
direct/native path; `tools/test_*.smt2` remain input fixtures.
The old exporter, JSON parser/decoders, compatibility CLI, and generated
F* proof snapshots have been removed. The [JSON report](JSON_PROOF_CHECKER_REPORT.md)
describes only that historical implementation.
[`tools/parse_farkas.py`](tools/parse_farkas.py) handles the separate LRA
certificate examples. Typecheck individual F* modules using the command
in the [overview](README.md).

## Experiments and coverage

| Experiment | Report and tools |
|---|---|
| Historical QF_AX/QF_UF proof production, rewrite-matcher coverage, timing, and follow-up matchers | [Archived benchmark report](QF_AX_QF_UF_BENCHMARK_REPORT.md); [`tools/analyze_benchmarks.py`](tools/analyze_benchmarks.py) remains for archived results; the exporter-dependent runner was removed. |
| Nine-logic SMT-LIB cross-cut, native coverage extensions, and producer updates | [Current cross-cut](SMTLIB_CROSSCUT_REPORT.md) includes the direct native interface; [arithmetic integration results](ARITHMETIC_CERTIFICATE_REPORT.md) preserve the earlier evaluation. |
| Occurrence coverage of clausal proof rules, distinguishing proved rules from trusted obligations | [Resolution report](RESOLUTION_CHECKER_REPORT.md) and [scope](RESOLUTION_CHECKER_SCOPE.md); [`tools/proof_rule_coverage.py`](tools/proof_rule_coverage.py) |
| Experimental rewrite-leaf tagging | [Rewrite-rule tags report](REWRITE_RULE_TAGS_REPORT.md); [`Z3RewriteRuleTags.fst`](Z3RewriteRuleTags.fst), [`tools/parse_rewrite_tags.py`](tools/parse_rewrite_tags.py) |

Rule-vocabulary coverage is not the same as complete semantic checking:
trusted rules and unmatched leaves must still be accounted for. Benchmark
reports record point-in-time measurements and follow-up results.

The rewrite-tagging call site was **reverted from master**. Its report and
F* lemmas document an experiment, not current proof-production behavior;
the captured local benchmark proofs are not reproducible with current
master's tagging behavior.

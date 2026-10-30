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
report](ARITHMETIC_CERTIFICATE_REPORT.md) documents a remaining legacy
semantic-model contract inhabitance gap: the conditional semantic theorems
are not an unconditional end-to-end SMT-LIB soundness theorem. Native
datatype documents instead use the contextual, sort-indexed kernel below;
that path does not assume the legacy model contracts. For the default
kernel, `Z3CoreKernel.lemma_core_check_node_sound` proves the Boolean,
equality and congruence rules (and bounded bit-vector steps) from the
inhabited typed contract `Z3CoreModel.core_model`; every other rule of that
kernel still rests on the legacy `Z3UnifiedProof.model_sound`, which has no
model.

## Modules and architecture

The following groups describe the main components, not a strict layering
of all imports.

| Component | Modules and role |
|---|---|
| Shared semantic foundation | [`Z3AstTheory.fst`](Z3AstTheory.fst) supplies expressions, well-formedness, and evaluation; [`Z3ValueTheory.fst`](Z3ValueTheory.fst) supplies concrete values and operator tags. |
| Equational calculus | [`Z3ProofTheory.fst`](Z3ProofTheory.fst) defines proof terms, `fact`/`facts_of`, leaf obligations, and soundness. [`Z3ProofJustifications.fst`](Z3ProofJustifications.fst) handles modus ponens, unit resolution, and elimination rules. |
| Preprocessing rules | [`Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst) and [`Z3PreprocessingProofTheory.fst`](Z3PreprocessingProofTheory.fst) formalize substitution, quantifier/connective laws, kernel rules, and pipeline composition. These rule families are not all implemented in Pulse. |
| Concrete interpretations | [`Z3InterpretedProofChecker.fst`](Z3InterpretedProofChecker.fst) combines semantic interpretations, with [`Z3ArrayInterp.fst`](Z3ArrayInterp.fst), [`Z3SeqInterp.fst`](Z3SeqInterp.fst), and [`Z3BvInterp.fst`](Z3BvInterp.fst) as theory companions. |
| Sort-indexed datatype model | [`Z3DatatypeValue.fst`](Z3DatatypeValue.fst) builds finite well-sorted constructor trees over arbitrary sort-indexed base carriers and derives datatype laws, typed environments, and sort-preserving evaluation. [`Z3DatatypeSignature.fst`](Z3DatatypeSignature.fst) validates native schemas and supplies canonical constructor/tester/selector dispatch with arbitrary argument-dependent wrong-selector interpretations and a total interpretation witness. |
| Typed canonical core model | [`Z3CoreModel.fst`](Z3CoreModel.fst) states `core_model i dom`: model-owned sort domains (typing fixes only `Bool`, to Boolean values, but integer `+`/`*` must return `VInt`, so the Int domain contains those images, and canonical equality must decide value identity wherever it is applied), environments typed against a scope of sorts, application and binder typing, the connectives keyed only by the typed predicates of [`Z3CanonicalOps.fst`](Z3CanonicalOps.fst), equality required to decide value identity only on scoped terms under typed environments, integer `+`/`*`, and the ground bit-vector contracts. `lemma_typed_eval` proves that every scoped term, open or under binders, takes a value of its sort. `lemma_core_inhabited` gives a hypothesis-free model: the standard ground interpretation with integer arithmetic. [`Z3CoreKernel.fst`](Z3CoreKernel.fst) proves, for every node for which the default kernel's `check_node_with_context` returns `Some` by assertion, hypothesis, lemma, reflexivity, symmetry, transitivity, congruence, commutativity, `iff~`, `mp`, `mp~`, unit resolution, and/not-or elimination or iff-true/false, or as a theory lemma or rewrite whose conclusion the bounded bit-vector evaluator decides, that the returned checked fact holds in every core model under every environment typed for a scope its judgments and premises are scoped in, given that its premises and the assertions hold. `Some` is not zero obligations: theory-lemma and rewrite nodes (which may have premises) can be returned with a pending obligation, even when false, and their guarantee comes from the evaluator condition in `core_rule`. It is a per-node theorem; no document-level theorem exists, and no F* lemma establishes the scope of document entries (ground-table documents rely on the native side listing every subexpression). The kernel's Boolean dispatch (`Z3ProofTheory.is_not`, resolution complements and clauses, `mp`, elimination rules, and the quantifier, finite-field, integer-division and factoring recognizers) accepts only canonical connectives. The seven connective conjuncts of the legacy `model_sound` are keyed the same way, but every core model satisfies only the six non-equality contracts and its typed canonical equality, not necessarily the re-keyed untyped `eq_sound` (`Z3CoreModelTests.core_without_untyped_equality`). Closed instances of the former name/tag and datatype-name clashes take the values of their own theory in the witness core model. `model_sound` still has no model: its open-environment, untyped binder and array/numeral obstructions remain. Quantifier truth, lambda/array semantics, real arithmetic, datatypes and finite fields are not part of `core_model`; quantifier and binder rules, definitions, the other rewrite and theory checkers and Skolemization are not covered. [`Z3CoreModelTests.fst`](Z3CoreModelTests.fst) instantiates the theorem on accepted closed and open-scope nodes with premises satisfiable in witness core models, shows that the typed environment and `core_rule` are needed, rejects look-alike connectives, and records two legacy obstructions as finite clause instances with satisfiable drop-one controls: the `array_model` store clause and the `numeric_operators` numeral clauses are jointly unsatisfiable at the closed term `(store a 0 1/2)`, and every model of the untyped quantifier contract with `arithmetic_model` and `eq_sound`, if one exists, falsifies the valid `forall x:Int. x + 0 = x`. |
| Ghost semantics and classical standard model | The interpretation fields of [`Z3AstTheory.fst`](Z3AstTheory.fst) and `eval` are ghost (`GTot`); the production `value` type, its `bool` and `Tot` array payloads, and every executable checker function are unchanged, and F* rejects ghost results in executable code. Proofs that run an executable evaluator on a ghost valuation use a proved-equal ghost twin or an executable valuation computed in a ghost context (`Z3BoundedBoolEquiv.geval`, `freeze`). [`Z3GhostStandardModel.fst`](Z3GhostStandardModel.fst) builds, with `FStar.IndefiniteDescription.strong_excluded_middle` and no added axiom or hypothesis, one interpretation that is a `Z3CoreModel.core_model` (with the ground bit-vector contracts), satisfies the legacy untyped canonical `eq_sound` on every value including arrays, gives `forall`/`exists` their classical truth over exactly the value lists typed for the reversed binder list, has standard Bool/Int/`(Array Int Int)`/bit-vector domains and computes integer numerals. [`Z3GhostStandardModelTests.fst`](Z3GhostStandardModelTests.fst) evaluates valid, mutated, satisfiable and unsatisfiable Int formulas, `[Int; Bool]` binders and their swapped form, numerals, array equalities and an array quantifier, with mutation controls. Lambdas (opaque values), Real, datatypes, finite fields, sequences and nested arrays are not modeled; the untyped `boolean_model` and hence `model_sound` still have no model; apart from quantifier instantiation (next row), no rule outside `core_rule` and no document theorem rests on this model yet. Development code that computes with expression values uses the executable [`Z3AstTotEval.fst`](Z3AstTotEval.fst), equal to ghost `eval` on quantifier-free expressions. |
| Typed quantifier instantiation | [`Z3TypedQuantifier.fst`](Z3TypedQuantifier.fst) states `quantifier_model i dom`: one interpretation and one domain assignment that satisfy `core_model`, typed `forall`/`exists` over exactly the value lists typed by the reversed binder list, and quantifier extensionality. `core_model` itself is unchanged. `Z3GhostStandardModel.lemma_quantifier_model` proves that the classical model satisfies all three jointly, with the same interpretation, domains and projection; extensionality is proved from its quantifier field, opaque lambda branch included, and is not a lambda (beta) law. [`Z3QuantifierKernel.fst`](Z3QuantifierKernel.fst) proves the unchanged executable decision `Z3QuantifierInstantiation.check` sound in every such model, under every environment: the evaluated closed arguments are typed by `L.rev bs`, the `forall` is eliminated at exactly those values, and the existing capture-avoiding substitution theorem relates the body there to the instance. For an instantiation node, `check_node_with_context` returns `Some` with pending obligation 0 exactly when `check_step` accepts it, and with pending 1 otherwise, also for false conclusions and always for `Equal` conclusions; observational conclusions and nodes with premises are rejected. The node theorem requires pending 0 and gives the returned fact, which has no hypotheses. `lemma_typed_check_node_sound` extends the core theorem to core rules plus checked instantiations. The legacy `lemma_check_sound` still requires the untyped `boolean_model` and `forall_elimination_model`, has no model, and is not used. [`Z3QuantifierKernelTests.fst`](Z3QuantifierKernelTests.fst) computes accepted and rejected actual nodes (Int, Bool, `[Int; Bool]` and two Int binders, nested binders, `BV2`) and checks them in the classical model: instances follow from true quantifiers, several rejected nodes returned with pending 1 have false conclusions, capture, shadowing, unscoped, wrong-order, wrong-sort and wrong-arity mutations are not checked, and the untyped elimination contract fails there while the typed one holds. Quantifier introduction and the other binder rules, definitions, Skolemization and the document layer still rest on `model_sound`. |
| Contextual datatype kernel | [`Z3SortedSemantics.fst`](Z3SortedSemantics.fst), [`Z3SortedDatatype.fst`](Z3SortedDatatype.fst), and [`Z3SortedProof.fst`](Z3SortedProof.fst) check native datatype proof DAGs against one checked schema and derive zero-obligation unsatisfiability of the original assertions in the typed interpretation. Native documents with datatype metadata use this path without a legacy fallback; [coverage and theory boundaries](OCAML_CHECKER_REPORT.md#concrete-sort-indexed-datatype-semantics) remain explicit. |
| Rewrite verification | [`Z3PatternMatchedProofChecker.fst`](Z3PatternMatchedProofChecker.fst) recognizes rewrite schemas and proves matching leaves sound; unmatched leaves can be collected as remaining obligations. |
| Rewrite synthesis | [`Z3ArrayEmbed.fst`](Z3ArrayEmbed.fst), [`Z3SeqEmbed.fst`](Z3SeqEmbed.fst), [`Z3BoolEmbed.fst`](Z3BoolEmbed.fst), [`Z3BvEmbed.fst`](Z3BvEmbed.fst), and [`Z3CoreEmbed.fst`](Z3CoreEmbed.fst) compute rewritten expressions via `apply_lemma_x`, `apply_lemmas`, and `is_rewrite`. This complements verification of a supplied expression pair. |
| Clausal/resolution calculus | [`Z3ResolutionProofTheory.fst`](Z3ResolutionProofTheory.fst) embeds equational proofs via `REq` and adds propositional/clausal rules, hypotheses, lemmas, and explicit trusted obligations. [`Z3ResolutionProofCheckerTests.fst`](Z3ResolutionProofCheckerTests.fst) exercises this calculus. |
| Clause-trail elaboration | [`Z3ClauseProof.fst`](Z3ClauseProof.fst) performs reverse unit propagation over active clauses and emits ordinary hypothesis, unit-resolution, and lemma steps. The existing document kernel checks these steps; literal IDs and propagation results are not trusted. Deletions remove one matching active clause. [`Z3ClauseProofTests.fst`](Z3ClauseProofTests.fst) covers positive and negative elaborations. |
| Full-DAG kernel | [`Z3UnifiedProof.fst`](Z3UnifiedProof.fst) uses checked premise judgments rather than synthetic rewrite/trusted leaves in the legacy recursive proof types. Supporting modules include [`Z3ObservationalEquality.fst`](Z3ObservationalEquality.fst), [`Z3Commutativity.fst`](Z3Commutativity.fst), [`Z3BooleanRewrite.fst`](Z3BooleanRewrite.fst), and [`Z3ArrayLemma.fst`](Z3ArrayLemma.fst). Observational equality is a separate judgment, not object-language equality. |
| Destructive equality resolution | [`Z3QuantifierDer.fst`](Z3QuantifierDer.fst) verifies guarded `forall`/`exists` variable elimination, with an occurs check, binding-sort checks, and capture-safe substitution. Closed original input facts may be used in binder certificates because their truth is environment-independent; definition expansion is applied consistently to parent conclusions and hidden certificates. |
| Skolemization | [`Z3Skolemization.fst`](Z3Skolemization.fst) represents each binding block by a joint Hilbert-choice tuple and its fresh function symbols by tuple coordinates. It verifies substitution, dependencies, acyclic interpretation extension, and preservation of fresh original inputs. A block none of whose variables occurs in its body needs no choice tuple and is checked structurally by `vacuous`. The unified kernel checks `sk` observations in this chosen interpretation, not as arbitrary fixed-model equalities; choice and the existing semantic-model contract remain explicit hypotheses. |
| Binder certificates and instantiation | The unified kernel checks hidden `proof-bind` DAGs using an all-environments invariant before lifting body relations through `forall`, `exists`, or `lambda`. [`Z3BinderSubstitution.fst`](Z3BinderSubstitution.fst) proves capture-avoiding substitution beneath nested binders and arbitrary unused-variable thinning; [`Z3QuantifierInstantiation.fst`](Z3QuantifierInstantiation.fst) checks native substitution parameters against this foundation. [`Z3QuantifierNnf.fst`](Z3QuantifierNnf.fst) derives quantifier duality. See [coverage and limits](OCAML_CHECKER_REPORT.md#binder-and-quantifier-proof-support). |
| Quantifier pulling | [`Z3QuantifierPull.fst`](Z3QuantifierPull.fst) derives same-kind binder flattening, quantifier negation, and capture-safe n-ary `and`/`or` pulling from the existing quantifier semantics. The unified `pull-quant` rule also checks open formulas in binder certificates; unsupported shapes or exhausted normalization fuel retain obligations. |
| Quantifier reductions and lambdas | [`Z3QuantifierReduce.fst`](Z3QuantifierReduce.fst) checks distribution and binder-aware endpoint equivalence; [`Z3DestructiveEquality.fst`](Z3DestructiveEquality.fst) checks guarded equality elimination; [`Z3LambdaRewrite.fst`](Z3LambdaRewrite.fst) checks extensionality and capture-safe beta/constant-array rewriting under explicit lambda interpretation contracts. |
| Shared theory normalization | [`Z3TheoryNormalize.fst`](Z3TheoryNormalize.fst) combines proved local rewrites with bottom-up congruence for rewrites, NNF, `def-axiom`, and actual-premise `th-lemma` implications. Newly generated terms are normalized again with decreasing fuel, including nested constructor field equalities. Bounded constructor-equality propagation rewrites actual premises and conclusions outside binders. [`Z3BvLemma.fst`](Z3BvLemma.fst) and [`Z3DatatypeLemma.fst`](Z3DatatypeLemma.fst) add native bit-vector/datatype semantic bridges. Coverage is bounded and conditional, not general bit-blasting or datatype theory completeness. |
| Imperative checking | [`Z3PulseProofChecker.fst`](Z3PulseProofChecker.fst) and [`Z3PulseJustificationChecker.fst`](Z3PulseJustificationChecker.fst) implement equational and justification specifications in Pulse, including verified heap mutation and traversal counts; [`Z3PulseProofCheckerTests.fst`](Z3PulseProofCheckerTests.fst) includes acceptance/rejection examples. |
| LRA certificates | [`Z3LraFarkasTheory.fst`](Z3LraFarkasTheory.fst), [`Z3PulseLraChecker.fst`](Z3PulseLraChecker.fst), [`Z3PulseLraCheckerTests.fst`](Z3PulseLraCheckerTests.fst), and [`Z3PulseLraCheckerParsed.fst`](Z3PulseLraCheckerParsed.fst) provide a separate Farkas-certificate theory/checker path. |
| Integrated arithmetic certificates | [`Z3LinearArithmeticTheory.fst`](Z3LinearArithmeticTheory.fst), [`Z3LinearArithmeticAst.fst`](Z3LinearArithmeticAst.fst), and [`Z3LinearArithmeticEmbed.fst`](Z3LinearArithmeticEmbed.fst) provide exact polynomial operations, certificate checking, and the AST semantic bridge used by the unified kernel. |
| Factored sign rewrites | [`Z3ArithmeticFactor.fst`](Z3ArithmeticFactor.fst) checks the arithmetic rewriter's `p = 0 ~> f = 0 or g = 0`, `p >= 0 ~> ((f >= 0) = (g >= 0)) or (f = 0 or g = 0)`, and negated `p <= 0` steps over Int or Real. It requires `p` and `f * g` to have the same integer-coefficient polynomial normal form, computed with the [`Z3NlaLemma.fst`](Z3NlaLemma.fst) multiplication over opaque atoms, and non-constant factors. Division, `to_real`, and uninterpreted terms stay atoms, so no field law is used. Soundness needs only the existing `numeric_model` and Boolean contracts. [`Z3ArithmeticFactorTests.fst`](Z3ArithmeticFactorTests.fst) decides closed positive and negative instances. |
| Conditional comparison rewrites | [`Z3ConditionalRewrite.fst`](Z3ConditionalRewrite.fst) checks rewrites with conditional subterms by replacing the first guard with `true` and `false` on both sides outside binders and folding each branch. Besides conditionals with literal guards and constant equations, the fold decides comparisons whose linear normal form is constant (such as `(>= 0 1)`) with [`Z3ArithmeticRewrite.fst`](Z3ArithmeticRewrite.fst), and drops literal arguments of `and`/`or` when [`Z3BooleanRewrite.fst`](Z3BooleanRewrite.fst) confirms the result. This covers the arithmetic rewriter's lifting of a numeral-branch conditional out of a numeric comparison, such as `(ite c 0 x) >= 1 ~> (not c) and (x >= 1)`, also after a numeral addend was moved across. Soundness uses only the existing numeric and Boolean model contracts. |
| Bit-vector extraction rewrites | [`Z3BvExtract.fst`](Z3BvExtract.fst) checks the bit-vector rewriter's steps that move an extraction into its argument: `((_ extract h 0) (bvadd x1 ... xn))` and `bvmul` to the sum or product of the extracted low bits, `((_ extract h l) (ite c t e))` to `(ite c ((_ extract h l) t) ((_ extract h l) e))` with the same guard, and `((_ extract h l) (concat x y))` to the bits of `y`, the bits of `x`, or the concatenation of the low bits of `x` and the high bits of `y`, keeping an argument whose bits are all taken. Sums and products are distributed only for `l = 0`, since higher bits depend on carries. Only binary concatenations are split. Inner extractions may be composed with an extraction argument, as `mk_extract_proc` does. Widths come from the native declarations and are compared as integers; both sides must be closed. Soundness uses only the existing `bv_model` and `term_ite_sound` contracts. |
| Bounded bit-vector evaluation | [`Z3BvExhaustive.fst`](Z3BvExhaustive.fst) decides premise-free `th-lemma` and `rewrite` steps by enumerating values for structurally identified BV leaves. The fragment includes canonical Boolean connectives and equality, unsigned BV comparisons, numerals, binary `concat`, `extract`, `zero_extend` and binary `bvadd`. Connectives require the typed name, tag, domain, range and parameter predicates of [`Z3CanonicalOps.fst`](Z3CanonicalOps.fst); datatype declarations with connective names are not connectives. BV operations use the checked [`Z3BvLemma.fst`](Z3BvLemma.fst) recognizers. Unsupported Boolean terms and malformed evaluated declarations stay pending. The conclusion must be closed and ground, with at most 512 unfolded-tree occurrences and at most 12 total leaf bits, hence at most 4096 assignments. Leaves are enumerated, not assigned a presumed constant value. [`Z3StandardModel.fst`](Z3StandardModel.fst) proves that the ground Boolean/BV contracts have models: canonical connectives and BV-tagged heads with matching parameters are computed, and remaining heads use an arbitrary function of their argument values, with results coerced to their range sorts. This witness has no hypotheses. The direct evaluator lemmas prove `valid` and `equivalent` sound in every ground model, with standard-model corollaries. The legacy kernel theorem reaches them only through the uninhabited global `model_sound`; `Z3CoreKernel` instead proves theory-lemma and rewrite nodes whose conclusion this evaluator decides sound from the inhabited `Z3CoreModel.core_model`. No document-level theorem is claimed. Arrays, arithmetic, datatypes, finite fields, quantifiers, open terms and projection widths above 4096 are outside this model's theory claims. [`Z3BvExhaustiveTests.fst`](Z3BvExhaustiveTests.fst) covers accepted and rejected steps, bounds, malformed declarations, name/tag clashes, datatype names, witness values and countermodels. |
| Modular bit-vector sums | [`Z3BvAddNormalize.fst`](Z3BvAddNormalize.fst) decides premise-free `rewrite` steps `a = b` between sums of one bit-vector sort `BV<w>`: each side is read as the sum of its numerals modulo `2^w` and the sequence of its atoms (any other closed term of that sort, kept opaque), through nested binary and n-ary `bvadd` recognized by declaration kind, width parameter and argument sorts with the [`Z3BvExtract.fst`](Z3BvExtract.fst) and [`Z3BvLemma.fst`](Z3BvLemma.fst) recognizers. Both sides must have the same total modulo `2^w` and the same atoms in the same order, so `bvadd(bvadd(c1, t), c2) = bvadd(c3, t)` is decided for any `t` of any width up to 4096, with wrap-around and cancellation to the bare atom. Atoms are never evaluated, reordered or merged; a malformed numeral or sum declaration is neither read nor an atom; the tree has at most 512 occurrences and both sides are closed. Soundness is an induction on the sum using only the existing `bv_model` conjuncts for numerals, `operation` and `nary_operation` (through `model_sound`). [`Z3BvAddNormalizeTests.fst`](Z3BvAddNormalizeTests.fst) decides closed positive and negative instances (widths 1, 8, 32 and 66, wrap-around, cancellation, wrong totals, dropped, extra, replaced, reordered and merged atoms, sorts, malformed declarations, the size bound). |
| Finite-field rewrites | [`Z3FiniteFieldLemma.fst`](Z3FiniteFieldLemma.fst) decides `rewrite` steps over `FF<p>` terms by normalizing both sides to sparse polynomials modulo `p` (atoms are the maximal non-field subterms) and by rescaling equalities with checked factors. It uses only commutative-ring laws, never assumes `p` is prime, and relies on the explicit `ff_model` hypothesis conjoined into `normalization_model`. The native bridge marshals `FiniteField p` sorts as `FF<p>` and `ff` numerals/operators with `decl_kind` 300-304 (see [`FINITE_FIELD_REPORT.md`](FINITE_FIELD_REPORT.md)). Finite-field `th-lemma` steps are decided by bounded exhaustive evaluation or, for any modulus, by replaying the recorded `ff-pac` ideal certificate in [`Z3FiniteFieldPac.fst`](Z3FiniteFieldPac.fst) when it uses only definitions and positive premises; certificates that need the inverse witness of a disequality remain unmet. |
| Integer division | [`Z3IntegerDivision.fst`](Z3IntegerDivision.fst) checks guarded quotient/remainder identities, remainder bounds, and common-factor cancellation with positive numeral divisors. Native integer `div` and `mod` have distinct interpreted tags. Soundness assumes their standard nonzero-divisor semantics; division by zero remains unspecified. [`Z3ArithmeticRewrite.fst`](Z3ArithmeticRewrite.fst) also checks binary-sum product expansion over integers and reals. |
| Gomory cuts | [`Z3LpGomory.fst`](Z3LpGomory.fst) reconstructs integer-split candidates from native LP row/bound data and requires both branches to derive the actual cut through the existing Farkas checker. Split exhaustiveness follows from integer semantics; no LP row, bound metadata, or foreign checker verdict is assumed. |
| Integer rounding cuts | [`Z3LpIntegerCut.fst`](Z3LpIntegerCut.fst) refutes a set of premises by Chvátal-Gomory rounding followed by a Farkas combination. A certificate is a list of rounded bounds `L <= k` and a final weight vector. Every bound and the final refutation are replayed through [`Z3LinearArithmeticAst.check`](Z3LinearArithmeticAst.fst) against the actual premise ASTs and the earlier bounds only, with one weight per premise or earlier bound plus one for the negated bound; that check rounds a strict inequality over Int terms (`a < b` to `a + 1 <= b`), so the rounding is checked, not trusted, and is unavailable for Real terms. Soundness uses only the existing `numeric_model` and Boolean contracts, exactly like [`Z3LpGomory.fst`](Z3LpGomory.fst). The untrusted candidate search handles the conclusion `false` only: it substitutes variables fixed or equated by unit-coefficient equalities, rounds each non-strict row whose atoms are all Int and whose coefficients have a common factor `g >= 2` not dividing the constant, and finds the final weights by Fourier-Motzkin elimination (cheapest atom first, one-sided atoms dropped). Every cap fails closed to a pending obligation: at most 32 premises, 8 bounds of at most 64 terms, 128 rows, 64 eliminations, 4096 row pairs in total, and magnitudes at most 2^128 for every coefficient, constant, denominator and weight, checked on the input rows and after every substitution or elimination. Systems that need a genuine Gomory or branching cut stay pending. [`Z3LpIntegerCutTests.fst`](Z3LpIntegerCutTests.fst) decides closed positive and negative certificates (too-strong and too-weak rounding, zero or negative divisor weights, non-cancelling rational weights, wrong weight lengths, forward references, permuted premises, Real sorts). |
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
`--sorted-core` opts non-datatype documents into the existing sort-indexed
kernel as well. This mode has no legacy fallback: Boolean and EUF proofs
can certify under the inhabited typed interpretation, while unsupported
arithmetic, array, binder, and definition steps retain obligations or reject.
It is an incremental semantic-migration path, not a complete combined
SMT-LIB theory model. Statistics identify it as `semantics=sorted-core`;
datatype documents continue to use `semantics=sorted-datatype`.
`--interactive` instead evaluates complete stdin commands on a persistent
context and checks each UNSAT proof through `Z3_set_proof_check_callback`,
preserving push/pop, assumptions, and queries. Certification reports are
SMT-LIB comments, not replacements for the solver's result; only
`proof-check ACCEPT` is an obligation-free check. See the
[interactive protocol](OCAML_CHECKER_REPORT.md#interactive-certifying-smt-lib-session).

### Clausal SMT search proofs

With `proof=true`, set `smt.clause_proof=true` before initializing SMT
search to replace learned-clause proof DAG reconstruction with a typed
`proof-trail` of additions and deletions. The default is standard proofs.
Preprocessing proofs and local theory certificates remain enabled; this is
not an option to disable all proof AST allocation. Changing modes on an
already initialized incremental solver requires resetting it first.

Run `checker --clause-proofs` (also supported with `--interactive`) to select
this producer mode. Input and theory additions carry ordinary certificates;
learned clauses without certificates must pass reverse unit propagation.
The elaborator discharges the negated target literals and prunes unused
history before checking the ordinary document. Original assertion membership,
root closure, and all selected inference steps are still checked. Missing
or unsupported theory certificates cannot produce an obligation-free
`ACCEPT`; they remain explicit obligations or fail checking.

Resolution recognizes `true` and `false` as complementary literals as well
as explicit negation. The semantic proofs require the standard Boolean
constant interpretations. Native `true-axiom` leaves are checked as
tautologies, not accepted solely because of their rule name. These
extensions do not certify arbitrary NLSAT assumptions or nonlinear theory
lemmas: unsupported arithmetic inferences retain their obligations.

[`tools/test_native_checker.py`](tools/test_native_checker.py) and
[`tools/test_native_bridge.ml`](tools/test_native_bridge.ml) exercise the
direct/native path; `tools/test_*.smt2` remain input fixtures.
The old exporter, JSON parser/decoders, compatibility CLI, and generated
F* proof snapshots have been removed. The [JSON report](JSON_PROOF_CHECKER_REPORT.md)
describes only that historical implementation.
[`tools/parse_farkas.py`](tools/parse_farkas.py) handles the separate LRA
certificate examples. Typecheck individual F* modules using the command
in the [overview](README.md).

## Native LP inference certificates

Arithmetic equality propagation can also be checked without producer-supplied
weights. `Z3LpReplay.fst` constructs the two non-strict bounds of the actual
numeric equality conclusion. Bounded Fourier-Motzkin synthesis in
`Z3LinearArithmeticAst.fst` proposes exact Farkas weights for each bound;
the existing verified checker independently replays both certificates
against the original premises before the equality is derived. Synthesis
is limited to 32 literals, 16 elimination rounds, and 128 rows. Unsupported
inputs or exhausted search retain an obligation. Integer strict-bound
strengthening is not applied to reals, and no arithmetic hint or native
solver verdict substitutes for either replay.

Triangle-equality clauses accept either order of the opposing bounds,
including reversed equality operands. Both orientations use the existing
proved equality-to-bounds equivalence. These extensions retain the legacy
numeric-model limitations described above; they do not repair that model.

With proofs enabled, `theory_lra` exports supported
`lp::evidence_manager::proof_expression` derivations as native proof DAGs,
not just their flattened dependency sets. The arithmetic `th-lemma` hints
are `lp-input`, `lp-linear`, `lp-integer-tighten`, `lp-integer-lattice`,
`lp-gomory`, `lp-monomial-substitute`, `lp-monomial-interval`, and
`lp-discharge`. Each node carries its step index and has a shared
`lp-context` node as its first parent. Discharge additionally uses an
ordinary native `lemma` node to close the temporary hypothesis.

The context proves only `true`. Its declaration parameters carry an
explicit, versioned certificate; they do not assert its input facts.
The C++ checker replays the arithmetic rules, validates variable and
monomial definitions against the actual bound ASTs, and checks every
native inference's premise and conclusion formulas. Export rejects
unmatched open inputs, including recycled probe constraints, rather than
turning them into axioms. Unsupported evidence keeps an explicit
unsupported hint (or the existing independently checked linear Farkas
certificate), not a fabricated derivation.

External consumers can obtain the typed parameters through the native
declaration-parameter APIs. The version-1 context parameter layout, after
`arith, lp-context`, is:

| Field | Encoding |
|---|---|
| Header | Version `1`, variable count. |
| Each variable | Native expression AST, integer flag, linear definition length, then `(rational coefficient, stable variable index)` pairs. |
| Monomials | Count, then each column index, factor count, and factor indices. |
| Steps | Count, then each rule tag, conclusion fact, input index, assumption step, recipe ID, equation fact, pivot, monomial definition index, source, divisor, premise count, `(step, coefficient)` pairs, bound count, and `(column, lower-premise-position, upper-premise-position)` triples. |
| Root | Root step index. |

A fact contains the relation tag (`0` = `<=`, `1` = `<`, `2` = `=`,
`3` = `>`, `4` = `>=`), contradiction flag, rational right-hand side,
infinitesimal component (required to be zero), and a length-prefixed
linear left-hand side. Rule tags follow the hint order above, starting at
zero. Absent indices are `4294967295`. Premise references are topological;
used variable and rule-data references are range checked.
An `lp-linear` node also supplies local rational weights, after its
step index: one per arithmetic parent and, for a non-contradiction
conclusion, one for that conclusion. These account for denominator
clearing when native integer formulas are emitted.

[`scripts/check_lp_proof.py`](../scripts/check_lp_proof.py) independently
replays all these arithmetic rules with Python exact rational and ring
arithmetic. `check_lp_nodes(proof)` takes a native Z3Py proof; it does not
invoke a solver, simplifier, or the C++ evidence checker. Its command-line
driver first produces a proof from an SMT-LIB file, then reports checked
LP nodes separately from **unchecked non-LP nodes**. This is an arithmetic
subchecker, not a complete SMT proof checker or an F* soundness theorem.

The OCaml native bridge feeds local linear and input-conversion weights
to the existing verified Farkas kernel, which checks the actual native
formulas independently of the context certificate. Steps outside that
kernel's fragment, including integer cuts and monomial rules, remain
explicit obligations named `arith/lp-...`. Python/C++ replay coverage must
not be confused with obligation-free F*/Pulse checking.

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

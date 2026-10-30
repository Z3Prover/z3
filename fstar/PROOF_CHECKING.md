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
that path does not assume the legacy model contracts.

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
| Finite-field rewrites | [`Z3FiniteFieldLemma.fst`](Z3FiniteFieldLemma.fst) decides `rewrite` steps over `FF<p>` terms by normalizing both sides to sparse polynomials modulo `p` (atoms are the maximal non-field subterms) and by rescaling equalities with checked factors. It uses only commutative-ring laws, never assumes `p` is prime, and relies on the explicit `ff_model` hypothesis conjoined into `normalization_model`. The native bridge marshals `FiniteField p` sorts as `FF<p>` and `ff` numerals/operators with `decl_kind` 300-304 (see [`FINITE_FIELD_REPORT.md`](FINITE_FIELD_REPORT.md)). Finite-field `th-lemma` steps are decided by bounded exhaustive evaluation or, for any modulus, by replaying the recorded `ff-pac` ideal certificate in [`Z3FiniteFieldPac.fst`](Z3FiniteFieldPac.fst) when it uses only definitions and positive premises; certificates that need the inverse witness of a disequality remain unmet. |
| Integer division | [`Z3IntegerDivision.fst`](Z3IntegerDivision.fst) checks guarded quotient/remainder identities, remainder bounds, and common-factor cancellation with positive numeral divisors. Native integer `div` and `mod` have distinct interpreted tags. Soundness assumes their standard nonzero-divisor semantics; division by zero remains unspecified. [`Z3ArithmeticRewrite.fst`](Z3ArithmeticRewrite.fst) also checks binary-sum product expansion over integers and reals. |
| Gomory cuts | [`Z3LpGomory.fst`](Z3LpGomory.fst) reconstructs integer-split candidates from native LP row/bound data and requires both branches to derive the actual cut through the existing Farkas checker. Split exhaustiveness follows from integer semantics; no LP row, bound metadata, or foreign checker verdict is assumed. |
| Typed proof documents | [`Z3ProofDocument.fst`](Z3ProofDocument.fst) performs transport-independent definition, scope, input, and topological validation; [`Z3ProofIndex.fst`](Z3ProofIndex.fst) supplies persistent caches. |
| Native Z3 integration | [`Z3Native.fsti`](Z3Native.fsti) and [`ocaml_runtime/Z3Native.ml`](ocaml_runtime/Z3Native.ml) expose foreign API views; [`Z3NativeProof.fst`](Z3NativeProof.fst) marshals expressions and proof DAGs directly into checker datatypes. |

## Native direct proofs, including non-Horn clauses

Both native frontends accept `--direct-out FILE` in batch mode. After a
zero-obligation `ACCEPT`, [`Z3DirectProof.fst`](Z3DirectProof.fst) derives the
complement of the **last input assertion**, which must be a nonconstant ground
literal. Put the negation of the desired goal last. Equivalent ground copies
are omitted too; none is exported as an axiom.

```sh
checker --direct-out direct.p input.smt2
```

This path needs no Taelja and permits multiple positive literals. It supports
clausal unit-resolution proofs over uninterpreted predicates and non-Boolean
terms, universal instantiation, clause-equivalent preprocessing, and native
`hypothesis`/`lemma` case-search proofs. For example, from `p | q`, `~p | r`,
`~q | r`, and the designated input `~r`, it produces a forward derivation of
`r` from the first three axioms.

A node with conclusion `C` and local hypotheses `H` becomes the unconditional
clause `C | ~H`, with the goal added if it used the designated input.
Hypotheses and that input become axiom-free tautologies. Binary resolution
computes the actual resolvent, followed by checked literal-inclusion weakening
when necessary. Learned clauses discharge only local hypotheses, never the
designated input. The output ends in `goal_1` with role `theorem`, not a
refutation under a negated-goal axiom. Ground equality reflexivity, symmetry,
binary transitivity, congruence, and predicate rewriting carry the same guards.
Boolean unit propagation through `iff-true`/`iff-false` proofs does too.
An independently inconsistent background
may establish the goal by weakening the empty clause.

The initial path requires ground literal hypotheses and resolution units;
quantified goals, nonclausal assertions, other equality rules,
existential/Skolemization, and interpreted theory inferences are unsupported.
It preserves the shared exporter's declaration/sort naming and typed universal
binders. `--direct-out` cannot be combined with `--tstp-out`,
`--interactive`, or `--clause-proofs`. Unsupported exports fail before opening
the destination. This is a presentation pass, not an extension of the trusted
kernel or a new soundness theorem for exported text. The native CLI tests can
independently check every emitted inference against only its cited parents:
set `Z3_FSTAR_SOLVER` to the checkout Z3 executable (both test builders do so
automatically).

### A Gentzen LK account

The appropriate calculus is **classical, multiple-succedent LK with equality**.
Write `Gamma |- Delta` for a sequent: the conjunction of the antecedent
implies the disjunction of the succedent. An empty succedent means
contradiction. A clause is a succedent, so a non-Horn clause needs no special
logical rule or single-positive-literal restriction. `bar(l)` denotes literal
complement; double negations are normalized classically.

The relevant ordinary LK rules include:

```text
           B |- B                                      identity

    Gamma, B |- Delta
    ----------------------                            negation-right
    Gamma |- Delta, ~B

    Gamma |- Delta, B       B, Pi |- Lambda
    --------------------------------------            cut
    Gamma, Pi |- Delta, Lambda

    Gamma |- Delta
    ------------------                                right weakening
    Gamma |- Delta, B

    Gamma |- Delta, B, B
    --------------------                              right contraction
    Gamma |- Delta, B

    Gamma, B |- Delta       Gamma, D |- Delta
    ----------------------------------------          disjunction-left
    Gamma, (B | D) |- Delta
```

Exchange and left structural rules are implicit. Packing a succedent into
one disjunctive formula uses disjunction-right.

Let `A` be the designated last literal, `G = bar(A)`, and `Gamma` the
remaining background assertions, omitting equivalent ground copies of `A`.
For each retained proof node, `H` records its local hypotheses and `g` its
dependency on `A`. Its conditional judgment has the form
`Gamma, H, [A if g] |- C`. Repeated negation-right, classical double-negation
normalization, and disjunction-right give the export invariant:

```text
    Gamma |- C, bar(h1), ..., bar(hm), [G if g]
```

Thus exported clauses are unconditional **relative to Gamma**, not relative
to the entire original input. The metadata describes the premises retained
by the presentation pass; clause-equivalent preprocessing can discard
logically redundant proof dependencies.

**Leaves.** A background assertion remains a background axiom. A local
hypothesis `h`, or the designated input `A`, is replaced by the corresponding
identity-derived excluded-middle sequent `|- h, bar(h)` or `|- A, G`.
Neither becomes a new background axiom.

**Resolution.** For signed-literal clause succedents, the derived cut macro is:

```text
    Gamma |- D, l       Pi |- E, bar(l)
    ----------------------------------
    Gamma, Pi |- D, E
```

It expands into ordinary LK cut and negation rules. Lifted resolution units
can have several literals because they carry hypothesis/goal guards. The
implementation computes their actual binary resolvent, contracts repeated
literals, then checks literal inclusion before weakening to the required
lifted conclusion. Weakening matters: if a carried `~p` coincides with a
resolution pivot, resolving `~p | q` with `p` yields `q`, while retained
context metadata may still require the weaker `q | ~p`. It is not correct
to label the latter the exact resolvent without this extra step.

**Learned clauses.** Suppose a native lemma discharges local hypotheses
`S` from a contradiction, retaining `H'`. Its lifted premise is
`bar(S) | bar(H') | [G if g]`. The native learned clause `L` contains the
complements needed to discharge `S`, so the target
`L | bar(H') | [G if g]` follows by exchange, contraction, and possibly
weakening. The exporter checks this inclusion. It never removes the
separate `g` flag when discharging local hypotheses. In the example below,
learning `p` under the designated input `~r` therefore yields `p | r`,
not an unconditional theorem `p`.

**Quantifiers and equality.** A universal instance follows by
universal-left and cut with the universal premise; it is not an extra
axiom. Guards and goals are ground, so no quantified variable occurs free
in them. Consequently placing guards inside a universal prefix is
capture-free and corresponds to standard LK quantifier rules. Ground
equality uses reflexivity and equality substitution, with cut carrying the
side succedents through symmetry, transitivity, congruence, and rewriting.
Boolean unit propagation similarly expands into propositional rules.
`forward_rewriting` is such a macro inference, not a primitive LK rule.

**Root.** The accepted native root has `C` empty and no local hypotheses.
If `g` is true, the lifted root is `Gamma |- G`. If it is false, the
background already derives the empty succedent, and right weakening gives
`Gamma |- G`. In either case `A` is absent from the final antecedent.

For the first example, resolve `p | q` with `~p | r` to get `q | r`,
then with `~q | r` to get `r | r`, and contract to `r`. The captured
`forward_rewriting` step compresses these cuts. Alternatively, the LK
branches `Gamma, p |- r` and `Gamma, q |- r` combine by disjunction-left
on the background clause `p | q`.

This is a classical direct derivation of the goal from the background,
**not a claim of cut elimination or an intuitionistic LJ translation**.
Excluded middle and classical double-negation normalization remain
available. The correspondence above is a mathematical account of the
presentation pass, not an F*-proved semantic-preservation theorem or a
new trusted kernel rule.

### Reproducible non-Horn examples

The inputs and captured native OCaml outputs are checked in together:

| Input | Captured output | Goal and feature |
|---|---|---|
| [`cases.smt2`](examples/direct/cases.smt2) | [`cases.p`](examples/direct/cases.p) | `r`, by disjunctive cases |
| [`learned-clause.smt2`](examples/direct/learned-clause.smt2) | [`learned-clause.p`](examples/direct/learned-clause.p) | `r`, with native `hypothesis`/`lemma` nodes |
| [`quantified.smt2`](examples/direct/quantified.smt2) | [`quantified.p`](examples/direct/quantified.p) | `q(a)`, by a typed non-Horn universal instance |

For example:

```sh
checker --direct-out direct.p fstar/examples/direct/learned-clause.smt2
```

The learned-clause input is:

```smt2
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (or p q))
(assert (or (not p) q r))
(assert (or p (not q) r))
(assert (or (not p) (not q) r))
(assert (not r))
```

Its actual direct output is:

```tptp
% Native direct proof; the last input assertion is discharged, not an axiom.
cnf(a0,axiom,((p) | (q))).
cnf(a1,axiom,(~(p) | (q) | (r))).
cnf(a2,axiom,((p) | ~(q) | (r))).
cnf(a3,axiom,(~(p) | ~(q) | (r))).
cnf(p5,plain,(~(r) | (r)),inference(tautology,[status(thm)],[])).
cnf(p28,plain,(~(p) | (p)),inference(tautology,[status(thm)],[])).
cnf(p29_r0,plain,((q) | (p)),inference(resolution,[status(thm)],[a0,p28])).
cnf(p30_r0,plain,((p) | (r)),inference(resolution,[status(thm)],[a2,p29_r0])).
cnf(p30_r1,plain,((r) | (p)),inference(resolution,[status(thm)],[p30_r0,p28])).
cnf(p32_r0,plain,((q) | (r)),inference(resolution,[status(thm)],[a1,p30_r1])).
cnf(p33_r0,plain,(~(p) | (r)),inference(resolution,[status(thm)],[a3,p32_r0])).
cnf(p33_r1,plain,((r)),inference(resolution,[status(thm)],[p33_r0,p30_r1])).
cnf(goal_1,theorem,((r)),inference(reiteration,[status(thm)],[p33_r1])).
```

There is no `~r` axiom, and `p28` is an excluded-middle theorem, not a
local assumption smuggled into the background. The clause at `p30_r1` is
the guarded learned lemma. The three stored outputs are example snapshots,
not stable proof-node identifiers: a different Z3 version can produce a
different valid DAG. The native CLI tests replay all three inputs with
both frontends, compare the background axioms and final goals, and, when
`Z3_FSTAR_SOLVER` is set, validate every recorded and regenerated inference
against only its cited parents.

## Taelja TPTP conversion

Both native frontends accept `--tstp-out FILE` in batch mode. After the
existing kernel returns `ACCEPT`, [`Z3Tptp.fst`](Z3Tptp.fst) exports a TSTP
refutation for [Taelja](https://github.com/kondylidou/Taelja). Conversion is
opt-in and does not add rules to the checker or discharge pending obligations.
`PARTIAL` and `REJECT` cannot be exported.

The bridge supports **ground and universally quantified Horn clauses over
uninterpreted predicates and non-Boolean terms**, including ground equality reasoning.
It translates asserted clauses and unit-resolution DAGs, equality reflexivity,
symmetry, binary transitivity, and congruence. Equality proofs become
superposition or rewriting steps; congruence starts from a reflexivity theorem,
not an additional input axiom. Boolean congruence and transitivity proofs are
traversed to collect the term equalities that rewrite predicates and clauses.
Reflexive disequalities are eliminated by equality resolution.

Modus-ponens steps that only change the presentation of the same clause are
removed, including `p => q` versus `not p or q`, and reversed term equalities.
Each clause has at most one positive literal.
Original declaration names are retained when they are unambiguous TPTP plain
words (`[a-z][A-Za-z0-9_]*`). Overloaded and other names use injective `dN`
fallbacks. Unambiguous source sort names are retained as TPTP atoms, quoting
printable ASCII names such as `U` or `user sort` and escaping quotes/backslashes.
Ambiguous, non-ASCII, or term-colliding sort names use injective `sN` fallbacks.
Generated declaration and sort names avoid original names in both namespaces
by appending underscores on collision. Native declaration and sort identities
are unchanged.
Ground-only problems use CNF.
Problems with universal assertions use typed TPTP (TFF): sort declarations,
function/predicate signatures, and typed universal binders preserve the
original many-sorted vocabulary. Nested universal prefixes, unused binders,
and shadowed source names are handled using de Bruijn indices, not textual
variable substitution.

At a checked unit-resolution step, the bridge recognizes the instantiation
tautology and its universal premise. It emits the instantiated clause citing
that premise, then resolves the remaining unit premises. Instances are derived
steps, never additional axioms. Clause-equivalent quantified preprocessing is
removed using the existing quantifier-normalization checks.

Existential/Skolemization proofs, quantifiers inside clause literals,
Boolean binders or Boolean-valued term arguments, interpreted
theory operations, other preprocessing or equality rules outside this bridge, and
`--interactive`/`--clause-proofs` exports are unsupported and fail explicitly.
Taelja can impose further restrictions, including refutations reduced entirely
to truth constants; converter failures are reported, not treated as proofs.

Build Taelja separately with GHC 9.6--9.12 and Cabal 3, following its README
(`cabal build exe:taelja`, then `cabal --project-file=cabal.project list-bin taelja`). The integration
is tested against Taelja 0.2.0.1, commit
`937074d3cc822edb12d58168e9b4711ad448847d`.
On Linux, including inside WSL, run:

```sh
python3 fstar/tools/convert_taelja.py input.smt2 \
  --checker /path/to/checker --taelja /path/to/taelja --output proof.p
```

The standard-library-only driver obtains the native checker's TSTP export
and invokes `taelja --tptp`. Both processes have a wall-clock timeout
(`--timeout`, default 60 seconds each). The destination is replaced only after
both succeed and Taelja produces nonempty output. It is not replaced on
unsupported input, failed checking, timeout, or translation failure.
For manual inspection, run `checker --tstp-out proof.tstp input.smt2` followed
by `taelja --tptp proof.tstp`.

The export bridge and Taelja are **presentation/conversion tools**, not additions
to the trusted F* kernel. An `ACCEPT` certifies the original assertions under
the checker's documented semantic contracts, not correctness of the exported
text. Independently validate the TPTP derivation before relying on its
translation. The ordinary single-executable checking workflow is unchanged
and needs neither Python nor Taelja.

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

# Formalization of SMT Theories

[Overview](README.md) | [Source audits](SOURCE_AUDITS.md) | [Proof checking](PROOF_CHECKING.md)

## Purpose and relationship to the other activities

This activity defines abstract semantics for SMT expressions and theory
values, then proves semantic laws in F*. The models do not depend on Z3's
internal C++ types. They provide a shared mathematical foundation for two
independent consumers: Neuro-Formal source audits and verified proof
checkers. A semantic lemma can support either activity without requiring
the other.

Some modules combine a theory model and its lemmas; others separate them
into `Theory`, `Rewrites`, or interpretation modules. Reports often describe
the foundational model together with an application to source auditing or
proof checking; the links below identify those shared resources, not a
dependency on the corresponding application.

## Foundations and theory library

| Area | Main modules | Related reports |
|---|---|---|
| Expressions and evaluation | [`Z3AstTheory.fst`](Z3AstTheory.fst): sorts, declarations, expressions, well-formedness, environments, interpretations, and evaluation; [`Z3BasicExprTheory.fst`](Z3BasicExprTheory.fst): basic-family operator classification | [Regex/AST](REGEX_REPORT.md), [simplifier primitives](SIMPLIFIERS_REPORT.md) |
| Concrete semantic values | [`Z3ValueTheory.fst`](Z3ValueTheory.fst): Boolean, integer, array, sequence, and bit-vector values and checker operator tags | [Pulse checker and interpretations](PULSE_PROOF_CHECKER_REPORT.md) |
| Boolean and arithmetic laws | [`Z3BoolRewriter.fst`](Z3BoolRewriter.fst), [`Z3ArithRewriter.fst`](Z3ArithRewriter.fst), [`Z3ArithRewriterPower.fst`](Z3ArithRewriterPower.fst), [`Z3ArithRewriterCast.fst`](Z3ArithRewriterCast.fst), [`Z3ArithRewriterOrder.fst`](Z3ArithRewriterOrder.fst), [`Z3NlArith.fst`](Z3NlArith.fst) | [Boolean/arithmetic](BOOL_ARITH_REWRITER_REPORT.md), [non-linear arithmetic and its assumptions](NL_ARITH_REPORT.md) |
| Real exponentiation | [`Z3PowerPreprocessing.fst`](Z3PowerPreprocessing.fst), [`Z3PowerSaturation.fst`](Z3PowerSaturation.fst), using `FStar.Math.Pow` for positive-base real powers | [Power bounds, counterexamples, and remaining analysis boundary](PR_11180_POWER_REPORT.md) |
| Exact linear arithmetic | [`Z3LinearArithmeticTheory.fst`](Z3LinearArithmeticTheory.fst), [`Z3LinearArithmeticAst.fst`](Z3LinearArithmeticAst.fst), [`Z3LinearArithmeticEmbed.fst`](Z3LinearArithmeticEmbed.fst) | [Arithmetic certificates and semantic-model contract limitation](ARITHMETIC_CERTIFICATE_REPORT.md) |
| Arrays | [`Z3ArrayTheory.fst`](Z3ArrayTheory.fst): extensional arrays, select/store, maps, and set operations | [Array theory and rewrites](ARRAY_REWRITER_REPORT.md) |
| Bit-vectors | [`Z3BvTheory.fst`](Z3BvTheory.fst), [`Z3BvRewriter.fst`](Z3BvRewriter.fst), using `FStar.UInt` | [Bit-vector laws and overflow predicates](BV_REWRITER_REPORT.md) |
| Datatypes and recursive functions | [`Z3DatatypeTheory.fst`](Z3DatatypeTheory.fst), [`Z3RecfunTheory.fst`](Z3RecfunTheory.fst) | [Datatypes](DATATYPE_REWRITER_REPORT.md), [recursive-function termination](RECFUN_REWRITER_REPORT.md) |
| Finite fields | [`Z3FiniteFieldTheory.fst`](Z3FiniteFieldTheory.fst), [`Z3FiniteFieldSearch.fst`](Z3FiniteFieldSearch.fst) | [Field operations, polynomial reasoning, and finite search](FINITE_FIELD_REPORT.md) |
| Finite sets and pseudo-Boolean constraints | [`Z3FiniteSetTheory.fst`](Z3FiniteSetTheory.fst), [`Z3PbTheory.fst`](Z3PbTheory.fst) | [Finite sets](OTHER_TH_REWRITER_REPORT.md), [pseudo-Boolean laws](PB_REWRITER_REPORT.md) |
| Sequences and regular expressions | [`Z3SeqTheory.fst`](Z3SeqTheory.fst), [`Z3RegexTheory.fst`](Z3RegexTheory.fst), [`Z3RegexExprTheory.fst`](Z3RegexExprTheory.fst), [`Z3StoiTheory.fst`](Z3StoiTheory.fst) | [Sequence/regex laws](SEQ_REWRITER_REPORT.md), [regex AST semantics](REGEX_REPORT.md), [sequence equations](SEQ_EQ_SOLVER_REPORT.md) |
| Floating point | [`Z3FpaTheory.fst`](Z3FpaTheory.fst), [`Z3FpaConverter.fst`](Z3FpaConverter.fst), [`Z3MpfTheory.fst`](Z3MpfTheory.fst), [`Z3MpfRound.fst`](Z3MpfRound.fst), [`Z3MpfExact.fst`](Z3MpfExact.fst) | [Floating-point semantics](FPA_REPORT.md), [MPF semantics and rounding](MPF_REPORT.md) |
| Substitution, quantifiers, and model reconstruction | [`Z3SimplifierTheory.fst`](Z3SimplifierTheory.fst), [`Z3ModelReconstructionTheory.fst`](Z3ModelReconstructionTheory.fst), [`Z3LeibnizTheory.fst`](Z3LeibnizTheory.fst) | [Simplifier primitives](SIMPLIFIERS_REPORT.md), [model reconstruction](MODEL_RECONSTRUCTION_REPORT.md), [Leibniz instantiation](LEIBNIZ_SIMPLIFIER_REPORT.md) |

Proof calculi and certificate semantics build on these foundations; their
modules and reports are indexed on the [proof-checking page](PROOF_CHECKING.md).

## Bounded Boolean equivalence

[`Z3BoundedBoolEquiv.fst`](Z3BoundedBoolEquiv.fst) is a verified semantic
procedure over `Z3AstTheory.expr`, with executable entry point:

```fstar
bounded_bool_equiv :
  depth:nat -> width:nat -> s:Z3AstTheory.expr -> t:Z3AstTheory.expr -> bool
```

It recognizes constants, n-ary `and`/`or`/`xor`, unary `not`, and binary
`implies`/Boolean `eq` using `Z3BasicExprTheory.decl_kind_of` tags in
`func_decl.interp`, not declaration names. This basic-family encoding is
distinct from the `Z3ValueTheory` proof-checker tag encoding. Declaration
domains, ranges, arities, parameters, and argument sorts must match.
Malformed or unrecognized applications, non-Boolean equality, variables,
and quantifiers are opaque; quantifier bodies are not traversed.
Nonidentical non-Boolean inputs return `false`.

`depth` bounds candidate discovery and connective expansion.
`candidate_nodes` visits the outer structure up to and including that
depth, without entering opaque nodes. `common_boundaries` intersects the
two candidate sets by structural equality. Each Boolean skeleton stops
at its first shared candidate, even if it appears at different depths
in the two inputs. Constants remain constants rather than boundaries;
unmatched nodes at the depth cutoff become opaque atoms.
`cut_with_boundaries` also supports a supplied boundary list, with
`lemma_cut_at_boundary` proving selected nodes atomic.

For example, depth 3 compares `(and (or (and A y) z) y)` with
`(and y (or A z))` using just the shared atoms `A`, `y`, and `z`, even
when `A` is arbitrarily deep.

`width` caps distinct atoms in the combined frontier, not discovered
candidates or internal AST nodes. The checker streams at most `2^width`
truth-table rows, using the same assignment for both inputs and stopping
at the first disagreement. Identical expressions succeed immediately,
even with zero bounds. Discovery is depth-bounded, not breadth-bounded;
structural equality can still inspect deep subtrees because the AST has
no constant-time node-identity operation.

`lemma_bounded_bool_equiv_sound` proves that success implies equal
`Z3AstTheory.eval` results under any interpretation and environment
satisfying `boolean_semantics`: ordinary Boolean evaluation laws and a
faithful Boolean representation. This is a semantic contract, not an
assumption that the checker is correct or the inputs equivalent.
`boolean_interpretation` constructs such an interpretation from a fallback,
`lemma_boolean_interpretation_semantics` proves its contract, and
`lemma_bounded_bool_equiv_boolean_sound` specializes soundness to it.
These proofs use no axioms or admitted obligations.

`false` means equivalence was not established, not necessarily that the
inputs differ. Bounds and opaque boundaries can lose semantic
relationships: freezing `A = (or p q)` prevents establishing
`(or A p) = A` when `A` and `p` are treated as independent atoms.

[`Z3BoundedBoolEquivTests.fst`](Z3BoundedBoolEquivTests.fst) covers the
connectives, empty n-ary operations, malformed/opaque expressions,
budget exhaustion, shared boundaries at unequal depths, deep shared
subtrees, and native evaluation soundness. Use the shared verification
command in the [overview](README.md).

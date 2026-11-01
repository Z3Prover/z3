# dt2bv proof-converter audit

## Result and scope

`Dt2BvProofConverter.fst` proves the denotational correctness of substitution-based
refutation transport, conditional on a sound target refutation and sound bridge
certificates. `verification.log` records F* verification; `manifest.json` binds
that verification to the exact source and audit-file hashes.
Text hashes normalize CRLF to LF, matching Git's committed text blobs on Windows
and Linux; verifier and solver binary hashes are not normalized.

This is a source-linked semantic audit, **not** a mechanized verification of C++
execution, Z3's SMT engine, or every proof rule. No unconditional equality between
an enumeration constant and an unrelated fresh bit-vector is assumed.

## Construction

For constructors `C0, ..., C(n-1)`, replace each fresh bit-vector `b` with
`ite(x = C0, 0, ite(x = C1, 1, ... n-1))`. The bit width must accommodate every
constructor index. Obtain a proof of each original assertion's equivalence to its
substituted target and a proof of every substituted range bound by refuting its
negation in a fresh, proof-enabled AST manager and SMT kernel.

Discharge the negated certificate hypothesis with `PR_LEMMA`. Nested contextual
lemmas are completed with complements of their remaining hypotheses, then unit
resolution restores their original context. A negated disjunction can be one
quoted hypothesis rather than separate clause literals; retaining both views
requires only Boolean absorption of a duplicated disjunction.

Substitute the target refutation, including expression-valued proof declaration
parameters such as `quant-inst` bindings. Replace asserted target leaves with
prepared proofs. Reject declaration-valued parameters that require replacing a
fresh declaration with an expression. Original premises are retained; introduced
bounds become theorems. Reject asserted leaves not owned by the original input proofs.

Prepare certificates before modifying the goal, then attach the converter through
ordinary `goal::add(proof_converter*)`. There is no separate refutation-converter
field. For a decided goal, `goal::pc()` closes its existing converter chain with
the stored refutation. The nullary `apply(manager, converter)` evaluates such a
closed graph; the three-argument overload still converts one supplied proof.
Without a stored refutation, a decided goal exposes no proof converter; this
preserves proof-disabled solving even when an unused subgoal graph remains.

Split-clause appends its discharge converter inside the parent's existing chain
and clears inherited proof converters from its children. Thus a parent encoding
is converted after branch discharge; an encoding introduced inside a branch is
converted before discharge. Sequential/repeat combinators clear a converter chain
once its proof has been materialized, so final proof retrieval does not apply it
twice. Conversion failure does not return an uncertified UNSAT proof.

## Source correspondence

| C++ operation | F* obligation |
|---|---|
| `dt2bv_proof_converter::insert_enum` | `lemma_encode_from`, `lemma_encode`, `lemma_range`, `lemma_equality`, `singleton`: total constructor encoding, non-wrapping numerals, bounds, injectivity |
| `prove`, `close_encoding_lemmas` | `discharge`, `complete_lemma`, `restore_context`, `absorb_quoted_clause`: discharge, contextual closure/restoration, quoted-clause absorption |
| `insert`, `insert_bound` | `rewrite`, `bound`: MP requires a proved substituted equivalence; bounds require theorem certificates |
| `operator()` | `lemma_substitute`, `lemma_certificates`, `refutation_transport`: pullback of a sound refutation through certified premises |
| `substitute_proof_parameters` | `lemma_parameters`: proof payloads and conclusions use the same substitution |
| Ordinary converter concatenation | `compose_transport`: convert the later transformation before the earlier one |
| Split-clause branch recombination | `split_refutation`, `lemma_refuted_branches`: discharge all branch hypotheses before parent conversion |
| Previous unconditional bridge | `old_bridge_is_not_valid`: an in-range, unrelated fresh BV does not justify the old rewrite |

The manifest also covers the rewriter's proof-suppression flag, eager tactic
preparation, goal copying/translation, final proof conversion, split-clause scope
handling, build registration, and native regression tests. Their C++ control flow
is reviewed and tested, not extracted into F*.

## Assumptions and limitations

Enumeration constructors denote distinct values and exhaust their sort. BV
numerals denote residues modulo `2^width`. AST substitution is capture-avoiding
because replacement encodings are closed; AST translation preserves declaration
identity and proof semantics. Returning certificate subexpressions are seeded
back to their original AST nodes.

Soundness of input proofs, primitive Z3 proof rules, Boolean rewrite certificates,
SMT certificate synthesis, allocation/lifetime behavior, and the C++/F*
correspondence remain trust boundaries. The F* transport theorem requires proofs
of **all** substituted target premises, not just range constraints. Quantified
encoding rewrites are permitted only when their bridge certificate can be
produced; the audit does not separately mechanize quantifier conversion.

Native regressions check closed false-root proofs, ownership of asserted leaves,
absence of fresh BV constants, converter translation, both split-clause tactic
orders, repeat-based recombination, exactly-once parent conversion after discharge,
proof-disabled UNSAT without a proof converter, expression-valued instantiation
bindings, and rejection of foreign
assertions, unsupported declaration-valued parameters, and invalid bridges.
The legacy checker and independent SMT checks of its returned side conditions
validate those test proofs. This is not a claim
that the Pulse checker supports all BV/datatype rules used by these proofs.

Certificate synthesis adds proof-enabled runtime cost and can fail under
cancellation, resource exhaustion, or unsupported solving. Proof-disabled
encoding and model reconstruction are unchanged.

## Reproduction

From the repository root, with F* and the checkout Z3 already built:

```powershell
& .\fstar\audits\dt2bv-proof-converter\verify.ps1 -FStar <path-to-fstar.exe> -Z3 .\build\z3.exe
.\build\test-z3.exe get_consequences
```

The verifier detects tool versions, records verification output, and publishes a
source-linked manifest only after a successful run with unchanged source/audit
hashes. Source hashes describe the working tree;
the recorded base commit is not a claim that these edits are committed.

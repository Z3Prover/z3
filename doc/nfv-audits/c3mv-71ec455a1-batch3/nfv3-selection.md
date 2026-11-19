# Batch 3 frozen whole-property selection

Status: selection stage complete, before model implementation or verifier use.
Exactly two new distinct changed entries, P18 and P19, not a ten-property quota
or separate properties for each branch/conjunct. Keep the two previous reports
and their verification histories immutable.

Audited source: `71ec455a18702fe695d0c924a535ff9f385bd58d`.
Current comparison pin: `c2460a558fc6fee3cf15cfebd2d3f642ebf77770`.
Unchanged merge base: `437536cd64a544a1c329fc57d83e56e294fdf47c`.
NFV methodology: `599726579274cfeb1c0915414b911371527a9870`.
The earlier published batches retain their old master pin. See the coverage
handoff for the changed comparison and explicit broader test-file overlap.

Frozen `nfv3-selection.json` SHA-256:
`0beb5b435b99a07ee85fbc6830028ee477f8b79bbd243c1f254887ef9b0da13e`.
Freeze receipt SHA-256:
`377b10d0275710ecf880d262995f264a19b053ddff627a372e15d8659b002502`.
Do not regenerate or overwrite these files. The selection builder intentionally
rejects an attempted overwrite. Record any later ambiguity explicitly rather
than silently changing a frozen goal or adding a convenient assumption.

## P18: all-case power-trichotomy rewrite preservation

Entry: `power_trichotomy::apply`,
`src\ast\seq\seq_power_facet.cpp:455-579`.
Source hypothesis: "Each case asserts exactly what its substitution
`Y^N := X^M . z` needs." The complete positive goal is
`!constraints_ok || fromWord == toWord` for the emitted substitution, including
f0's distinct empty substitution target. All five cases, both directions,
constant/fresh-root alternatives and actual residual order stay in one entry.

Use the full flattened token value view, with token boundaries and observed
literal-character flags, to give ConstantWord its real body-defined behavior;
do not infer literal status from a variable's word valuation. Preserve signed
power semantics, empty fresh roots, negative fresh k and the strict mirrored
length guard. Arithmetic/word constraints added by the branch become the
explicit output conjunction, not an unconditional environment assumption.

Retain the actual constant/period enumerator domains. In particular two
constant bases in f2 must commute: the enumerator excludes the other case.
Prove any needed primitive-root/common-root facts with bodies; do not assume
that Y is a power of the chosen root when the code does not add that equation.
For constant f3, prove the actual suffix/slice periodic decomposition, including
periods that do not divide the word length. Preserve unsigned length arithmetic
in its enumerator guard rather than assuming it never wraps.

Eight complete input examples cover f0, f1, both fresh-empty and constant f2,
symbolic-negative-k and constant-nondividing-period f3, f4, and mirrored f1.
These are only independent domain candidates, not checked witnesses or native
traces. Full AST/rewriter correspondence, registration/dependency/lifetime
effects, preceding search reachability and branch completeness remain outside
this word-semantic projection. If the full goal cannot be proved, report it as
unresolved; do not replace it with lengths or assume the missing word theorem.

## P19: documented semantic rewatch contract and complete local updates

Entry: `try_rewatch`, `src\util\stx_search_tree.h:681-708`, including its
attached precondition/return-contract comment. The entire positive property
combines moved iff a semantic core literal is absent, valid selected watch,
semantic absence at a moved watch, and exact unwatch/assign/watch effects or
the unchanged state on false. Preserve the full conjunction for all checks.

Keep pointer identity separate from semantic equivalence-class values. Model
the actual identity-based scan and skip-old-watch loop, with body-defined
identity membership, semantic presence and first-remove/resize/append helpers.
Represent all watch buckets by lengths and flattened core-ID contents; do not
leave state mutations unconstrained. The current watched literal is required
to be semantically active, as justified by the semantic store lookup caller.

Three complete independent domain candidates include live aliases for both
canonical objects, a genuinely absent second literal requiring bucket growth,
and a singleton semantic alias. None is a counterexample until the complete
conjunction is mechanically negated, every input is pinned and the independent
domain plus concrete caller are checked. Any accepted converse violation is
a missed-hit/local contract result, not evidence that a core is satisfiable,
that Z3 returned a false SAT/UNSAT result, or that native code crashed. Resource,
allocation, overflow and memory-safety behavior is outside the normal-return
value-state projection and must remain disclosed.

## Validation and next stage

The builder validates pinned inventory hashes, exact attached source quotes,
changed anchors in each selected slice, distinct entry count and complete
input coverage in every candidate example. A pre-freeze span check initially
failed because the rewatch quote was outside the body-only slice; the slice
was extended to include the attached changed contract. That source-selection
failure is preserved in JSON and is not a verifier attempt or solver finding.

Next: nfv3-model. Read the frozen JSON as authoritative. Give every computation
an exact source tag and every helper a body and source/environment metadata;
all inferred requires have metadata. Preserve draft diagnostics. Establish
all index domains, run only trusted Dafny resolve/provenance checks, and seal
computation/contracts before verification-stage property-free validity,
independent domains and full original goals. Use a new batch-3 workspace,
the pinned Dafny 4.11.0 / explicit Z3 4.12.1, two cores and bounded limits.

P13's whole queue property, C11 global caller acyclicity, semantic dependency
core sufficiency and P12 native giant-pattern reachability remain open. No
eligibility-only or fuel-only replacement is selected. Schedule 2 stays active.

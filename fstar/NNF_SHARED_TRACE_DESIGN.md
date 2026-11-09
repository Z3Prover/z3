# Shared-step NNF proof checking: findings and proposed design

## Status and scope

Design review, 2026-11-09, against Z3 revision
`532cbc4aee06a3745a318fc9e8b86124123c7bca`.
This document records findings and an implementation plan; it does not describe
an implemented or newly verified checker.

The objective is to check `nnf-pos` and `nnf-neg` with overhead proportional to
the transformations Z3 performs, while preserving the existing typed semantics,
Skolem model extensions, malformed-certificate rejection and explicit pending
obligations. The benchmark corpus is `C:\bench\inputs\fstar-build`.

**Recommendation:** retain Z3's existing local NNF derivations. Replace
tree-oriented certificate processing with shared, typed step checking, and add
explicit substitution/definition metadata where the checker currently has to
rediscover it. Raising work limits or expanding NNF into larger generic Boolean
proofs is not the proposed solution.

Related documentation:
[existing NNF protocol](PROOF_CHECKING.md#nnf-certificate-replay-sorted-route)
and [historical checker report](OCAML_CHECKER_REPORT.md).

## Findings

### The producer already records local, shared transformations

`src/ast/normal_forms/nnf.cpp` maintains four caches indexed by expression,
polarity and whether the expression is inside a quantifier. Results and proofs
are reused. Connective transformations have local child proofs; binder bodies
use `proof-bind`; Skolemization is composed with the surrounding transformation.
The producer knows the actual witness declarations, dependencies and
capture-avoiding substitution when it creates a Skolem step.

`ast_manager::mk_nnf_pos` and `mk_nnf_neg` construct proof nodes with shared
parents and observational source/target facts
(`src/ast/ast.cpp:3282-3299`). A wholesale replacement of Boolean proof
generation is therefore not the first priority.

The C++ proof checker is not an independent correctness oracle for these rules:
its NNF cases are still `TBD` and return true
(`src/ast/proofs/proof_checker.cpp:811-818`).

### Shared expressions are repeatedly processed as trees

The native bridge caches marshaled expressions, so expression subterms are
physically shared (`Z3NativeProof.fst:203-235`). However:

| Location | Work that must be addressed |
|---|---|
| `Z3NnfReplay.fst:920-982` | `nodes_within` counts unfolded tree occurrences; every demanded entry's formula is walked; premise formula sizes are charged again at each use. |
| `Z3UnifiedProof.fst:799-836,878-969` | Scope propagation records demanded scopes, then traverses complete formulas under each demanded scope. |
| `Z3UnifiedProof.fst:669-730` | Sort comparisons charge base-sort name characters repeatedly; computing name lengths also allocates character lists. |
| `Z3SortedProof.fst:1701-1711,2138-2142` | Whole-formula scoping and context validation run before NNF replay, outside the replay's work accounting. |

Consequently, a small shared derivation can exhaust a resource budget rather
than replay successfully in time proportional to its DAG. The unbudgeted
front-door checks also mean that improving `nodes_within` alone cannot establish
an end-to-end bound.

The existing OCaml equality implementation uses `Stdlib.compare`, which can
skip physically shared subtrees (`ocaml_runtime/prims.ml:44-48`). The problem
must not be described as every equality comparison blindly unfolding sharing:
the explicit walkers above do so independently of that optimization.

### Certificate sharing stops at root boundaries

`marshal_binder` starts `marshal_binder_jobs` with an empty proof-entry cache
for every root (`Z3NativeProof.fst:399-435`). Each certificate deduplicates its
own proof DAG, but overlapping roots can duplicate proof-entry records and
premise lists. These binder roots become premise-free
`QuantifierIntroduction` nodes rather than ordinary globally shared proof
nodes (`Z3NativeProof.fst:504-580`).

Expression trees are not deep-copied per entry. Cross-root metadata duplication
is a separate issue from repeated traversal, and was modest in the fresh
examples below.

### Remaining coverage is not generally missing Boolean NNF laws

`Z3NnfReplay.entry_ok` supports the local Boolean rules, congruence, reflexivity,
transitivity and eligible Skolem equations. Scoped rewrites and related rules
are gated to a `quant-intro` root; that does not make them supported under an
NNF root. Naming with `intro-def`/`apply-def`, labels and other unsupported
leaves must remain explicit obligations until justified.

Closed and dependent Skolem extraction also have an independent
`expression_budget 4096` gate (`Z3SortedProof.fst:2764,2830`). Eliminating scope
budget exhaustion alone does not remove this gate.

Current diagnostics combine unsupported rules, resource exhaustion and failed
local checks into `Unreplayed`, often exposing only the outer `nnf-pos` or
`nnf-neg`. Malformed premise references already have a distinct rejected-entry
contract; preserve it.

## Evidence and limits

### Historical extracted-checker results

The dependent-Skolem re-sweep in `OCAML_CHECKER_REPORT.md:4937-4998` used
candidate `3499ebf14`, producer `b3c1e0bac` and 359 NNF-bearing files. Over the
answered queries it recorded:

| Remaining cause | OCaml | Cherry |
|---|---:|---:|
| Closed Skolem formula exceeds the 4,096-node definition budget | 54 | 53 |
| `intro-def` / `apply-def` inside NNF certificates | 9 | 9 |
| Scope-guard work exhausted | 20 | 17 |
| Total | 83 | 80 |

No diagnosed residue stopped at a local Boolean NNF rule, a dependent-Skolem
step or a malformed certificate. The scope-budget cases needed 1.02-14.2 times
the configured work; 81-92% of their charges were sort-name characters.
Nineteen of the twenty OCaml scope-budget cases would subsequently fail the
Skolem definition budget anyway.

These are historical observations, not current-master coverage counts.
Timeouts and unexecuted query tails were not counted as checked. An unbounded
diagnostic rerun is not a production checker acceptance.

### Fresh native observations

The review rebuilt the current native producer and exercised all 15 existing
NNF probe inputs, which returned UNSAT. It inspected the actual native proof
DAGs for all eight queries of `queries-FStar.PartialMap.smt2`, all eight queries
of `queries-FStar.FunctionalExtensionality-1.smt2`, and the first query of
`pulse\queries-PulseCore.Action-1.smt2`.

For Pulse `Action-1`, query 1, the NNF-rooted certificate closures contained:

| Metric | Count |
|---|---:|
| Distinct proof steps | 100 |
| Proof entries summed over certificate roots | 103 |
| Distinct formula DAG nodes | 764 |
| Unfolded node occurrences summed over certificate formulas | 71,789 |

The last count is about 94 times the distinct formula-node count. It measures
repeated tree-processing potential, not an observed RSS multiplier or the exact
number of operations the bounded checker completes. Only three proof entries
were duplicated across roots here; sharing certificates alone would not
address the principal traversal mismatch in this example.

Native-only controls used the first-query prefixes, proof production off/on,
three repetitions per mode, and sequential runs:

| Input | Median wall time, off/on (ms) | Median sampled peak working set, off/on (MiB) |
|---|---:|---:|
| PartialMap | 49.75 / 57.25 | 29.46 / 30.36 |
| FunctionalExtensionality-1 | 44.77 / 47.16 | 29.05 / 29.48 |
| Pulse Action-1 | 162.28 / 189.41 | 35.46 / 38.96 |

All 18 runs returned UNSAT. Working-set information was sampled at 2 ms
intervals; these are sampled observations, not guaranteed final absolute peaks.
These controls measure native solving/proof-production costs, not extracted
checker overhead, and do not establish whole-corpus behavior.

No current extracted F* checker was rebuilt or run for this review. A local
historical checker predates `Z3NnfReplay` and is not a valid current baseline.
The fresh native UNSAT results are not fresh F* `ACCEPT` results. A paired
current-checker time/allocation/peak-memory baseline remains an action item.

Review artifacts were retained in the originating Copilot session's `files`
directory: `nnf_review_20261109.py`, `nnf-review-20261109-summary.json`,
`nnf-review-native-profile.json`, the per-input `*.nnf-review.json` records,
and `nnf-review-20261109.db`. The summary records the reviewed source hashes.
These are local artifacts, not repository dependencies or a substitute for
the reproducible baseline required below. The native build included the three
pre-existing unsigned-cast warning fixes, with no NNF production changes.

## Proposed certificate and checker

### Document-level shared tables

Use one document-level table each for sorts, declarations, terms and proof
steps. Roots reference existing steps. Intern terms through checked shallow
definitions whose child references are already validated. Check exact
declaration signatures, parameters, argument sorts and binder conventions.

Native AST IDs and hashes are untrusted transport identifiers. Do not equate
sorts by stripping `sort!<id>:` prefixes or trusting a native ID. Establish a
correspondence between validated table entries and their semantic objects.
Charge input names and other payloads when importing them, not repeatedly at
each proof use.

An NNF step should identify its rule, polarity, source, target and child steps.
Binder steps additionally identify their binder sorts. Skolem and naming
steps carry the explicit metadata discussed below. Preserve legacy public
NNF proof kinds and printing initially; the bridge can first derive the shared
representation from the existing native proof DAG.

### Scope-parametric transformation soundness

Make the following the principal proof obligation for Boolean transformations,
under a certified definition context `C`:

```text
for every compatible scope Gamma, typed environment rho and model M of C:
  typed Gamma source
    implies typed Gamma target
        and eval(M, rho, target)
              = (if positive then eval(M, rho, source)
                             else not eval(M, rho, source))
```

Non-Boolean helper steps need the corresponding same-sort value equality.
Binder cases extend the scope with the producer's reversed binder-sort list.
Local checks consume only the relevant node shapes and child references.

The forward typing implication is essential. The weaker statement "equal
whenever both endpoints are scoped" does not justify generic transitivity:
premises can be vacuous at a root scope when their intermediate term is
ill-scoped. Forward typing preservation establishes the intermediate's typing
from the first premise before applying the second.

This invariant could allow one shared transformation scheme to be reused
without enumerating all ambient scopes. It is not proved by the existing
guard-based theorem and requires new constructor, composition, binder and
substitution lemmas. Memoizing `(proof ID, entire scope)` alone does not
establish linearity in native NNF states.

The existing `Z3NnfReplay.lemma_replay_with` at lines 3279-3304 is a useful
semantic reference: it proves a scoped conclusion and actual Sorted truth
under its quantifier/model/assertion assumptions, not merely certificate
well-formedness. Preserve this meaningful connection. Local NNF soundness
alone is not unconditional soundness of the entire SMT-LIB pipeline.

### Explicit Skolemization and conservative definitions

Record witness declarations, dependency indices and sorts, binder order and
the actual substitution at the native generation point. Check substitution
through local recorded work rather than repeated expansion of whole bodies.

Maintain all of the existing semantic obligations:

- Fresh declarations are disjoint from original declarations and other fresh
  declarations, with exact signatures.
- Dependency references are typed, substitutions are capture-avoiding and
  binder/index shifts are checked.
- Definitions are acyclic and conservatively extend the original model.
- Correlated existential witnesses use one joint choice tuple for each
  dependency tuple, not independent choices.
- The source and result correspond to the same checked substitution and
  definition context.

Skolem equations hold in a certified joint-choice model extension, not in every
arbitrary fixed interpretation. The context `C` in the invariant must be
constructed and justified accordingly, rather than assumed without proof.

Add dedicated conservative-definition rules for `intro-def`/`apply-def`.
Labels, the `hnf.cpp` variant and other unsupported leaves must not be accepted
merely because their enclosing root has an NNF rule name.

### Storage, accounting and diagnostics

Dense checked IDs permit array-like lookup. The present `Z3ProofIndex` integer
trie has logarithmic lookup/update and persistent path-copy allocation;
renaming it a cache does not make it constant-time. A verified mutable
implementation should refine the pure table model, with checked bounds and
postconditions connecting lookup/update to that model.

The target is linear overhead in emitted transformation steps, consumed
argument/premise edges and explicitly recorded substitution/definition work,
in addition to independently accounted import and type-validation work.
Include context construction and definition expansion; preserve the existing
memoized expansion sharing in `Z3ProofDocument`.

Do not claim a whole-pipeline linear bound before context-sensitive input
typing, table construction and all front-door checks are covered. In
particular, avoid structural equality or scope walks that silently unfold
shared expressions in an otherwise local fast path.

Use resource limits on actual checked/imported work. Unused padding entries
must not determine whether an otherwise identical derivation replays.
Separate diagnostics for unsupported rules, resource exhaustion, malformed
references and semantic/local-check mismatches; include the failing inner
step ID. Preserve rejected malformed-reference behavior and explicit pending
results. Any compatibility fallback needs its own bounded accounting rather
than hiding expensive semantic search after replay fails.

## Implementation sequence and acceptance gates

1. **Establish the current baseline.** Build the current checked/extracted
   OCaml and Cherry pipelines using their documented verification process,
   with the same native producer and bindings. Run the existing NNF suites.
   Record source/toolchain hashes and isolate pre-existing failures. Measure
   marshaling, context construction and checking separately, including elapsed
   time, allocation and peak live/process memory.
2. **Introduce shared transport without weakening acceptance.** Add a
   document-level step table and roots-as-references. Preserve the legacy path
   for comparison and malformed-certificate contracts. Differentially compare
   conclusions and outcomes on identical proof documents.
3. **Prove the local transformation kernel.** Establish the scope-parametric
   forward-typing/value theorem for the supported Boolean and helper rules.
   Replace repeated whole-formula validation only where the new theorem
   justifies it. Refine the chosen storage implementation to the pure spec.
4. **Complete definition and Skolem replay.** Emit explicit native metadata;
   prove checked substitution, conservative naming and joint-choice extension
   correspondence. Remove tree-size gates only when the replacement has
   justified resource and semantic checks.
5. **Validate scaling and corpus coverage.** Check actual producer-to-bridge-
   to-extracted-kernel results, not just hand-constructed certificates.
   Compare paired runs on byte-identical proof documents where possible;
   report different proofs, timeouts and unexecuted tails separately. Publish
   pending counts by inner reason as well as outer proof kind.

Required focused tests:

- The existing roughly 60-level exponentially unfolded shared DAG replays with
  work/storage scaling in the shared representation, without padding.
- Wide disjunctions, deep negations, long transitivity chains, shared
  subderivations and overlapping roots have near-linear scaling; padding does
  not buy acceptance.
- Polarity, connective, premise order, binder sort/order, variable index,
  capture-avoidance and substitution mutations fail appropriately.
- Closed endpoints do not hide an ill-scoped intermediate term.
- Freshness collisions, cyclic definitions, missing dependencies and
  incorrectly independent Skolem witnesses fail.
- Forward, self, negative and missing references retain malformed rejection;
  unsupported valid leaves remain explicitly pending.
- Existing local-rule and dependent-Skolem tests continue to pass, and the
  previously diagnosed resource/naming residues are reclassified or discharged
  by actual checked rules, not by larger budgets or unchecked assumptions.

Do not use stale unchecked caches, bypass verification or remove guards merely
to obtain coverage or performance numbers. Completion requires both semantic
correspondence and measured scaling; a smaller pending count alone is not the
acceptance criterion.

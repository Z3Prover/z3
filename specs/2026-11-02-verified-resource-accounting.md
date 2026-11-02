---
status: draft
kind: design-only
compatibility: preserve public proof syntax, verdict protocol and existing default behavior until a reviewed opt-in rollout
source_baseline: b3c1e0bacb804261488516043836258018ec0b7d
related_nnf_pr: https://github.com/Z3Prover/z3/pull/11515
---

# Verified sort identities and DAG-aware checker resource accounting

## 1. Executive summary

Replace repeated name-based sort comparisons with checked sort identities, then reuse scope-validation results for shared proof structure. This is a change to the representation and charging model, not an increase to the existing work limit.

First introduce transparent caching that preserves the current result and remaining-work semantics. Next implement an explicitly versioned DAG accounting mode whose preparation cost is charged and whose scope-check theorem is proved against the same AST semantics. Keep the old default until the new mode passes proof, adversarial, native and benchmark gates.

The important boundaries are `validate_sort_graph`, which earns the right to use compact identities, and `check_certificate_scopes`, which checks every demanded typed scope. No native identity or producer hash becomes trusted merely because it is convenient.

This plan does not implement the change. It does not remove the independent Skolem-expression limit or establish whole-checker global soundness.

## 2. Context and motivation

### 2.1 Current state and evidence

Current master is pinned above. Relevant implementation:

- [Z3UnifiedProof.fst](../fstar/Z3UnifiedProof.fst), `name_length`, `sort_tasks_within`, `sort_eq_within`, `sorts_match_within`, `scope_entries_checked` and `binder_scoped_within`.
- [Z3BinderScope.fst](../fstar/Z3BinderScope.fst), executable-guard equivalence and root/edge scope theorems.
- [Z3ProofIndex.fst](../fstar/Z3ProofIndex.fst) and [Z3IdTable.fsti](../fstar/Z3IdTable.fsti), existing indexed structures and verified implementation boundaries.
- [Z3NativeProof.fst](../fstar/Z3NativeProof.fst), native reflection and nested binder-certificate transport.
- [PR #11515](https://github.com/Z3Prover/z3/pull/11515), typed NNF replay and dependent Skolem support. It is draft and unmerged at this plan's source baseline.

The NNF review identified 20 guard failures. An exact extracted-code trace established real budget exhaustion in every investigated certificate. In representative `PulseCore.Action-1`, query 1, node 433, the forward guard needs 3,542,713 abstract units against 2,555,749 available. The first failure is the scope check of entry 33, a transitivity step.

Across those certificates, 81–92% of charged work is base-sort name characters. The native reflected name `sort!2147483829:Term` has 20 characters. Comparing two such base sorts repeatedly charges both lengths before equality. Restated growing judgments also cause a sum of tree traversals even where the input proof shares structure.

The guard is behaving as specified. Its budget is a poor fit for this representation. This is not evidence of malformed scopes or incorrect NNF semantics.

Evidence is retained in `C:/z3atomic/.atomic/nnf-neg-20261101/phaseB4.md`, the guard4 traces and the completed workflow `3cb6d44a-f216-4969-8a13-505ea27c2b2f`. No repository `research/` directory exists in the inspected checkout; this plan uses those task artifacts and actual source instead.

### 2.2 Two separate costs

1. Repeated physical work: decoding/counting names, comparing sort structure and revisiting shared expressions.
2. Repeated abstract charges: billing the same name and subterm at each occurrence.

Caching length can reduce physical work without changing charges. Checked interning changes the unit of work and requires a new resource contract. These must not be confused.

The separate 4,096-node Skolem-expression budget still blocks 19 of the 20 certificates behind the scope guard. Improving sort accounting alone does not make those complete proofs ACCEPT. One representative would replay once the guard succeeds; others require a separate expression-budget design.

## 3. Goals and non-goals

### Goals

- Preserve sort equality exactly, including complete names, kind, array domain arity/order and range.
- Validate all referenced identities before cheap comparisons.
- Charge input preparation, table lookup, structural edges, distinct scope-validation obligations and memory growth explicitly.
- Reuse structural validation for the same expression under the same typed scope without reusing it under a different scope.
- Derive scope and NNF replay guarantees from the actual new executable checker.
- Improve the diagnosed cases without accepting false or ill-scoped certificates.
- Explain which limit was exhausted through additive diagnostics, preserving existing verdict and machine-row formats.

### Non-goals

- Strip native name prefixes, trust native sort IDs, treat hash equality as proof or raise the old budget to suppress failures.
- Skip guards for reflexive/transitivity steps.
- Trust the native declarations/expressions table to contain every term the checker reads.
- Change theory rules, epsilon freshness, Root laws, default route selection or public proof syntax unnecessarily.
- Remove the Skolem-expression cap in the same slice.
- Claim a hard process-time/whole-checker memory bound from an abstract validation-work theorem.

## 4. Proposed solution

Use document-local checked sort and expression graphs. A native ID or physical-sharing hint can locate a candidate entry, but it cannot establish equality. The verified construction validates the graph's complete structural content.

```text
existing proof/AST transport
  -> bounded preparation of actual consumed terms
  -> validate_sort_graph
       exact names + ordered domain/range edges + acyclicity
       -> CheckedSortGraph
  -> validate_expression_graph
       declarations, argument edges, binders, variable annotations
       -> CheckedExpressionGraph
  -> demand scopes from the closed root
  -> check_certificate_scopes
       memoized structural validation by expression identity + scope identity
       -> scoped certificate or named refusal
  -> existing typed rule replay
```

Candidate modules, subject to the first prototype's dependency review:

| Path | Planned responsibility |
|---|---|
| `fstar/Z3CheckedSorts.fst` | Pure checked sort graph, interpretation and equality theorem |
| `fstar/Z3CheckedExpressions.fst` | Expression graph validation and structural scope obligations |
| `fstar/Z3BinderScope.fst` | Scope-demand and scope-check proofs for the new representation |
| `fstar/Z3UnifiedProof.fst` | Bounded executable preparation and guarded integration |
| `fstar/Z3NativeProof.fst` | Optional untrusted sharing hints only if necessary |
| native OCaml/Cherry drivers | Opt-in accounting mode and additive exhaustion diagnostics |
| corresponding F* and native tests | Representation, scope, budget, sharing and parity scenarios |

Keep the dependency graph acyclic. The foundational checked graphs must not import the rule/document module that imports them. Reuse existing index-table contracts rather than create a second unproved cache implementation.

Boundary names: `validate_sort_graph`, `validate_expression_graph`, `check_certificate_scopes`. None publishes or mutates external state. The only new trust transition is successful checked representation construction.

## 5. Typed contracts and data flow

These signatures are design sketches, not APIs that exist today.

### 5.1 Validation boundaries

```text
validate_sort_graph(raw, budget)
  -> Prepared<CheckedSortGraph> | InvalidSortGraph(reason) | Exhausted(phase)

validate_expression_graph(raw, checkedSorts, budget)
  -> Prepared<CheckedExpressionGraph> | InvalidExpressionGraph(reason) | Exhausted(phase)

check_certificate_scopes(graph, root, demands, budget)
  -> ScopedCertificate | InvalidScope(node, scope, reason) | Exhausted(phase, node)
```

`CheckedSortGraph` contains a ghost structural interpretation of each valid ID. Its constructors are private. Required invariant:

```text
id_equal(i, j) <=> interpret_sort(i) == interpret_sort(j)
```

Structural deduplication is optional initially. If two structurally equal sorts have different IDs, a proved equality lookup can implement the same contract until canonical interning is available. Do not advertise integer equality as complete equality before proving injectivity and canonicality.

Graph validation rejects dangling references, conflicting ID definitions, cycles, wrong arities and invalid declaration/sort associations. Exhaustion is distinct from structural rejection. Wrappers translate resource exhaustion to existing pending/uncertified behavior, not false certification.

### 5.2 Exact name semantics

Intern base sorts by their exact reflected name, not a parsed display suffix or the native numeric ID. Read and validate name data within the preparation budget before allocation or hash expansion. A hash can choose a bucket; equality must verify complete bytes/characters according to the AST's string-equality contract.

Charge the actual scanning, decoding and collision comparisons. Count every serialized occurrence that must be read. “Unique input bytes” cannot be assumed just because a later table deduplicates names. If reflection already shares strings, exploiting that sharing must have an explicit runtime trust/validation boundary.

Malformed byte handling and the existing runtime decoder are retained and tested. This work must not introduce a different equality relation to avoid the current UTF-8 count cost.

### 5.3 Resource model

Use distinct budget components, not one number whose units silently change:

```text
PreparationBudget: scanned input/name units, graph nodes and edges
ValidationBudget: demanded node/scope obligations, lookups and local edges
StorageBudget: table entries, demand pairs and queued work
```

Spend before allocation or traversal amplification. Duplicate-ID validation is charged even if the ID was seen before. Hash-collision work and ordered-table lookup costs are charged. Integer/digit comparisons must be bounded before expensive conversions.

The intended accounted work is proportional to scanned input plus graph edges plus distinct validation obligations plus the specified lookup cost. It is not necessarily linear in unique expressions: one expression may require checking under many scopes. Do not write an unconditional `O(n)` claim or omit input decoding, cache preparation and memory costs.

Initial numeric defaults remain an explicit approval question after a prototype measures the units. The old work-limit constant cannot be copied into the new mode and described as an equivalent budget.

### 5.4 DAG-aware scope validation

Memoize a positive *structural* scope check using at least:

```text
(document generation, checked expression ID, checked scope ID)
```

Scope IDs represent the complete ordered sort environment, including reversed binder extension. Rule-child/premise checks still inspect actual edges and earlier-entry constraints. Distinct consumers demanding distinct scopes must be checked separately.

A cache entry earns the proposition `D.scoped scope expr`; it does not claim semantic truth, hypothesis discharge or a model-specific rule result. The checker cannot use a truth fact from one interpretation after an epsilon override without the existing preservation/replay proof. Budget exhaustion and incomplete checks must never populate a success cache.

Memo hits have a charge. Their proof transfers the stored structural proposition through validated ID interpretation, not pointer equality. Avoid expensive whole-expression hashing before the budget; hash-cons bottom-up using validated child IDs and charge any structural collision verification.

### 5.5 Actual consumed data

Build from original assertions and every judgment, rule argument, binder-certificate term, definition/closure and generated expression actually used by checking. Do not take `doc.expressions` completeness as an assumption. Existing read-view lemmas establish which source fields are consumed; extend them for preparation, generated terms and node-ID interpretation.

For generated dependent-Skolem closures, validate or derive new graph entries through checked constructors. Their variable indices and padding scopes must satisfy the same scope theorem. A graph prepared before elaboration is not automatically complete after elaboration.

## 6. Alternatives

| Alternative | Benefit | Problem / decision |
|---|---|---|
| Increase `binder_work_limit` | Small patch | Retains duplicated cost and moves the failure threshold. Not the selected design. |
| Cache name lengths, retain old charges | Low-risk CPU improvement with exact result/work equivalence | Does not fix charged-budget misses. Selected as an optional first transparent slice. |
| Trust native sort IDs | Fast equality | Unsound for adversarial or inconsistent reflected metadata. Rejected. |
| Hash names and trust digest equality | Convenient indexing | Collisions cannot become logical equality. Rejected without complete equality verification. |
| Checked sort interning only | Addresses dominant name cost | Repeated tree visits remain. Selected first representation milestone. |
| Checked sort + expression DAG + scoped memoization | Better fit to shared proofs | Larger proof/transport change. Selected staged extension after sort milestone. |
| Rich producer equality/share certificates | Can avoid rediscovery | Useful only as untrusted hints checked by the same validation boundary. Optional if existing sharing is insufficient. |

## 7. Backwards compatibility and operational risks

Published proof syntax, verdicts, stdout protocol and current diagnostic rows must remain compatible. Start with an opt-in `verified-dag` accounting mode; the existing default is unchanged until reviewed rollout. The spelling/location of the option is not yet settled.

Semantic compatibility is required, but **old remaining-work values cannot stay identical in a changed charging mode**. The transparent caching slice should prove exact old results and remaining work. The new mode must prove the same scope predicate, then separately describe new completeness/resource behavior. Under sufficient respective budgets, both agree with structural scope validation. At finite limits, some old pending results may become checked. Any newly checked false/scope-invalid result is forbidden.

New preparation limits can also cause rejection or pending earlier than the old mode. Measure and review those cases; do not promise old ACCEPT preservation under arbitrary new limits. Default changes require an explicit policy decision after compatibility results.

Internal canonical IDs are per document and cannot be persisted or reused across queries without generation/version validation. Incremental push/pop must not revive stale IDs or successful scope entries from a different document.

Abstract accounting does not cap the unmodified parser, solver, reflection runtime, allocator or all theory checkers. Keep process wall/memory envelopes and normal-stack tests. No hard DoS claim until the complete path has a corresponding bound.

## 8. Implementation and validation phases

### Phase 1: baseline and diagnostic contract

Red: reproduce n433's exact guard exhaustion and cases where `None` means a structural failure instead. Green: an additive named diagnostic identifies the phase, consumed units and node/scope without changing checking results. Refactor: share diagnostic accounting with production through a proved result correspondence.

Preserve the counted NNF benchmarks and the baseline `dt2bv` failure. Record actual source/proof identities. Structural metadata matching is not proof-byte identity.

### Phase 2: transparent reuse

Red: repeated long-name/tree work under a fixed document. Green: cache decoded name length or previously computed structural equality while continuing to deduct the exact old charge. Prove equality of the entire option/result/remaining-work behavior. This phase may be skipped if its machinery cannot be reused in the canonical representation.

It must not be presented as eliminating resource misses.

### Phase 3: checked sort graph

Red: forged IDs, cycles, conflicting repeated IDs, same ID with two names, different IDs with equal structure, reordered array indices, malformed names and extreme depth. Green: a bounded bottom-up validator with interpretation/equality lemmas on both F* pins. Refactor: replace repeated sort-name equality in the opt-in scope guard with validated identities.

Gate: a complete positive model/AST construction plus adversarial mutations, no assumptions or native-ID trust. Generated OCaml and Cherry code must be iterative where depth grows with input.

### Phase 4: expression/scope DAG

Red: shared expression under incompatible scopes, nested reversed binders, shadowing, open internal entry behind a closed root, repeated judgments and diamond proofs. Green: validated expression graph and positive scope memoization by node/scope pair. Refactor: prove the existing root/edge scope statements for the new executable path.

Keep all proof/hypothesis/epsilon semantic invariants outside the structural success cache. Measure the number of node/scope pairs, not just nodes.

### Phase 5: real certificate and resource tests

Run the 20 diagnosed guard-budget certificates and the earlier normal-stack long-name/application/sort fixtures on matched baseline/candidate, both backends. Separate effects of scope accounting from the unchanged Skolem-expression cap. Expect one demonstrated scope-only case to progress if preparation and validation budgets admit it; do not promise all 20 become ACCEPT.

Test exact/one-short budgets, storage exhaustion, duplicate-heavy input, hash collisions, deeply shared sorts, huge names, malformed annotations, fresh document generations and incremental queries. Every success must imply the same scoped AST predicate; every exhaustion must remain fail closed.

Report same-frozen-document check/preparation cost and memory separately. Preserve first timeout observations and distinguish producer variation. Verify old machine output parity when new diagnostics are disabled.

### Phase 6: review and rollout

Freeze the implementation after proofs, native tests and bounded corpus measurements. Independent reviewers cover semantics/equality, resource accounting/stack safety, and compatibility/completeness. Stop implementation once those gates pass. Publication and default activation are separate final actions requiring authorization.

Default numeric budget selection and default-mode activation remain open. An opt-in release can establish evidence without weakening the existing default contract.

## 9. Open decisions and unresolved proof questions

- Can checked preparation preserve existing reflection sharing, or does it require a new untrusted graph transport? Prototype this before specifying a public certificate format.
- Which verified map strategy gives bounded name/structure collision handling without a large trust expansion?
- What numeric preparation/validation/storage limits admit the target certificates while preventing input amplification? Calibrate and review, do not inherit old constants under new units.
- Should graph preparation cover the whole document at once or be extended through checked constructors during elaboration? Actual consumed/generated data decides this.
- What API shape best exposes the opt-in mode while preserving existing consumers? No default switch is authorized by this plan.
- The separate 4,096-node Skolem cap needs its own later unique-node/occurrence-accounting assessment. Do not silently remove it here.

This document is a draft. Implementation is not authorized or launched by producing the plan.

## 10. Completion evidence for the plan

Source and task evidence were inspected. Current master was fetched and pulled into a dedicated planning checkout before this file was written. No checker code, budget, model, parser, corpus or scheduler state changed. The 20-resource-failure measurements come from the reviewed NNF task, not a new experiment. Link checks and scope inspection are recorded in the accompanying planning receipt.

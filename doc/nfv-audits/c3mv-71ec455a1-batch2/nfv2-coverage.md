# Batch 2: continuing-audit coverage ledger

Status: coverage mapping complete. Formal property selection is the NEXT
scheduled stage, not part of this stage. No new proof/refutation/crash finding
is claimed. No native source was executed, built, tested, imported or changed.

## Immutable scope and artifacts

Production head: `71ec455a18702fe695d0c924a535ff9f385bd58d`.
Comparison master: `d738f81eab9af1468394664a812fe4310ae8e1fa`.
Branch merge base: `437536cd64a544a1c329fc57d83e56e294fdf47c`.
The working production tree still matches the audited head. Original published
evidence remains unchanged at `doc/nfv-audits/c3mv-71ec455a1`.

- `nfv2-coverage-ledger.json`: all 89 changed src files, file kinds, prior
  primary model scopes, source-anchored candidate entries and follow-up limits.
- `nfv2-coverage-source-inventory.json`: immutable blob IDs, hashes and exact
  candidate-source excerpts; every source file matched its pinned Git blob.
- `capture_nfv2_coverage.py`: reproducible capture and changed-span checks.
- `nfv2-p1-source-trace.md`: completed source-applicability follow-up, to be
  published with this batch rather than editing the original immutable audit.

There are 64 production files, 20 tests and five build files in the 89-file
src delta. Each of the original ten models has a primary entry in a different
production file. Thus 54 production files had no first-batch PRIMARY model;
this is not a claim that those 54 were never inspected or used as context.
Likewise, a primary model does not verify its entire containing file.

## Candidate areas for the selection stage

The JSON ledger contains exact source anchors, conditions and next steps.
These are 13 changed-code candidate ENTRIES, not 13 selected whole properties:
some broad follow-up areas require splitting before they could be selected.

| Entry | Gap and next obligation |
| --- | --- |
| C01 | Containment's all-determined-mismatches discharge, distinct from P1's prefix prune. Hypothesis shape `[X,a,Y]` versus `[X,b,Z]`, with X=aa,Y=b,Z=epsilon as a candidate ONLY; not yet modeled or refuted. |
| C02 | `replace_all_split::apply_case`: semantics and coverage of numbered empty/end/match/copy cases, retained tail equations and unsigned case-count arithmetic. |
| C03 | Regex-request propagation: erase-at-head, preserve unknowns in order, same-index reexamination, qhead bounds and actual trail undo. Oracle verdicts do not prove regex equivalence. |
| C05 | `check_stoi_coherence`: callbacks that append/reallocate term tracking, saved term/depth values, monotone updates and guarded numeric upper bounds. |
| C06 | `preimage`: fixed-index and last-index `str.at`, including short/empty words and nullable target languages. |
| C07 | Replacement/containment preprocessing: observing one character when neither replacement operand contains it, including empty needle/no-match semantics. |
| C08 | Negative-containment substitution/qhead/dependency/trail updates. A genuine undo model must reverse logged operations, not simply return the expected original state. |
| C09 | Regex witness acceptance: a carefully selected Boolean-constructor and work/depth-budget slice, not full derivative/regex correctness. |
| C10 | A selected power-trichotomy f3 word identity and its guards; not full branch exhaustiveness and not merely factor-count algebra. |
| C11 | Recursive substitution expansion and termination: trace caller-maintained acyclicity before inferring any reachable loop/crash. |
| C12 | Cache/core/watch soundness and representation: trace dependency provenance, canonical clone/live fact identity and excluded facets; split this area into meaningful entries if selected. |
| C13 | Nested power-slot model reconstruction: trace producers before claiming balanced-stack safety and preserve word/exponent semantics. |
| C14 | Two separate future properties: saturating upper-length bounds, and nonnegative decimal languages with leading zeros. Split before selection. |

C04 records derivative interval exclusion/intersection as **unchanged helper
context only**. The immutable zero-context Git diff did not intersect those
implementation spans. They must not be presented as branch-introduced entry
changes; a genuinely changed caller would be needed for such a property.

A justified next batch can select fewer than ten properties. Prioritize C01,
C02, C03, C05, C06, C07 and C08; add C09 or C10 only with a faithful,
tractable complete property. C11-C13 need substantial caller/invariant work
and remain valuable coverage-driven later stages. Do not select only expected
refutations, and do not weaken source behavior to obtain positive verdicts.

## Crash-oriented observations, not crash findings

The scope is logical correctness and possible user-space crashes. Inspected
paths deliberately copy data before operations that may reallocate: replacement
propagation copies result/input/replacement/pattern/dependency; power-trichotomy
copies its power records; conversion coherence copies its term/depth pair;
interval append code copies an interval value. Regex-request propagation
continues after erase without rereading its erased reference. These are local
source observations, not a memory-safety proof or a clean native crash result.

Potential risks requiring explicit preconditions or further tracing include
`2 * pattern_length + 2` in replacement case enumeration; index/length
arithmetic and sentinel values; qhead/vector sizes across erase/pop; appended
conversion terms during callbacks; nested power-stack `.back()` operations;
and recursion/substitution graph invariants.

In `eq_facet::eliminate`, removal from `on_stack` precedes a membership check
of that same token. That warrants tracing whether callers guarantee acyclic
substitutions; it is NOT enough to claim a reachable infinite loop or crash.
Likewise, cache rewatch compares canonical clone pointers with live active
pointers: inspect actual container equality before any claim, and distinguish
a missed optimization from an incorrect logical cache hit.

## Integration and remaining coverage

Additional production diffs inspected this stage include model-evaluator power
expansion configuration; SLS derivative dispatch; Boolean-not sequence rewrites;
default-tactic regular-preprocessing gates and concat-only unconstrained
elimination; asserted-formula regular-input retention, replacement observation
rewrites, reset/pop/commit bookkeeping; nseq/character theory setup; and compact
view-witness acceptance checks. Their complete semantics and native integration
remain unproved. New tests/build registrations provide context only.

The branch's full derivative/automata equivalence, all regular preimages,
trichotomy exhaustiveness, dependency/core correctness, quantifier witnesses,
model reconstruction, AST lifetime/GC semantics and all native crashes remain
open audit areas. Files with no candidate in this bounded stage remain in the
ledger; do not treat silence as verification. Master-only missing changes
remain distinguished from branch-introduced regressions as in the first report.

## Next stage requirements

Freeze at most ten meaningful whole properties BEFORE constructing models.
Read the listed prerequisite helpers/callers, keep actual guards and update
order, and represent unsigned arithmetic honestly. Disclose any mathematical
integer, finite-state, aliasing, recursion or oracle abstraction. Do not turn
native safety into an assumption and then call it a proven safety result.
Preserve property-free validity, independent concrete domains, complete-property
proof/refutation rules, all failed attempts and original immutable artifacts.
The continuous schedule must remain enabled after this stage and after batch
publication; finishing a batch is not completion of the user's continuous goal.

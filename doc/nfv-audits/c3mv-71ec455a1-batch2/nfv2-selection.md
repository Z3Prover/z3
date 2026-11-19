# Batch 2: seven whole-property hypotheses frozen before modeling

Status: selection stage complete. No batch-2 Dafny implementation or verifier
verdict was produced in this stage. Continue with modeling on the next
scheduled turn; do not stop the continuous schedule.

## Authoritative selection

- `nfv2-selection.json`: exact selected scopes, complete positive properties,
  domains, helper requirements, correspondence limits and concrete examples.
- `nfv2-selection-source-inventory.json`: exact quotes/context from 15 pinned
  source files; captures were matched against immutable source blobs.
- `nfv2-selection-freeze.json`: byte hashes of both inputs and IDs P11-P17.
- `select_nfv2_properties.py`: deterministic generation and quote checks.

Selection SHA-256:
`be379560dc9f91cc8650d5abaa0de4e4680748d54c81be5385cc69e2131a1685`.

Head/master/merge-base and NFV upstream remain the original pinned revisions
recorded in the JSON. This is a freeze of INTENT, not a claim that model
computation/contracts have already been frozen or verified. Their separate
freeze belongs before the first original-property check.

## Selected whole properties

| ID | Source behavior and complete goal |
| --- | --- |
| P11 | The all-determined-mismatches containment discharge implies actual character-level noncontainment, for haystack `[X,a,Y]` and needle `[X,b,Z]`, distinct opaque variable identities and a!=b. Compare token identities/kinds faithfully, independently of word valuations. |
| P12 | For positive unsigned pattern lengths and legal positive case numbers, the `2*p.length()+2` admission guard agrees with the mathematical case range. Model actual 32-bit unsigned wrap, not assumed no-overflow arithmetic. This is admission only, not full replacement splitting. |
| P13 | Request propagation removes exactly resolved nonconflicting scanned requests, retains unknowns and the unprocessed suffix in order, detects the first scanned conflict, and preserves correct qhead bounds/update. Bisimulation verdicts are explicit observations for bookkeeping. |
| P14 | Both fixed-index and last-index `str.at` preimage branches agree with target-language membership, including empty/short words, allowed singleton characters and epsilon acceptance. |
| P15 | The rewritten character observation agrees with first-occurrence replacement semantics when neither needle nor replacement contains the observed character. Include empty needles, no matches and all subsequent copied characters. |
| P16 | The new vector erase-trail helper, after saving and erasing a valid slot, restores the exact original vector with its actual push/backward-shift/store undo algorithm; all modeled accesses must be in bounds. |
| P17 | Boolean regex-constructor aggregation implements the complete three-valued intersection/union result, preserving decisive short-circuiting and unknown accumulation. This is not a full regex-acceptance or resource-budget property. |

Each row counts ONE whole property, including all its conjuncts. There are
seven properties, not ten by quota. Hypothesized witnesses are candidates only:
P11 uses X=aa,Y=b,Z=epsilon,a='a',b='b'; P12 uses pattern length 2147483647 and
case one. These MUST first receive valid model/domain checks and original
positive-property checks before any whole-property negation is accepted.

## Source-grounding decisions that matter

The replacement caller in `src/smt/theory_nseq.cpp:592-611` admits nonempty
literal patterns without an explicit small-pattern bound. `zstring` exposes
an unsigned buffer length (`src/util/zstring.h:30-75`). P12 therefore does
not silently assume its multiplication/addition cannot wrap. It abstracts the
length of a valid source literal; no huge literal is allocated and no native
heap reachability or native crash result is claimed. Do not convert a numeric
counterexample into a confirmed source crash.

P15's helper must be body-defined from `src/util/zstring.cpp:120-143`:
empty needles prepend replacement, a matching nonempty needle is replaced
only once, and scanning then copies later characters. Its length restrictions
keep the selected unsigned helper arithmetic representable. It must not be
replaced by an unconstrained `ReplaceFirst` contract or a no-match-only proof.

P16 audits a genuinely NEW shared helper, not the deferred full substitution
pipeline: `src/ast/seq/seq_eq_facet.h:78-91`. The actual caller records a slot
before erase, and `src/util/vector.h:447-456` shifts left then pops. Undo pushes
the saved value, shifts backwards and restores the slot. Use that computation;
do not make restoration true by directly assigning the original vector.
Movable integer values are an explicit abstraction of request records, not a
proof of native destructor/AST/reference-count or allocator safety.

P13 and P16 are different changed functions and obligations: queue scheduling
versus exact erase/undo restoration. P11 concerns a different branch than the
first audit's prefix-pruning P1. P12 goes beyond the first audit's constant
pattern `match_at`; P14/P15 go beyond negative decimal lowering; P17 is witness
Boolean aggregation, not the earlier DFS child-status aggregation.

## Deferred rather than misrepresented

C05 callback-driven coherence needs actual callback/registration and object
lifetime contracts; copying term/depth values alone would be a weak proxy for
the proposed broad safety property. C08 full substitution/dependency/qhead
undo needs caller aliasing and dependency-graph tracing. Those remain open,
not verified. P16 does NOT discharge them.

Also retain later batches for trichotomy word identities/completeness,
substitution acyclicity, semantic cache/core justification and pointer
representation, nested model-reconstruction stack/lifetime invariants, and
separate positive-decimal/length-bound properties. C04's unchanged interval
helpers stay dependency context, not branch-introduced entry changes.

P17 deliberately selects only the Boolean aggregation branch: its child
verdicts may reflect resource exhaustion, but the shared work counter,
recursion limit, recursive acceptance, slicing and derivatives are not
proved. Do not silently add an unjustified work-counter bound to claim
resource safety.

## Next stage implementation contract

Create a NEW session workspace `nfv2-models`, models P11.dfy through P17.dfy,
and independent metadata/check evidence. Reuse/adapt the prior harness/checker
only after reading their schema. NEVER append runs to the immutable prior
P1-P10 artifacts or its 50-check record.

Read `nfv-methodology.md` for source-tag, helper-body, input/return type and
trust-escape restrictions. Read selection JSON for the complete original
goals; translating their notation into actual Dafny must preserve the whole
meaning, not weaken it. Every helper and assumption needs metadata, and all
input indices must be guarded. Preserve source loops/guards/update order and
model mathematical versus machine arithmetic explicitly. Independent domain
examples are not substitutions for general properties.

This next stage is modeling/type/provenance validation. Then the separate
verification stage checks property-free validity, independent concrete
domains, original whole properties, full negation for genuine refutations,
annotation-only proof repairs after freeze, and bounded follow-up/model fixes.
Keep every diagnostic attempt. Candidate repairs change only entry computation
and retain original input/helper contracts and entire postconditions.

Publication must include the P1 source follow-up and coverage ledger with
this new batch, preserving conditional model labels and exact evidence.
Continue the 10-second schedule after publication by choosing further genuine
coverage gaps; no empty commits or fabricated findings.

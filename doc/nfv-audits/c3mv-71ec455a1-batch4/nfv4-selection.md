# Batch 4: frozen whole-function selection

Selected exactly three distinct changed entries, not a quota or three
branches of the same function. The two completed source handoffs are hashed
prerequisites. All three are source-inferred hypotheses, not reported outcomes.

| ID | Entry | Complete obligation |
| --- | --- | --- |
| P20 | power_facet::apply_subst | Exact remove/register/rebase effects, structural state and preservation of acyclic active CURRENT-base dependencies. |
| P21 | cache_insert | Exact admission/filter/intern/core/watch effects and preservation of semantic contradiction of the whole cache under fixed per-solve background. |
| P22 | constraint_store::intern | Complete canonical ownership/ID/clone behavior on hits and misses, including hash collisions and distinct live aliases. |

P22 is a positive comparison property, not another suspected failure. It
separates canonical storage correctness from P21's semantic sufficient-premise
question and P19's already published rewatch result. All three entries are
new relative to the prior selected obligations. Changed-line overlap and exact
grounding quotes are captured before any Dafny model is constructed.

## Domains, state and concrete examples

P20 models the full power vector, original immutable token catalog, current
bases, activity, exponents, dependency handles and both flag bits. Registration
checks active keys only and occurs BEFORE rebasing the entire resulting
vector. New records get their original syntax base/exponent and null/default
metadata. The incoming dependency is deliberately ignored, as in the source.
No acyclic mutable graph is required: the original positive property contains
the implication from input graph acyclicity to output graph acyclicity.
The immutable AST catalog alone must represent finite, noncyclic syntax.
An exact graph predicate may not be replaced by assumed rank or arbitrary
execution fuel. Four complete examples cover pre-registered gpower P/Q bases,
empty replacement, deactivate/append and repeated same-key registration.

P21 uses exact finite languages on one sequence variable, each explicitly
listing words, not an oracle of satisfiability. Descriptors retain syntax
identity even if their accepted languages happen to be equal. Dependency
handles distinguish null from nonnull empty-leaf sets. Full old canonical
store, core rows, watch positions and watch buckets are inputs, not assumed
empty. The fixed background and temporary length query are separate.

Only a path ready to insert a nonempty filtered signature requires a closing
certificate: actual participating fact dependencies and any temporary length
leaf must be represented in the conflict union, and the explicitly evaluated
proof-premise language intersection plus fixed background and optional query
must be empty. A guessed length must satisfy the fixed background and each
individual signature language. This does NOT require the original joint
languages to be contradictory. No semantic unsat-core oracle or pure-signature
closure assumption is smuggled into requires.

Five complete P21 examples cover {a,bb}/{b,bb} with model length1 and fixed
lengths1,2; disabled insertion; an excluded live request; an unconditional
{a}/{b} contradiction with a pre-existing core/watch bucket; and empty
signature. Bypass examples require no closing certificate and do not claim
a native closing-state construction. P21 preserves the cache invariant as
an implication from all OLD cores being unsatisfiable, rather than assuming
arbitrary old caches are valid.

P22 represents borrowed/owned pointers as arena indices, semantic value
classes, actual unsigned64 hashes and unsigned32 stored IDs. Lookup compares
the actual low32 hash projection plus value equality. Miss clones a fresh
object, initializes its ID to UINT_MAX, explicitly assigns the old store size
and owns it. Four examples cover empty store, equal live alias, low32 hash
collision on unequal values and direct canonical-pointer hit. Allocation is
successful and hashtable membership uses its canonical ADT; physical bucket
layout, allocation failure and native equivalence are outside this model.

Every example supplies EVERY selected named input. They are frozen independent
domain candidates, not checked witnesses or predicted verifier outcomes. Input
partitions, IDs and source-size bounds remain explicit; there are no optional
restrictions, arbitrary small collection caps or hidden fresh-per-call symbols.

## Protocol and limits

Next stage constructs models and metadata in a fresh batch-4 workspace, then
seals computation/contracts. Every helper must have a body and source tags;
all meaningful helper effects remain constrained. Validity without the entry
postconditions and independent domain checks precede original whole-positive
checks. Failed proof alone is not refutation. A refutation must mechanically
negate the entire conjunction, independently pin all inputs and check its
concrete caller. Keep every failure, warning, timeout and exact input/log.

Do not replace P20's dependency graph with a direct-self-only result, P21's
semantic cache goal with leaf inclusion/eligibility, or P22's complete state
contract with returned-ID bounds. Candidate repairs can change only entry
computation with frozen helper/input contracts and the full original goal.

The gpower prestate still has a native driver/earlier-power-peel gap. The
length-query candidate still has earlier-processing, model, helper-core and
insertion/hit gaps. P19 may suppress multi-literal hits. Neither candidate is
a native crash, hang or wrong SAT/UNSAT result. Universal elimination
termination and arbitrary-regex semantic caching remain deferred. P13/P18
original complete proof gaps are unchanged, with no weaker replacements.

Artifacts: `nfv4-selection.json`, `nfv4-selection-freeze.json`,
`nfv4-selection-source-inventory.json`, and `select_nfv4.py`. Current checks
are source/provenance, changed-entry, typed-input-completeness and selection
freeze checks, not Dafny/native verification or full upstream admission gates.
Schedule2 remains active; `nfv4-model` is the next separate scheduled stage.

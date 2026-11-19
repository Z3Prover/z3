# DESLOP Review: c3mv String Solver

## Scope

This review examines the `c3mv` implementation as a code-structure review, not
as a proof of solver correctness.  The principal additions are the
domain-agnostic facet/search tree and the `nseq` theory, with substantial
preprocessing and test coverage outside that implementation.

The review found a working modular direction: AST/string facets, a trait-style
ambient context, an arithmetic subsolver, and a generic plugin-based search
tree separate several concerns better than the legacy theory monolith.  The
remaining concern is that the implementation repeatedly compensates for solver
state in special conditions, fixed thresholds, return branches, and
cross-module graph traversal.  Those mechanisms should become explicit strategy
interfaces and invariants rather than additional branch-specific code.

## Executive findings

1. **`asserted_formulas` is becoming a second string-solver driver.**  It imports
   sequence utilities and the regular simplifier, tracks string-specific state,
   and performs a custom replace/contains elimination pass.
2. **The generic search tree has a complex cache policy that needs stronger
   abstraction.**  Cache eligibility, dependency filtering, interned constraints,
   and semantic containment should be expressed by a small cache API instead of
   distributed pointer and dependency logic.
3. **The facet registry is closed and coupled.**  `ambient_context_i` maintains
   an enumerated `m_*_id` field and typed accessor for every facet.  Adding one
   facet still requires coordinated changes in several files.
4. **Several facets are policy-heavy rather than pure deterministic rules.**
   Fixed budgets, fixed witness lengths, root-visit periods, residue ranges,
   and fallback assumptions appear close to the propagation logic.
5. **Some source paths are clearly audit patches rather than stable rules.**  The
   negative-containment alignment and replace-all split should use a centralized
   token-character abstraction and width-safe arithmetic.
6. **The `nseq` theory is too large as an orchestration class.**  It combines
   facet registration, final checks, assumption forcing, model construction,
   conversion coherence, and experiment-like digit reconciliation.

## High-priority structural findings

### 1. Move string preprocessing out of `asserted_formulas`

Relevant code:

- `src/solver/assertions/asserted_formulas.h:61-64`
- `src/solver/assertions/asserted_formulas.cpp:140-150`
- `src/solver/assertions/asserted_formulas.cpp:290-410`
- `src/solver/assertions/asserted_formulas.cpp:425-442`

`asserted_formulas` now owns `nseq` regular-preprocessing state, regular-simplifier
statistics, original regular inputs, pending/complete flags, and a custom
replacement/contains rewrite.  This is a domain-specific policy in a general
preprocessing module.

The more serious problem is `simplify_replace_contains()`.  It manually walks
the whole formula graph, classifies extracted terms and replacement terms,
propagates blocked nodes through a parent map, disables itself for proofs and
quantifiers, then performs a final `expr_safe_replace`.  It is syntactic
pattern matching expressed as an imperative reachability algorithm.  Future
changes in replacement, contains, extract, sharing, or proof formatting can
invalidate the handwritten graph invariants without a local abstraction making
that risk visible.

Recommended rework:

- Define a small sequence preprocessing component with one responsibility:
  regular preprocessing and one responsibility for a replace/contains rewrite.
- Register that component through the existing assertion-preprocessing pipeline;
  do not give `asserted_formulas` direct knowledge of `"nseq"`, sequence
  operations, or `seq_regular_simplifier`.
- Represent the rewrite as a validated AST transformation with a proof/domain
  contract.  Return whether the rewrite is safe for each occurrence; do not use
  a graph-wide `blocked`/`replacements` state plus a second reachability pass.
- Keep proof-producing and quantifier behavior in the same component interface,
  even if a particular implementation declines to run.
- Do not retain raw original formula pointers in general assertion state when
  that state can be an owned preprocessing request object with scope/reset
  semantics.

### 2. Replace fixed policy thresholds with named budget and strategy objects

Relevant code:

- `src/ast/seq/seq_mem_facet.cpp:116-175`
- `src/ast/seq/seq_mem_facet.cpp:1790-1850`
- `src/smt/theory_nseq.cpp:1257-1260`
- `src/smt/theory_nseq.cpp:1430-1475`
- `src/smt/seq_solver_facet.cpp:30-37`

Examples of embedded policy include:

- profile checking only below AST depth 256;
- six letters, moduli 2 through 5, and 1,000,000 residue assignments;
- a fixed length 16 witness bound;
- root monadic asks controlled by a visit period;
- digit reconciliation after 64 SAT snapshots or when search stalls;
- a nested arithmetic solver with `max_conflicts = 100`;
- digit guesses with a magic threshold in `branch_stoi_digit`.

Some of these values are legitimate complete-or-giveup budgets.  They become
unsafe as code structure when the policy is duplicated at call sites and cannot
be observed or changed as a unit.  The magic values hide whether a branch is
exhaustive, merely heuristic, or a temporary implementation limit.

Recommended rework:

- Add a named `seq_search_policy`/`seq_search_budget` object containing resource
  limits and phase-selection choices.
- Make a result explicit as `complete`, `inconclusive`, or `cancelled`; do not
  infer the meaning from `l_undef`, a null iterator, or a `-1` state.
- Keep phase ordering (`precheck`, `word search`, `witness search`,
  `conversion reconciliation`) in theory orchestration, not in every facet.
- Move fixed constants from propagation code to policy construction and expose
  at least aggregate counters for debug/statistics.

### 3. Make the facet registry capability-based

Relevant code:

- `src/ast/seq/seq_ambient_context.h:31-78`
- `src/ast/seq/seq_ambient_context.h:80-100`
- `src/ast/seq/seq_ambient_context.h:178-202`
- `src/smt/theory_nseq.cpp:180-190`

`ambient_context_i` is a useful bridge, but it is a central closed registry:
every facet has a private id, setter, getter, typed node accessor, and
`ambient_ref` forwarding method.  Adding a facet currently requires edits to
the bridge, all three typed accessor layers, and theory registration.

Recommended rework:

- Split `ambient_context_i` into stable capabilities:
  bounds/current values, assumptions, dependency creation, arithmetic bridge,
  and model/value bridge.
- Let the node expose facets by service/interface lookup rather than a long
  sequence of sequence-facet IDs.
- Keep a registration helper, but avoid forward-declaration plus setter/getter
  pairs for every concrete facet.
- Do not put sequence-facet type knowledge in the domain-agnostic search engine;
  only the sequence ambient adapter should know concrete sequence facets.

### 4. Centralize token/word interpretation

The facets currently decide token semantics independently:

- `seq_ncontains_facet` compares individual units/opaque tokens.
- `seq_mem_facet` counts units and opaque words.
- `seq_power_facet` recognizes powers and base/period tokens.
- `seq_replace_all_facet` constructs unit and character prefixes.
- `seq_solver_facet` separately defines which tokens contribute length.

This has already produced width-sensitive bugs: a token position is not
necessarily a character offset, and "raw character" versus `unit(...)` versus
variable-width sequence terms has inconsistent meaning across facets.

Relevant code:

- `src/ast/seq/seq_ncontains_facet.cpp:128-141`
- `src/ast/seq/seq_ncontains_facet.cpp:264-301`
- `src/ast/seq/seq_solver_facet.cpp:132-155`
- `src/ast/seq/seq_replace_all_facet.cpp:215-230`

Recommended rework:

- Add a single token-view abstraction that exposes resolved unit,
  resolved string, opaque word, power, length, and character-offset properties.
- Implement alignment/window operations once in the token/word utility layer.
- Require every pruning/discharge rule to state whether its start position is
  token-aligned or character-aligned.
- Replace ad hoc unsigned threshold arithmetic with a checked/safe integer
  utility and apply the same type rules to all split counts and pattern lengths.

## Facet-specific findings

### Negative containment

`ncontains_propagation` is understandable at the level of aligned token scans,
but it contains a specialized "determined mismatch" three-valued algorithm:
matches conflict, mismatches discharge, and unknown positions remain pending.
The prefix-removal branch removes a leading token run and currently assumes
that token count equals character progress.  The full-discharge branch also
scans a token window and may treat opaque variable-width tokens as character
windows.  This is fragile future-proofing; the guard should be in a reusable
token alignment helper, not an isolated branch.

The split has a similarly special lifecycle.  It carries a condition, emits a
shorter-haystack branch, and later emits a longer-haystack fallback.  The
returned edge and append-only obligation behavior should be tested as a general
search invariant, not only through individual witness examples.

### Membership and witness search

`mem_facet` mixes several distinct services in the same class:

- membership storage and substitutions;
- profile-abstract residue conflict search;
- monadic derivative/witness search;
- short-witness assumptions;
- exact-length and model-fallback behavior.

The profile search and monadic witness search are legitimate heuristics, but
the fixed work limits and special calls in `mem_leaf_split` show the need for
explicit strategy composition.

The monadic split adds a length <=16 assumption for every singleton subject
when short-witness mode is active.  This is a search resource policy and can
become an ordering-sensitive band-aid if facts from the assumption facet,
arithmetic facet, and outer SMT context are not reconciled carefully.

The `m_pending_visits` root-period mechanism is a cross-search throttle.
Throttling should live in the monadic strategy object and carry a named budget,
not be hidden in facet state.

### Power and gpower

The power facet has substantial dedicated algebra and a large gpower
introduction/split implementation.  The period-compression branch for ground
prefixes is a concrete optimization: find the minimal repeating period, unwrap
a power token, naturalize direction, introduce a fresh power, and produce
substitution alternatives.

This is domain logic, so it is not inherently misplaced.  However, its trigger
search, period compression, power construction, and substitution broadcasting
are embedded in one split class.  Future power rules should share a power
normalization service rather than add one more special trigger.

The family should be reorganized around:

- power canonicalization;
- factor/period extraction;
- one broadcast/substitution helper;
- explicit applicable preconditions;
- one proof/justification form.

### Replace-all

`replace_all_split::apply_case` currently evaluates
`c >= 2 * p.length() + 2` using `unsigned` arithmetic.  On 32-bit/unsigned
length arithmetic this can wrap before the threshold is computed.  This is
both an audit finding and a code-style finding: index and count arithmetic
has no central width contract.

The split also mixes split case enumeration, pattern prefix construction,
character inequality constraints, fresh variables, and replacement equations.
Those should be separate helpers:

- enumerate a split case;
- construct prefix/suffix terms;
- add the character inequality;
- emit the equation pair.

This would make it possible to test case generation independently of search
node mutation.

### Equation and model-completion facets

The equation facet is modular and carries substitutions, disequations, tail
splits, and model-completion alternatives.  The main structural concern is
fallback proliferation:

- `model-completion-fallback`,
- blocked model completion,
- explicit `break` after independent words,
- assumptions only attempted once,
- return-unknown-style branches.

Fallback behavior is important, but it should be represented by an ordered
completion strategy with a result type.  "candidate rejected, fallback active,
assumptions blocked" is currently scattered across a fixture and production
callers.

### Lexicographic and request facets

These facets are comparatively disciplined: they hold pending obligations,
apply substitutions, simplify, and return `simp_result`/unknown.  The concern
is inconsistency in lifecycle and cursor ownership.  Multiple facets have
separate `qhead`, append-only vectors, rewind/advance helpers, and clone
methods.  A reusable incremental-facet base or shared pending-obligation
template would reduce future off-by-one and substitution bugs.

## Cross-module findings

### 1. SMT dependency and assumption plumbing

`ambient_context_i` and `ambient_ref` provide a good bridge, but assumptions
are currently sent to both the nested arithmetic solver and the outer
`assumption_facet`.  This dual registration is easy to drift.

Preferred structure:

- one assumption journal owned by the bridge;
- one method to add a local constraint and return a synchronized global literal;
- explicit local-only versus ambient-enforced constraint categories;
- no facet deciding by ad hoc reads of literal assignment.

### 2. The nested arithmetic solver has string-shaped special cases

`seq_solver_facet.cpp` configures the nested solver with
`string_solver=none`, sets `QF_LIA`, and limits it to 100 conflicts.  That is
appropriate isolation, but model extraction contains string-specific graph
repair:

- sequence operations are described as uninterpreted functions;
- `substr(s,i,1)` is specially normalized;
- function entries and else values are consulted manually;
- equality terms are replaced with false in model values.

This belongs behind a sequence arithmetic model adapter.  It should not remain
as handwritten model graph traversal in a general solver facet.

### 3. `theory_nseq` is a monolith

The theory contains:

- facet registration;
- model-value construction;
- assumption/literal forcing;
- search orchestration;
- STOI digit reconciliation;
- UBV sequence coherence;
- final checks;
- unknown/depth cutoff handling.

This is too many roles for a theory implementation.  Recommended split:

- `nseq_facets` / search-state assembly;
- `nseq_model_builder`;
- `nseq_search_controller`;
- `nseq_stoi_bridge`;
- `nseq_final_check` orchestration.

The bridge's logic can remain in `smt`, but each class should own one state
machine rather than the theory implementing one switch over every branch.

### 4. General search cache needs explicit semantic containment

`stx_search_tree.h` is domain-agnostic and is a good place for cache mechanics,
but constraint interning, dependency filtering, and watch rewalking are tightly
coupled.  The audit concern about canonical pointers versus semantically equal
constraints also belongs at this boundary.

The cache API should require:

- `constraint_i::equals` as the canonical semantic membership test;
- canonicalization performed once during intern;
- containment based on semantic equality, never pointer identity;
- a cache entry state machine (`watched`, `rewatched`, `fired`);
- no implicit assumption that a constraint clone retains pointer equality.

Dependency filtering should also be a separately tested cache-core function,
with tests for no-handle constraints, partial leaf sets, and inactive facets.

## Cross-facet duplication

Several mechanisms are repeated instead of shared:

- append-only obligations with `qhead`;
- trailed remove/replacement;
- substitution broadcasting;
- fresh-variable construction;
- model-completion fallback;
- assumption/constraint synchronization;
- no-progress versus unknown decisions.

Recommended rework:

- one `pending_obligation` base/utility for qhead, active, dependency, clone,
  and substitution;
- one `substitution_broadcast` helper;
- one `fresh_symbol`/skolem factory;
- one result enum for `complete`, `unknown`, `progress`, `conflict`;
- one model-completion strategy with ordered candidates and resource accounting.

## Code style and maintenance concerns

- There are many very long comments claiming soundness or exact behavior.  Those
  comments should be paired with invariant comments and targeted tests, not used
  as a substitute for type-encoding invariants.
- Several methods inspect a facet by path plus a literal assignment, such as
  `ctx.b_internalized()`/assignment/fallback logic.  A bridge method should
  return a tri-valued state and dependency in one call.
- `#if 0` and throw-on-unsupported branches remain in the sequence axiom code,
  for example `seq_axioms.cpp:1370-1373`.  Remove dead branches or preserve them
  behind a documented unsupported-feature assertion.
- Fixed magic values should not be scattered through `.cpp` files.
- `NSEQ_DUMP_UNKNOWN` and environment-driven diagnostics are useful local
  debugging but should be represented as a standard trace category.
- Public headers mix API, implementation notes, and scheduling policy.
  Split long module headers for public types and private facet implementation.
- A large number of test-only and audit-specific model words may make file
  organization noisy.  Keep general unit tests next to facet implementations,
  and keep generated/reproduction evidence under `doc/nfv-audits`.

## Highest-leverage implementation sequence

1. Introduce width-safe token/word and index arithmetic utilities.
2. Fix negative-containment alignment and replace-all case generation as reusable
   sequence rules, with property tests for interior occurrences.
3. Extract cache semantic containment and cache-core filtering into explicit
   domain-agnostic APIs with focused tests.
4. Remove direct nseq/sequence policy from `asserted_formulas`.
5. Replace fixed leaf/witness periods and thresholds with a named search policy.
6. Split `theory_nseq` orchestration from model, STOI, and facet-state classes.
7. Replace closed facet-ID setters with capability lookup or typed facet registry
   interfaces.
8. Consolidate pending-obligation and fallback lifecycles into reusable utilities.

## Final assessment

The c3mv branch is substantially modularized compared with a monolithic theory,
and most of the new code is placed in appropriate sequence directories.  The
main remaining work is to make policy and state transitions explicit:

- general modules should not know nseq-specific preprocessing;
- every fixed budget should have a named result and policy owner;
- token offsets must be either character offsets or token offsets, never
  silently interchangeable;
- cache containment must be semantic;
- facet registration and assumptions should use extensible interfaces;
- audit-finding compensations should be replaced by general invariants.

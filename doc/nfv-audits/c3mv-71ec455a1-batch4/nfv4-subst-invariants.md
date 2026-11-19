# Batch 4: producer-wise substitution source trace

Source pin: `71ec455a18702fe695d0c924a535ff9f385bd58d`.
Comparison master: `c2460a558fc6fee3cf15cfebd2d3f642ebf77770`.
Previous publication: `13cfdf0d3f046886dd16ae6aef2c9853679b4877`.

All 24 known production broadcasts now have producer guard, replacement,
normalization, dependency and activity evidence, in 16 scopes. This is a
source-only handoff: no selected property, verifier attempt, native execution,
native failure or production patch. Existing P13/P18 whole-proof gaps remain.

## Mechanisms and important limits

`seq_eq_facet.cpp:37-68,109-151,373-391`: substitution replaces whole matching
tokens, not arbitrary AST subterms. Active equations are rewritten; old stored
substitution RHS vectors are not. Lookup uses newest matching binding. The
elimination loop removes a token from its set before testing membership, so
this is not an ancestor-cycle guard. Broadcast supplies no central occurs/DAG
check, dispatches all sinks, then asserts the length equation.

`seq_power_facet.cpp:43-60`: the power sink deactivates the substituted active
power, registers replacement powers, and rebases every active current base
containing the substituted whole token. Current bases may differ from the
original term's AST base. `seq_power_facet.h:86-118`: find_power ignores
inactive records, so registration idempotence is only over active records;
a previously deactivated term can be registered again.

`seq_ambient_context.h:146-159`: freshness uses a retained cache keyed by
caller, sort and arguments. First use allocates a fresh constant; repeated
identical keys reuse it, including across search backtracking. It is not a
new constant on every invocation. Global producer/iterator frontier
invariants cannot simply assume otherwise.

`seq_mem_facet.cpp:323-345`: membership substitution snapshots old vector
size, removes old entries and adds rewritten entries. This pass does not
revisit newly appended memberships. Free helper `unfold_empty` has two direct
callers, power cpp257 and885, in the captured source.

## Exactly three concrete chain attempts

1. Simple reverse binding: start X=Y.A and Y=X.B. After X->[Y,A], the active
   second equation becomes Y=Y.A.B. The local occurs check at eq cpp302
   blocks that definition. This is not a proof over all producer histories.
2. Self-containing power variable decomposition: attempt X against power(X,n).
   The caller at power cpp922-926 requires every flattened base token to be
   a unit; variable X fails. This guard does not protect the different gpower
   introduction producer.
3. Conditional gpower/current-base chain: suppose the entry sees active
   equation [P,X]=[X,unit(a)] and registered active P=power(X,n), n symbolic.
   No prior binding is needed. The forward trigger at power cpp1087-1101
   accepts prefix [P] before target X. Single-power unwrapping at1211-1226
   replaces that prefix with [X]; the code does not recheck groundness. With
   fresh integer k and Q=power(X,k), split registers Q with base X at1241-1245
   before the first iterator call. At i=0 the token X is plain and prefix is
   empty, so1168 broadcasts X->[Q]. The power sink then rebases both active
   P and Q to current base Q. Q's current base is now its own token.

The third attempt distinguishes two graphs. Q remains the finite AST
power(X,k); its separately stored current base points to that finite token.
There is no cyclic AST allocation. The initial latest-binding graph only has
X->[Q], not a self-edge. If a subsequent fixed-exponent splitter establishes
k=1, power cpp802 emits Q->[Q]: one-copy unfolding at85-91 returns the current
base unchanged. With that binding, eq cpp128-150 cannot terminate elimination
of Q. This is a conditional source consequence, NOT a native hang finding.

Full search-driver reachability, earlier propagation, competing splitter
priority, implication success, backtracking and a later elimination call
have not been established together. No native solver was run. The ordinary
input equation even admits X="a", n=1, but mathematical satisfiability does
not establish implementation-path reachability or the subsolver's result.

## Selection handoff and evidence

A justified candidate for later selection is whole-entry invariant
preservation by `power_facet::apply_subst`, with all remove/register/rebase
effects modeled and the gpower producer prestate made explicit. Do not
silently assume a decreasing rank, globally fresh-per-call symbols, closed
substitution RHSs, or an acyclic poststate. Do not count this source trace as
a formal refutation or select a property before both batch-4 source stages.

`nfv4-subst-producer-ledger.json` contains all 24 entries and three attempts.
`nfv4-subst-source-inventory.json` preserves the original exact 1,539-line
capture and three failed lexical extraction assertions. Those are source
tool validation events, not verifier attempts. `nfv4-subst-extra-source.json`
adds exact helper/caller excerpts from six pinned files, with raw Git blob
identity, SHA-256, numbered source and worktree-text checks. The lookup for
seq_decl was corrected to seq_decl_plugin after missing paths were reported.
No restricted files were encountered. `finish_nfv4_substitutions.py` validates
all anchors, all 24 unique sites, 16 scopes and both immutable capture sets.

Next scheduled stage: `nfv4-core-provenance`. Schedule2 remains active at its
requested 10-second cadence. Publication waits for later selection/model/
verification stages; existing published histories remain immutable.

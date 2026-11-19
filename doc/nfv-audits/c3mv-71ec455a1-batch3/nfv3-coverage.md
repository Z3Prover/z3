# Batch 3 remaining-coverage refinement

Status: source-only bounded coverage stage complete. No new selected property,
model, verifier invocation, confirmed native bug, or production modification.
Read `nfv3-p12-source-trace.md` alongside this handoff. Keep the entire batch-2
P13 request-queue proof gap open; none of these candidates replaces it.

## Pins and comparison change

Audited production revision: `71ec455a18702fe695d0c924a535ff9f385bd58d`.
Latest published audit commit: `146f70d7ddf5507fdf731af2511edf4c5f669fc5`.
Remote c3mv still points to that publication. The local HEAD source tree equals
the pinned production tree.

Remote master advanced from `d738f81eab9af1468394664a812fe4310ae8e1fa` to
`c2460a558fc6fee3cf15cfebd2d3f642ebf77770`. Fetching that commit did not change
the branch or worktree. Merge base remains
`437536cd64a544a1c329fc57d83e56e294fdf47c`.

The two intervening master commits change bound_simplifier.cpp,
theory_finite_set_size.cpp, finite_set.cpp and smt_context.cpp. None overlaps
the nine files captured for this coverage stage. smt_context.cpp DOES overlap
the broader branch delta by path; do not claim global path disjointness.
The new direct master-to-source
comparison has 110 files / 93 src files, including changes introduced only on
master; the merge-base-to-source branch delta remains 104 files / 89 src files.
Do not count the new master commits' changes as newly authored c3mv code.
Previously published reports retain their original master pin; do not silently
relabel them as proofs of the advanced comparison.

## C10: complete periodic-word identities are tractable candidates

Source: `src\ast\seq\seq_power_facet.cpp:94-108,271-305,385-579`.
`power_trichotomy::apply` emits `Y^N := X^M . z` in each selected nonempty
branch. A meaningful property compares actual interpreted words, preserving
the complete constructed residual; scalar length/count equalities alone do
not establish this property. Entry arithmetic expressions are built using
the actual rewriter, not an unconstrained oracle.

For f1 preserve N>=1 and Y=X^M.y1. For f2 preserve M>=1, the actual root
construction and i,j constraints, the length guard, and signed N. A fresh
root can be empty, so the length guard does not always imply iM<=jN; do not
invent a nonempty-root restriction. Nonpositive word powers have empty-word
semantics, rather than a silently strengthened natural exponent domain.

For f3 preserve M,N>=2. The symbolic branch asserts X=(p1.p2)^k.p1 but does
not constrain fresh k to be nonnegative. The constant branch instead computes
l1=|X| mod r, p1 as the trailing l1 letters and p2 as X[l1..r); it needs a
body-defined period argument, not an assumed identical decomposition. A
period need not divide |X|. The enumerator supplies 0<r<|X| and has_period;
its optional constant-Y checks include unsigned length arithmetic. Disclose
overflow exclusions if using mathematical lengths for that enumeration.

For f4 retain M=1, q>=0, q+1<=N, Y=y1.y2 and X=Y^q.y1. Preserve orientation
and the weak/strict direction-dependent length guard. An identity proof does
not establish branch exhaustiveness, dependency provenance, substitution
lifetime safety or full equivalence to the native arithmetic backend.

The ledger proposes this whole-identity family and its period construction
for the next selection stage. It does not freeze a quota, split a whole
conjunction, or choose properties in advance of that stage.

## C11: defer universal elimination termination

Sources: `src\ast\seq\seq_eq_facet.cpp:35-68,109-151,288-307,373-398`,
all 24 captured production broadcast call sites, and the set implementation
in `src\util\obj_hashtable.h:25-58` / `src\util\hashtable.h:514-573`.

`eliminate` removes t from on_stack immediately before its contains test.
The backing table is a pointer set, with removal deleting its entry, not a
reference-counted stack multiset. The membership test therefore is not an
ancestor-cycle guard. This observation does not establish a reachable cycle,
hang or crash: a globally maintained acyclic latest-substitution graph could
still justify expansion termination.

All 24 production broadcast_subst calls in the three seq facet cpp files are
listed exactly in the ledger (11 equation, 11 power, 2 membership). Their
surrounding source is captured. This enumeration is not a producer-wise
transitive-DAG proof. Representative syntactic occurs checks and fresh-token
construction have been read; there is no uniform central occurs guard.
The equation sink appends new bindings without normalizing old RHS vectors.
Do not turn an invented rank, arbitrary fuel or assumed DAG into a claimed
source termination proof. Defer until a justified caller invariant is found.

## C12: separate missed-hit observation from semantic cache soundness

Sources: `src\util\stx_search_tree.h:570-850,1070-1106`,
`src\ast\seq\seq_eq_facet.h:145-156`, and
`src\util\vector.h:579-589`.

constraint_store uses semantic hash/equals, owns clones, and returns canonical
clone pointers by ID. compute_constraints collects borrowed live facet
pointers. try_rewatch uses vector.contains on these pointers, which tests
pointer identity. The equation clone allocates a distinct value-only object.
Consequently semantic presence of another core literal does not entail its
clone pointer's membership in the active vector. This supports a missed-hit /
performance concern and a possible failure of the documented rewatch converse,
not evidence of an unsound SAT/UNSAT result or a native crash. A false return
still requires the inspected other clone pointers to be present, a sufficient
condition for their semantic presence. No native behavior was measured.

Defer the broader obligation that conflict-dependency filtering preserves a
semantically sufficient contradiction. Leaf-set inclusion is not itself a
proof of that fact. One must justify dependency producers, excluded facets
and derived-fact provenance, rather than postulate an unsat-core oracle.

The complete cache_eligible control gate is separately tractable, but a
boolean admission-gate proof must not be presented as complete cache
soundness or selected merely to fill a batch quota. Prefer substantive word
identities if their actual source contracts can be faithfully modeled.

## Evidence and handoff

`capture_nfv3_coverage.py` uses one narrow ls-tree and one cat-file batch for
nine pinned files. It checks Git blob hashes, exact local text, all candidate
spans, 24 production-call count, unchanged source tree, and nonoverlap of the
new master paths with the nine current capture paths. Its inventory captures 1,219 exact
numbered source lines. The ledger records candidates, limitations, baselines
and the inventory SHA-256. These checks are provenance/coverage checks, not
translation equivalence or formal correctness proofs. The ledger also keeps
the failed overbroad disjointness assertion and its correction; that source
validation failure is not a Dafny attempt or a finding about solver behavior.

Next stage: nfv3-select, after both source prerequisites. Read the methodology,
freeze at most ten meaningful new whole-property intents and independent
domain witnesses before modeling in a new workspace. Preserve original
report/evidence directories and the existing stash. Schedule 2 stays active.

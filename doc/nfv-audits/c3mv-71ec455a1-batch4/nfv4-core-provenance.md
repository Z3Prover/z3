# Batch 4: conflict-dependency and cached-core provenance

Source: `71ec455a18702fe695d0c924a535ff9f385bd58d`; comparison master:
`c2460a558fc6fee3cf15cfebd2d3f642ebf77770`. This is a bounded source-only
handoff, not a formal cache-soundness proof or a confirmed native bug.

## Dependency production and scope

The capture covers sixteen new files, twelve facet registrations and 28
textual direct facet-conflict calls, including one previously captured power
call. One membership call, cpp785, is under `#if 0`; only 27 are active.
Transitive helper/oracle implementations are not exhaustively audited.

`dependency.h:190-275`: null is the empty dependency, joins preserve existing
leaf values, and null is join identity. The cache conservatively retains
facts with null handles and skips filtering entirely for a null conflict.
Null is not necessarily a missing proof: the backend can contradict only
unconditional assertions, which have no assumption handle.

`seq_solver_facet.cpp:43-106`: nonnull-dependency constraints are guarded by
assumption literals; negative solver results join the dependencies of the
returned active core. `theory_nseq.cpp:739-743` encodes outer assumptions as
odd leaf values; `seq_ambient_context.h:113-119` encodes conditional expressions
as even leaf values. `theory_nseq.cpp:815-844` reports both kinds as negated
premises. A conditional leaf can therefore name an additional hypothesis,
not an active signature fact or an unconditional theorem.

Equation/dequation producers use current-fact dependencies, ambient-false
joins or joins with used approximation views. Membership producers use own
facts, joined witness/monadic cores, arithmetic cores or length/letter joins.
Negative containment uses own facts or joins equation/ambient premises.
Request and lexical producers forward obligation or helper-cycle dependencies.
These observations do not verify reducer/oracle correctness or completeness
of every used-premise list.

`stx_search_tree.h:424-443,1145-1158`: conflict history survives branches and
depth rounds; aggregate closure joins all recorded history, not just immediate
siblings. Over-inclusion can weaken filtering; do not infer missing dependencies
merely because a cache hit has null immediate conflict dependency.

## Cache lifetime and excluded state

`stx_search_tree.h:1345-1358` clears cache entries, watches, canonical store and
conflict history at solve entry. Cache reuse spans DFS branches and iterative
deepening within that call, not different solve invocations. An outer-context
change across calls is therefore not an established stale-cache issue.

The active value signatures are equations, disequations, regex memberships and
negative containments. Clones intentionally omit dependency handles. The
eligibility gate checks `is_satisfied` on excluded facets, not literal emptiness.
In particular, `seq_solver_facet.h:131` accepts a SAT backend with live state;
`seq_power_facet.h:135` and `seq_assumption_facet.h:85` always return true.
Those exclusions can be intentional, but the gate alone cannot justify that
all omitted premises are fixed background or semantically irrelevant.

## Concrete conditional sufficiency candidate

Consider two active single-variable languages L1={"a","bb"} and
L2={"b","bb"}. Each allows lengths 1 and 2, their intersection is nonempty
("bb"), but their intersection at length 1 is empty. This mathematical
observation is not yet a checked NFV property or a native reproduction.

The witness-extraction path at `seq_mem_facet.cpp:826-913` can read an
arithmetic-model length using `sf.value`, allocate a conditional dependency
for that equality, and add an exact-length view temporarily to `view_witness`.
On a negative result it joins the helper core and sets node conflict. Scope
exit removes temporary views. The guessed view was not added to the
membership facet's signature list. The completion wrapper at958-971 can
return with that conflict; the generic driver at1000-1014,1103-1111 can then
reach cache insertion after the splitter scope unwinds.

If the backend supplies length 1, the helper reports a correct length-
conditional contradiction, earlier processing leaves these memberships
unchanged, and other excluded facets remain eligible, both membership
dependencies survive the subset filter. However, the temporary length premise
is absent from the cached value set, which still admits "bb". The missing
obligation is semantic preservation of sufficient premises, not accuracy of
the leaf-subset test itself.

Required native reachability remains unproved: earlier template/monadic
processing, competing splitters, actual model choice, helper core details,
insertion and later hit. The selected path must skip or get unknown from the
optional monadic endgame. No source was run. The previously published P19
pointer-identity mismatch may suppress multi-literal hits; an insufficient
stored core is not automatically a reachable wrong UNSAT result.

## Selection handoff

A justified next candidate is the complete `cache_insert` semantic
sufficiency/state-effect contract, using body-defined finite-language semantics
and checked length-conditional conflict premises rather than an assumed
unsat-core oracle. Include actual admission, filtering, interning and watch
effects; do not replace semantic sufficiency with an eligibility/subset theorem.
If a faithful domain cannot be justified, defer this candidate explicitly.

The separate producer-stage power-substitution invariant candidate remains
available. Registration confirms power_peel precedes gpower introduction;
this does not close that candidate's earlier driver-reachability gap.
P13/P18 original whole-property proof gaps remain unchanged.

Evidence: `nfv4-core-source-inventory.json`,
`nfv4-core-provenance-ledger.json`, `capture_nfv4_core.py` and
`nfv4-core-handoff.json`. Capture checks exact Git blob identity, SHA-256,
numbered excerpts, all listed sites, disabled-code classification, worktree
text and unchanged source tree. These are provenance checks, not translation
equivalence. The initial text assertion failed on the pinned lexical file's
536 CRLF endings. A sixteen-file diagnostic confirmed newline normalization
was the only difference. The corrected comparison normalizes newlines only
for that check; raw blob identity/hashes remain exact. The failed source-tool
attempt is retained in capture metadata, not counted as a verifier attempt.
The initial shell's later git status masked Python's nonzero exit; the
corrected invocation propagates Python failure before subsequent inspection.
No model selection, verifier invocation, native execution or
production patch occurred in this stage. Next: `nfv4-select` on the continuous
10-second schedule; publication is a later stage.

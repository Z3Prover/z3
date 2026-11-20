# Native follow-up: closing NFV audit findings P19, P21, P22

**Method: direct native C++ source review, not the Dafny/NFV translation
methodology used in `c3mv-71ec455a1-batch1` through `batch6`.** This is a
targeted code-reading exercise to establish whether the three NFV findings
below correspond to a genuine native soundness bug, continuing where
`nfv-next-triage-20261119`/`nfv-next-reproduce-20261119` left off. No model
was built or run; no production source was modified, built or executed
beyond ordinary read-only inspection.

Source reviewed: `src/util/stx_search_tree.h`,
`src/ast/seq/seq_eq_facet.{h,cpp}`, `src/ast/seq/seq_mem_facet.cpp`,
`src/ast/seq/seq_ncontains_facet.cpp` at c3mv HEAD `d246e188d`.

## P19 — semantic presence vs. canonical pointer identity

Already closed by the NFV audit itself
(`c3mv-71ec455a1-batch3/README.md`, "P19: semantic presence and canonical
pointer identity diverge"): the refuted model shows `try_rewatch` can treat
a semantically-active literal as absent under a different pointer alias.
The audit's own conclusion: *"This is a model repair, not a C++ fix ... No
false SAT/UNSAT result or native crash follows from this finding."* The
failure mode is a possible missed cache hit (conservative), never an
incorrect one. Nothing further to add from native review.

## P21 — `conflict_deps()` over-inclusion at all-children closure

**Finding confirmed, not a soundness bug.**

`node::m_conflict_deps` (`stx_search_tree.h:358-357`, comment above the
field) explicitly accumulates every dependency that contributed to an unsat
verdict *anywhere in the current `solve()` call*, across every `dfs()`
revisit of the same node at any depth, and documents that joining them into
one justification is meant to happen "once, after `solve()` returns unsat."

The all-children-closure path (`stx_search_tree.h:~1147-1154`) instead
joins the full accumulated `conflict_deps()` for an interior node, right
before `cache_insert()`:

```cpp
dep_tracker joined = nullptr;
for (dep_tracker d : n.conflict_deps())
    joined = m_dep_mgr.mk_join(joined, d);
n.set_conflict(br_children_failed, joined);
pure_out = all_children_pure && cache_eligible(n);
if (pure_out)
    cache_insert(n);
```

This can over-include dependencies from earlier, unrelated visits to `n`.
Two independent mechanisms bound the consequence to efficiency, not
correctness:

1. `filter_by_conflict_dep()` (`stx_search_tree.h:778-803`) only ever
   *removes* a fact whose leaf set is provably not a subset of
   `conflict_dep`'s leaves — an over-large `conflict_dep` just makes this
   filter less aggressive, yielding a larger-than-minimal but still
   **correct** over-approximate core (see the soundness argument in the
   comment immediately above the function).
2. `cache_lookup()` (`stx_search_tree.h:715-738`) only reports a hit when
   **every** literal in a stored core is currently active in the querying
   node (via `try_rewatch`'s absent-literal search). An over-inclusive
   stored core can only make a hit rarer, never incorrect.

Net effect: a node revisited with varying conflicts within one `solve()`
call gets a less-than-minimal cached core, reducing future hit-rate. No
path from this to a false UNSAT/SAT result was found.

## P22 — `constraint_store::intern`, hash collisions, clone/store_id ownership

**Finding confirmed as a design property, not a soundness bug.**

`constraint_store` (`stx_search_tree.h:573-613`) buckets by `hash()` (cast
to 32 bits for the bucket index in `ptr_hash`, `stx_search_tree.h:589`) and
only ever confirms identity via `equals()` — the class comment states this
directly: *"`hash()` only selects the bucket; `equals()` always confirms."*
A 32-bit-bucketed hash collision can only degrade hashtable performance,
never cause two distinct constraints to be treated as equal, **provided
every concrete `equals()` does genuine structural comparison**. Checked all
four concrete `constraint_i` subclasses; all do:

| Type | File | `equals()` |
| --- | --- | --- |
| `eq_facet::equation` | `seq_eq_facet.cpp:98` | `dynamic_cast` + `m_lhs`/`m_rhs` field equality (both orientations) |
| `deq_facet::disequation` | `seq_eq_facet.cpp:960` | same pattern |
| `mem_facet::str_mem` | `seq_mem_facet.cpp:386` | `dynamic_cast` + `m_str`/`m_view` field equality |
| `ncontains_facet::str_ncontains` | `seq_ncontains_facet.cpp:98` | `dynamic_cast` + `m_haystack`/`m_needle` field equality |

None uses a hash comparison as an equality shortcut.

Clone/ownership: `constraint_i::m_store_id` (`stx_search_tree.h:122`)
defaults to `UINT_MAX` and is set only on the store's own `clone()` inside
`intern()` (`stx_search_tree.h:~606`), never on the facet-owned borrowed
original. Every consumer (`constraint_store::find()`,
`stx_search_tree.h:~593-598`, and `cache_lookup()`) reads `store_id()` from
the result of a `find()`/hashtable lookup — i.e. always from the store's
own clone — never from a facet-owned reference directly. No aliasing
between the two ownership copies' IDs was found.

## Disposition

P19, P21 and P22 are closed: each is a real, specific, confirmed property
of the current implementation, and each is bounded to an efficiency
(reduced cache hit-rate / bucket distribution) consequence rather than a
soundness one, by an explicit, checkable mechanism in the surrounding code
(the subset filter, the active-literal hit requirement, or genuine
structural `equals()`). No native reproduction, regression test or source
change follows from this review, consistent with the audit's own standing
priority: soundness/correctness bugs, not algorithmic performance work, are
in scope for this pass.

P20 (`power_facet::apply_subst` — self-rebase/later self-binding
elimination, active-equation occurs checks, unit-base guards) remains the
one NFV finding in this group that is genuinely unresolved (the Dafny side
reports "resources exhausted before positive check," neither proved nor
refuted) and is the next item under native review.

## P20 — theoretical concern noted, not confirmed

**Disposition: theoretical concern noted, not confirmed as a native bug.**

`power_facet` has been substantially rearchitected since the audited
snapshot (`71ec455a18702fe695d0c924a535ff9f385bd58d`): there is no longer a
separate "current base" indirection that a power obligation's base could be
repointed at (the mechanism the batch4 trace — `nfv4-subst-invariants.md`,
"Conditional gpower/current-base chain" — relies on). `apply_subst`
(`seq_power_facet.cpp:43-59`) now rebases in place by substituting directly
into `m_s`'s token list (`subst_in`) and rebuilding it via `mk_concat`. The
exact reproduction the Dafny side traced does not carry over mechanically.

The per-step substitution gate (`eq_facet::simplify_equation`,
`seq_eq_facet.cpp:293-303`) uses `ast/occurs.h`'s `occurs()`, a standard,
full recursive AST traversal (`quick_for_each_expr`,
`src/ast/occurs.cpp:65-73`) — not a shallow/token-level check. This
directly guards against a variable being bound to a replacement containing
it as a nested subterm (e.g. inside a `power(x,k)` token), which is a
likely improvement over the weaker check the audit's batch4 trace implies
for the old architecture.

A separate, not-yet-excluded risk was identified by inspection:
`eq_facet::eliminate()` (`seq_eq_facet.cpp:128-148`) walks a substitution
chain with an `on_stack` set seemingly meant to catch cycles, but the
`on_stack.remove(t)` happens immediately when `t` is popped, before the
`!on_stack.contains(t)` check runs — making that check close to vacuous as
a cycle-breaker on a straightforward reading. Combined with the audit's own
note that "old stored substitution RHS vectors are not rewritten" when a
referenced variable is later itself eliminated, a *transitive* (multi-step,
not single-step) cycle could in principle bypass the per-step occurs-check
in `simplify_equation` and reach this code.

Three concrete SMT2 constructions were tried, none reproduced a hang:

1. `Y = X ++ a`, `X = Y ++ b`, `a`/`b` free — resolves `sat` in ~0.07s
   (length arithmetic forces `a = b = ""`, a trivial fixed point).
2. Same with `len(a) = len(b) = 1` asserted — resolves `unsat` in ~0.08s
   (length arithmetic alone: `len(Y) = len(X) + 1` and
   `len(X) = len(Y) + 1` contradict).
3. Case 1 with `:model_validate true` and `(get-model)` — resolves `sat`
   with a correct, validated model (`X = Y = a = b = ""`) in ~0.08s.

A direct two-variable mutual back-reference is mathematically forced by
length arithmetic to either contradict or trivialize, so it cannot reach
the deeper string-level elimination path regardless of the code's own
protections — these tests do not probe the actual concern. Constructing an
input that does (a longer variable chain, or one directly involving
`power`, matching the audit's original scenario) would need substantially
more targeted construction with uncertain payoff, and was not pursued
further by user agreement: **conclusion is "theoretical concern noted, not
confirmed," not "ruled out."** A future session revisiting P20 should start
from a 3+-variable chain or a `power`-involving construction rather than a
direct two-variable cycle.

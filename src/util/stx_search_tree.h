/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    stx_search_tree.h

Abstract:

    Domain-agnostic plugin-based search tree (namespace `stx`).

    This implements the trail/iterator-based architecture described in the
    (updated) design document "A Modular Plugin-Based Search Tree for
    String Solving" (based on `theory_nseq` / `nielsen_graph` on the c3
    branch). It provides a generic engine that knows nothing about
    sequences, strings, or automata: it manages a *single mutable node*,
    dependencies, conflict explanation, iterative deepening, subsumption,
    and backtracking over an abstract node *state*, which is a collection
    of *facets* contributed by plugins.

    Unlike the earlier (Phase 1-4) revision of this file, nodes are no
    longer persistent/clone-per-edge: there is exactly one live `node`
    object per `search_tree`, and "descending into a branch" means
    destructively mutating that node's facets while registering undo
    actions on a shared `trail_stack` (util/trail.h, reused verbatim).
    Backtracking out of a branch means popping that trail scope, which
    restores every mutated facet's prior state without any cloning.
    `facet_i::clone()` still exists, but only for cold-path use (hot
    restart's post-solve snapshot of a SAT leaf); it is never used on the
    DFS hot path itself.

    The two extension points are:
      - `propagation_plugin_i`: deterministic, non-branching simplification.
        Mutations MUST register with the trail; must NEVER call
        `push_scope()` itself (that is the DFS driver's job, via
        `scoped_push`).
      - `split_plugin_i`: nondeterministic branching (search) rules,
        selected lowest-cost-first. `split()` now materializes the first
        available branch immediately (mutating the live node in place and
        pushing exactly one trail scope) and returns a `split_iterator_i`
        for resuming the remaining branches on backtrack.

    Everything domain-specific (string equalities, regex memberships,
    arithmetic constraints, ...) is expected to live *outside* this file, in
    facet/plugin implementations that only interact with the engine through
    `facet_i`, `propagation_plugin_i`, and `split_plugin_i`.

Author:

    Nikolaj Bjorner (nbjorner) 2026
    Clemens Eisenhofer 2026
    Margus Veanes 2026

--*/
#pragma once

#include "util/util.h"
#include "util/vector.h"
#include "util/dependency.h"
#include "util/trail.h"
#include "util/statistics.h"
#include "util/scoped_ptr_vector.h"
#include "util/rlimit.h"
#include <string>
#include <memory>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <climits>
#include <ostream>
#include <sstream>
#include <fstream>
#include <chrono>

namespace stx {

    // Result of a deterministic propagation pass. `noop` means this call
    // made no change to the node's facets (used by propagate_to_fixpoint()
    // to detect a fixed point without a structural fingerprint); `proceed`
    // means it made some change but reached neither a conflict nor a
    // satisfied state.
    enum class simplify_result { noop, proceed, conflict, satisfied };

    // Result of solve()/dfs(). `depth_cutoff` is an internal-only variant
    // of `unknown` used by dfs() to distinguish "this subtree was
    // truncated by the current depth bound" (retrying with a larger bound
    // may resolve it) from a genuine stuck/no-more-splits `unknown`
    // (retrying will not help); `solve()`'s iterative deepening uses this
    // to decide whether to keep raising the depth bound, but never
    // returns `depth_cutoff` itself to callers - it is normalized to
    // `unknown` in the final result.
    enum class search_result { sat, unsat, unknown, depth_cutoff };

    // A stable per-plugin handle into a node's facet array.
    using facet_id = unsigned;

    // Reason a node/subtree was closed. Plugin-defined, engine-opaque; the
    // core reserves 0 for "unevaluated" and a small value for its own
    // generic reason (children all failed); plugins should use values
    // >= br_plugin_base.
    using backtrack_reason = unsigned;
    const backtrack_reason br_unevaluated     = 0;
    const backtrack_reason br_children_failed = 2;
    const backtrack_reason br_plugin_base     = 3; // first value free for plugin use

    // Shared helper for `constraint_i::hash()` implementations: hash one
    // whole fact's canonical encoding (as built by the concrete
    // constraint's own e.g. sig_encode_pair-style helper) down to a
    // single opaque uint64, salted with a facet-specific tag so
    // identically-shaped encodings from different constraint kinds never
    // collide. `hash()` need only be a good bucket selector - it is
    // never trusted alone (`constraint_store` always follows a hash
    // match with an exact `equals()` check, so an occasional collision
    // between unrelated facts is harmless, merely a wasted equality
    // check) - but should still be built from the *whole* fact, not just
    // one of its sub-terms (e.g. a shared character literal or skolem
    // reused across many unrelated equations), so that in practice
    // distinct facts rarely collide.
    inline uint64_t stx_hash_fact(uint64_t tag, vector<uint64_t> const& enc) {
        uint64_t h = 1469598103934665603ull ^ (tag * 1099511628211ull);
        for (uint64_t v : enc) {
            h ^= v;
            h *= 1099511628211ull;
        }
        return h;
    }

    /**
     * Domain-opaque handle for ONE atomic fact a facet contributes to the
     * unsat-cache (e.g. a word equation, a disequation, a regex
     * membership). Unlike the earlier uint64_t-hash-based signature
     * scheme, facets now subclass this directly on their own live
     * fact-holding element type (e.g. `seq::eq_facet::equation` IS-A
     * `constraint_i`) and hand the engine borrowed pointers to their own
     * (currently active) elements - no separate encode-to-uint64_t step,
     * and no reliance on hash values alone for equality (a hash
     * collision between two unrelated facts can never cause a false
     * unsat-cache hit, because `search_tree::constraint_store` always
     * follows up a hash match with an exact `equals()` check).
     *
     * `hash()`/`equals()` must implement whatever canonicalization makes
     * two structurally-interchangeable facts compare equal (e.g. a word
     * equation `x = y` and a mirrored `y = x` - both possible outputs of
     * Nielsen branching depending on split order - must hash/compare
     * identically); `equals()` must return false for two constraints of
     * different concrete (sub)type, even if by some coincidence their
     * hashes matched (a plain `dynamic_cast` check is the simplest way to
     * guarantee this, and is already used elsewhere in this codebase,
     * e.g. `seq_eq_facet.cpp`'s ambient-context lookups).
     *
     * `clone()` allocates a fresh, independent, heap-owned copy holding
     * just the comparison-relevant state: the dependency-tracking and
     * active/alive bookkeeping fields a *live* fact carries (e.g.
     * `equation::m_dep`, `::m_active`) are never meaningful once memoized
     * into the constraint_store (a stored entry is a pure value, never
     * mutated or backtracked, and its identity is only ever queried via
     * `hash()`/`equals()`), so `clone()` need not copy them - a
     * default-constructed/omitted dependency and `active()==true` are
     * both fine.
     */
    class constraint_i {
    public:
        virtual ~constraint_i() = default;
        virtual uint64_t hash() const = 0;
        virtual bool equals(constraint_i const& other) const = 0;
        virtual constraint_i* clone() const = 0;
    };

    /**
     * Domain-opaque marker base class for an "ambient context" handle
     * stashed on a `search_tree::node` and reachable from every facet
     * registered against that node. This class deliberately has NO
     * virtual methods and NO dependency on any domain type (in
     * particular, nothing from `src/ast`): `stx_search_tree.h` is a
     * domain-agnostic engine and must not know what an `expr*` or a
     * `dep_tracker` is. The domain layer (e.g. `ast/seq/
     * seq_ambient_context.h`'s `ambient_context_i<dep_tracker_t>`)
     * derives its concrete, method-bearing interface from this class;
     * facets that need to query it hold a `facet_i::ambient()`-style
     * accessor that `static_cast`s this base pointer back down to the
     * domain's own `ambient_context_i` type (see e.g. `seq::eq_facet::
     * ambient()` in `ast/seq/seq_eq_facet.h`).
     */
    class ambient_context_base {
    public:
        virtual ~ambient_context_base() = default;
    };

    /**
     * One constituent of a node's state. Plugins define concrete subclasses
     * (e.g. an `eq_facet`, a `solver_facet`); the engine interacts only
     * through this interface, and never inspects a facet's contents.
     *
     * Every concrete facet is constructed with a reference to the shared
     * `trail_stack`, so that its own destructive mutator methods (defined
     * by the plugin, not by this interface) can register undo objects
     * (`m_trail.push(some_trail_object)`) instead of allocating a fresh
     * clone per mutation. `push_scope()`/`pop_scope()` themselves are never
     * called by a facet or plugin - only the DFS driver (via `scoped_push`)
     * owns scope boundaries.
     */
    class facet_i {
    protected:
        trail_stack& m_trail;
    public:
        explicit facet_i(trail_stack& trail) : m_trail(trail) {}
        virtual ~facet_i() = default;

        // Cold-path deep-clone, e.g. for a hot-restart snapshot of a SAT
        // leaf's facets (taken outside the live trail before it unwinds).
        // NOT used on the DFS hot path.
        virtual facet_i* clone(trail_stack& trail) const = 0;

        // Scope-boundary hooks, called by the engine (never by a facet or
        // plugin) in lockstep with the shared trail's push_scope()/
        // pop_scope(): push() immediately after a trail scope is opened,
        // pop() immediately before/alongside the matching trail unwind.
        // Default no-ops; a facet overrides these only if it maintains
        // scope-local state that isn't already trail-object-based.
        virtual void push() {}
        virtual void pop() {}

        // Is this facet's constraint set trivially/vacuously satisfied
        // (e.g. no equations left, or an empty membership set)?
        virtual bool is_satisfied() const = 0;

        // Print this facet's internal state (e.g. its pending equations/
        // disequations/memberships) for diagnostics. Default: print
        // nothing (a facet only needs to override this to be useful in
        // debugging output); the engine never relies on the output being
        // present.
        virtual std::ostream& display(std::ostream& out) const { return out; }

        // --- unsat-cache signature (see search_tree::m_unsat_cache) ---
        //
        // Does this facet's current state contribute to the transposition-
        // table signature used to memoize string-only UNSAT nodes? Default
        // false: a facet that doesn't override this is conservatively
        // excluded from the signature, and any node where it currently
        // holds live (non-vacuous, i.e. !is_satisfied()) content is made
        // ineligible for the cache altogether (see search_tree::
        // cache_eligible) - this is what keeps the cache sound without
        // needing per-facet "did I actually cause this conflict"
        // bookkeeping: a facet opting out only ever forfeits its own
        // caching benefit (e.g. the arithmetic backend, whose bounds are
        // deliberately excluded the same way c3's cache excludes length/
        // arithmetic from its node signature), it can never cause an
        // unsound hit.
        virtual bool contributes_to_signature() const { return false; }

        // Append a BORROWED `constraint_i const*` per currently *active*
        // fact/constraint this facet owns (e.g. one pointer per active
        // equation, one per active membership) to `out`. Order does not
        // matter (the engine canonicalizes by interning each pointee into
        // `search_tree::constraint_store` and, where order-sensitivity
        // matters at all - e.g. `cache_insert`'s insertion-time dedup -
        // sorting the resulting dense ids itself), so a facet needs no
        // internal self-sorting of its own the way the old uint64_t-hash
        // scheme required.
        //
        // Each pointer must point at an object whose `hash()`/`equals()`
        // pair implements the SAME fact this facet's own is_satisfied()/
        // display() logic reasons about - the unsat cache (search_tree::
        // cache_lookup) tests these for SET CONTAINMENT against a totally
        // unrelated node, so equals() returning true must mean "this
        // exact whole fact is active in both nodes", never merely "some
        // sub-term this fact happens to use is active in both" (e.g. a
        // shared character literal or skolem var also appearing in many
        // other, unrelated facts) - that would make containment across
        // unrelated nodes unsound.
        //
        // The pointers are only read synchronously during this call and
        // the (also synchronous) `constraint_store::intern()`/`find()`
        // call that immediately follows it - never retained past that -
        // so they may (and normally do) point directly at this facet's
        // own live, currently-active elements (no extra allocation needed
        // just to compute a signature); if `constraint_store` needs to
        // memoize a genuinely new fact, it calls `clone()` itself to make
        // an independent, permanently-owned copy. Only ever called when
        // contributes_to_signature() is true; default no-op.
        virtual void append_constraints(vector<constraint_i const*>& out) const {}
    };

    /**
     * Domain-agnostic plugin-based search tree.
     *
     * `dep_source_t` is supplied by the instantiating domain (e.g. a
     * `std::variant<sat::literal, enode_pair>` for a sequence solver) and is
     * the leaf payload type of the dependency arena (`util/dependency.h`'s
     * `scoped_dependency_manager`, reused verbatim - it is already fully
     * generic).
     */
    template <typename dep_source_t>
    class search_tree {
    public:
        using dep_manager_t = scoped_dependency_manager<dep_source_t>;
        using dep_tracker   = typename dep_manager_t::dependency*;

        class node;

        // A pure value type: a named transformation, with a
        // dependency-tracked justification and an iterative-deepening
        // cost. There is only one live `node` at a time, so an edge no
        // longer carries src/tgt pointers; it exists purely to describe
        // *how* the (in-place) mutation that already happened got there,
        // for diagnostics/explanation.
        class edge {
            const char*       m_rule_name = "";
            dep_tracker       m_dep = nullptr;
            bool              m_is_progress = true;
            unsigned          m_cost = 0;
        public:
            edge() = default;
            edge(char const* rule_name, dep_tracker dep, bool is_progress, unsigned cost = 0) :
                m_rule_name(rule_name), m_dep(dep), m_is_progress(is_progress), m_cost(cost) {}
            char const* rule_name() const { return m_rule_name; }
            dep_tracker dep() const { return m_dep; }
            bool is_progress() const { return m_is_progress; }
            unsigned cost() const { return m_cost; }
        };

        // Resumable iterator over the remaining branches of a split that
        // has already materialized (and the driver has since backtracked
        // out of) its first branch. The driver pushes exactly one trail
        // scope immediately before every `next()` call (popping it again
        // if `next()` returns false), so `next()` itself must NEVER call
        // push_scope()/pop_scope() - only the scope-owning driver does
        // that. `next()`:
        //   - on success: destructively mutates the live node via the
        //     owning facet's own mutator method(s), registering trail undo
        //     objects as it goes, fills `out`, and returns true.
        //   - on failure (no more branches): must not touch the node, and
        //     returns false (the driver undoes the scope it pre-pushed for
        //     this call).
        class split_iterator_i {
        public:
            virtual ~split_iterator_i() = default;
            virtual bool next(edge& out) = 0;
        };

        // Deterministic, non-branching simplification. Must be confluent:
        // repeated application (in any order, interleaved with other
        // propagation plugins) converges to the same fixed point. May touch
        // only the facet kind(s) it was registered against, and any
        // mutation must register a trail undo object (never call
        // push_scope()/pop_scope() itself).
        class propagation_plugin_i {
        public:
            virtual ~propagation_plugin_i() = default;
            virtual char const* name() const = 0;
            // Run one pass over `n`. Return `conflict` if `n` is now
            // provably unsatisfiable (call `n.set_conflict(reason, dep)`
            // first), `satisfied` if `n` is now trivially satisfied,
            // `noop` if this pass made no change to `n` at all, and
            // `proceed` if it made some change but reached neither of the
            // above. The engine's propagate_to_fixpoint() relies on every
            // plugin reporting `noop` accurately to detect the fixed
            // point (a round where every plugin reports `noop`) - a
            // plugin that mutates `n` must never report `noop`.
            virtual simplify_result propagate(node& n) = 0;

            // Add this plugin's own use counters (e.g. "times invoked",
            // "times it made a change") to `st`, keyed by name() (or a
            // more specific sub-key); a subclass overrides this to expose
            // whatever counters it maintains in its own `stats` struct.
            // Default: no-op (a plugin need not track anything).
            virtual void collect_statistics(::statistics& st) const {}
            // Reset this plugin's own internal `stats` struct to zero.
            // Default: no-op.
            virtual void reset_statistics() {}
        };

        // Nondeterministic branching (search) rule. Unlike
        // `propagation_plugin_i`, a split rule has no fixed priority of its
        // own: the driver assigns a `cost` (an iterative-deepening bound
        // over branch expense, not tree depth) and repeatedly asks whether
        // the plugin has a split available at exactly that cost, starting
        // at 0 and increasing. The driver pushes exactly one trail scope
        // immediately before every `split()` call (popping it again if the
        // call declines to commit a branch), so `split()` itself must
        // NEVER call push_scope()/pop_scope() - only the scope-owning
        // driver does that; all scope management for both `split()` and
        // `split_iterator_i::next()` happens in one place in the engine.
        class split_plugin_i {
            unsigned m_min_cost = 0;
        public:
            virtual ~split_plugin_i() = default;
            virtual char const* name() const = 0;

            // Cheapest cost at which this plugin might ever offer a
            // split (a static lower bound, set once via set_min_cost()
            // - typically at construction). extend_node() consults this
            // before calling split() at all, so a plugin whose splits
            // only ever appear at cost >= k need not itself re-check
            // `cost < k` in every split() override; the engine already
            // skips those calls entirely. Default: 0 (no lower bound;
            // split() is tried starting at cost 0, as before).
            virtual unsigned min_cost() const { return m_min_cost; }
            void set_min_cost(unsigned c) { m_min_cost = c; }

            // - A split exists at exactly `cost`: materialize the FIRST
            //   branch immediately (mutate `n`'s own facet(s) via their
            //   mutator methods, registering trail undo objects - but do
            //   NOT push a scope), fill `out`, and return a (possibly
            //   null, if there is only one branch) `split_iterator_i` for
            //   the remaining branches. The driver has already pushed the
            //   scope this branch's mutations land in; it detects "did
            //   this plugin commit a branch" via a separate `committed`
            //   out-flag rather than by inspecting the trail's scope
            //   count (which no longer changes here).
            // - No split at `cost` but one exists at a higher cost: leave
            //   `n`/the trail untouched, set `has_more = true`, and return
            //   nullptr.
            // - Nothing left to offer `n` at any cost: leave `n`/the trail
            //   untouched, set `has_more = false`, and return nullptr.
            // `committed` must be set to true iff a branch was
            // materialized in `n` (the always-fresh, pre-pushed scope for
            // this call), regardless of whether the returned iterator is
            // null (single-branch case) or non-null.
            virtual scoped_ptr<split_iterator_i> split(node& n, unsigned cost, edge& out, bool& has_more, bool& committed) = 0;

            // Add this plugin's own use counters to `st`, keyed by
            // name() (or a more specific sub-key); a subclass overrides
            // this to expose whatever counters it maintains in its own
            // `stats` struct. Default: no-op.
            virtual void collect_statistics(::statistics& st) const {}
            // Reset this plugin's own internal `stats` struct to zero.
            // Default: no-op.
            virtual void reset_statistics() {}
        };

        enum class node_status { unevaluated, satisfied, conflict };

        // The single mutable node. Holds one facet_i* per registered
        // facet_id (installed once, at root-construction time, and
        // thereafter mutated in place by plugins through trail-registered
        // undo objects - never replaced/re-`set_facet`'d mid-search).
        class node {
            friend class search_tree;

            ptr_vector<facet_i>  m_facets;          // indexed by facet_id
            node_status          m_status = node_status::unevaluated;
            backtrack_reason     m_reason = br_unevaluated;
            dep_tracker          m_conflict_dep = nullptr;
            // Every dependency that contributed to an unsat verdict
            // anywhere in the current solve() call, in the order
            // discovered. Only cleared by solve() itself before a new
            // search begins - never by clear_status() - since dfs()
            // revisits this same node at every depth/branch and each
            // contributing dependency must survive across all of them.
            // No joining happens during search; a caller that needs a
            // single combined justification joins over this vector once,
            // after solve() returns unsat.
            vector<dep_tracker>  m_conflict_deps;

            // Not owned; set once (search_tree::set_ambient_context(),
            // typically right after mk_root()) and thereafter reachable
            // from every facet registered against this node via
            // `ambient()`. See `ambient_context_base`'s comment above for
            // why this is stored as an opaque, method-free base pointer
            // here rather than the domain's own `ambient_context_i`.
            ambient_context_base* m_ambient = nullptr;

            explicit node(unsigned num_facets) {
                m_facets.resize(num_facets, nullptr);
            }

        public:
            ~node() {
                for (auto* f : m_facets) dealloc(f);
            }

            // Opaque ambient-context handle, or nullptr if none was ever
            // set. Facets/plugins that need the domain's own method-
            // bearing interface `static_cast` this down to it (see e.g.
            // `seq::eq_facet::ambient()`).
            ambient_context_base* ambient() const { return m_ambient; }
            void set_ambient(ambient_context_base* ac) { m_ambient = ac; }

            unsigned num_facets() const { return m_facets.size(); }

            facet_i& facet(facet_id id) { SASSERT(m_facets[id]); return *m_facets[id]; }
            facet_i const& facet(facet_id id) const { SASSERT(m_facets[id]); return *m_facets[id]; }
            bool has_facet(facet_id id) const { return id < m_facets.size() && m_facets[id] != nullptr; }

            template <typename T> T& facet_as(facet_id id) { return static_cast<T&>(facet(id)); }
            template <typename T> T const& facet_as(facet_id id) const { return static_cast<T const&>(facet(id)); }

            // Install the facet at `id` (root-construction time only).
            // Takes ownership. NOT for mid-search mutation - facets mutate
            // themselves in place via their own mutator methods.
            void install_facet(facet_id id, facet_i* f) {
                SASSERT(!m_facets[id]);
                m_facets[id] = f;
            }

            // AND over all installed facets' is_satisfied().
            bool is_satisfied() const {
                for (auto* f : m_facets)
                    if (f && !f->is_satisfied())
                        return false;
                return true;
            }

            // Scope-boundary fan-out to every installed facet, called by
            // the engine's scoped_push/pop() in lockstep with the shared
            // trail's push_scope()/pop_scope().
            void push_facets() {
                for (auto* f : m_facets)
                    if (f) f->push();
            }
            void pop_facets() {
                for (auto* f : m_facets)
                    if (f) f->pop();
            }

            node_status status() const { return m_status; }
            bool is_conflict() const { return m_status == node_status::conflict; }

            void set_conflict(backtrack_reason r, dep_tracker dep) {
                m_status = node_status::conflict;
                m_reason = r;
                m_conflict_dep = dep;
                // Leaf conflicts (reported by a propagation plugin) carry
                // a real dependency and are recorded here. Aggregate
                // conflicts (all branches of a split failed) have no
                // dependency of their own - each contributing branch
                // already recorded its own dependency when it hit its
                // conflict - so there is nothing new to add to the vector.
                if (dep)
                    m_conflict_deps.push_back(dep);
            }
            void set_satisfied() { m_status = node_status::satisfied; }
            void clear_status() { m_status = node_status::unevaluated; m_reason = br_unevaluated; m_conflict_dep = nullptr; }

            // Called once by solve() before a new search begins; NOT by
            // clear_status(), which runs on every dfs() re-visit of this
            // same node throughout the search.
            void clear_conflict_deps() { m_conflict_deps.reset(); }

            backtrack_reason reason() const { return m_reason; }
            dep_tracker conflict_dep() const { return m_conflict_dep; }
            vector<dep_tracker> const& conflict_deps() const { return m_conflict_deps; }

            // Cold-path: snapshot every installed facet into a standalone
            // node not tied to any live trail scope (used by hot restart to
            // preserve a SAT leaf's facet state across the trail unwinding
            // back to root).
            node* clone(trail_stack& trail) const {
                node* n = alloc(node, m_facets.size());
                for (facet_id id = 0; id < m_facets.size(); ++id)
                    if (m_facets[id])
                        n->m_facets[id] = m_facets[id]->clone(trail);
                n->m_status = m_status;
                n->m_reason = m_reason;
                n->m_conflict_dep = m_conflict_dep;
                n->m_ambient = m_ambient;
                return n;
            }
        };

        // RAII guard around one DFS branch descent: pushes a trail scope
        // and fans out node::push_facets() on construction; pops both
        // (unwinding every trail object registered since, and calling
        // node::pop_facets()) on destruction - including through an
        // exception, so a plugin/facet throwing mid-mutation cannot leave
        // the shared node and trail in a mismatched state relative to the
        // DFS call stack. Internal to search_tree; use search_tree::pop()
        // for a one-shot trail+node pop outside of a scoped_push. Always
        // operates on the single live node (m_tree.m_root) - there is only
        // ever one.
        class scoped_push {
            search_tree& m_tree;
            bool         m_active = true;
        public:
            explicit scoped_push(search_tree& tree) : m_tree(tree) {
                m_tree.m_trail.push_scope();
                m_tree.m_root->push_facets();
            }
            ~scoped_push() { if (m_active) m_tree.pop(); }
            scoped_push(scoped_push const&) = delete;
            scoped_push& operator=(scoped_push const&) = delete;
            // Release without popping (ownership of the scope has been
            // transferred elsewhere, e.g. to a surviving split_iterator_i).
            void release() { m_active = false; }
        };

        struct stats {
            unsigned m_num_solve_calls  = 0;
            unsigned m_num_dfs_nodes    = 0;
            unsigned m_num_sat          = 0;
            unsigned m_num_unsat        = 0;
            unsigned m_num_unknown      = 0;
            unsigned m_max_depth        = 0;
            unsigned m_num_cache_hits   = 0;
            std::unordered_map<std::string, unsigned> m_propagate_counts;
            std::unordered_map<std::string, unsigned> m_split_counts;
            void reset() { *this = stats(); }
        };

    private:
        // Per-depth bookkeeping for the (recursive) DFS driver. Replaces
        // what used to live directly on a persistent `node` object: since
        // there is only one live node now, everything that varies by DFS
        // depth (the winning split's resumable iterator, its
        // last-produced edge) must live on the call stack instead.
        struct dfs_frame {
            scoped_ptr<split_iterator_i>           m_iter;                // resumable remaining branches, if any
            edge                                   m_last_edge;
        };

        unsigned                              m_next_facet_id = 0;
        scoped_ptr_vector<propagation_plugin_i> m_prop_plugins;  // owned
        scoped_ptr_vector<split_plugin_i>       m_split_plugins; // owned
        scoped_ptr<node>                      m_root;
        trail_stack&                            m_trail;
        reslimit&                               m_limit;
        unsigned                               m_max_search_depth = 1000;
        unsigned                               m_depth_bound = 0; // current iterative-deepening bound, set by solve()
        unsigned                               m_max_cost = 1000;
        unsigned                               m_max_nodes = 0; // 0 == unlimited
        // Physical dfs() call-nesting counter: unlike `depth` (the logical
        // iterative-deepening bound argument, which is NOT incremented for
        // "free" progress edges - a variable eliminated, an arithmetic
        // decision), this counts every recursive dfs() invocation regardless
        // of edge kind. A long chain of free progress edges (e.g. a bound
        // propagation that converges one unit at a time) can recurse far
        // deeper than `m_depth_bound` ever sees, since the logical depth
        // never advances - risking a native stack overflow rather than a
        // clean depth_cutoff. This is a pure stack-safety backstop, set
        // generously above any depth iterative deepening would reasonably
        // reach; tripping it degrades to the already-handled depth_cutoff
        // result (retried at a larger bound / eventually reported unknown),
        // never changes the answer on well-behaved inputs.
        unsigned                               m_raw_dfs_depth = 0;
        static const unsigned                  m_max_raw_dfs_depth = 3000;
        // Starting bound for solve()'s doubling loop (see set_min_search_depth()).
        // Every call to solve() otherwise restarts iterative deepening from 1,
        // re-exploring the same shallow, provably-insufficient rounds each time -
        // wasteful once the caller already knows some floor (e.g. the number of
        // top-level constraints just asserted) below which no split sequence can
        // possibly finish. This is a pure performance floor: solve() still runs
        // the doubling loop and any depth_cutoff still triggers further deepening,
        // so soundness/completeness are unaffected by any value here.
        unsigned                               m_min_search_depth = 1;

        // iterative deepening doubles the bound (as c3), clamped so the maximum is still tried
        unsigned next_depth_bound(unsigned d) const { return d >= m_max_search_depth ? m_max_search_depth + 1 : std::min(2 * d, m_max_search_depth); }
        dep_manager_t                          m_dep_mgr;
        stats                                  m_stats;

        // --- unsat cache (watch-list based unsat-core memo) ---
        //
        // Unlike c3's m_unsat_node_cache (a set of persistent nielsen_node*
        // pointers - c3 keeps every historical node alive until reset()),
        // this engine has exactly one live, destructively-mutated node, so
        // every cache entry is an owned VALUE snapshot: a canonical vector
        // of constraint-store ids (see facet_i::append_constraints) built
        // fresh at insertion
        // time and never aliasing the live facets - here called an "unsat
        // core", though (per the eligibility gate above) it is really only
        // an over-approximation of one: the full active, non-vacuous,
        // signature-contributing content of the node that just closed, not
        // a minimized core. Cheap to build (no extra proof-of-unsat-core
        // extraction pass); the watch-list lookup below is what keeps
        // checking it affordable even though it isn't minimized.
        //
        // Lookup no longer recomputes a full signature and does an exact
        // hash-bucket vector comparison against every previously-cached
        // entry (that only detects a node revisiting the EXACT SAME active
        // set as some past unsat node). Instead each core is a *subset*
        // check: it fires as soon as ALL of its literals are simultaneously
        // active in the current node - a strictly more general and more
        // useful hit (a superset of a known-unsat set of facts is itself
        // unsat), regardless of what else is also active.
        //
        // This is done with one-watched-literal bookkeeping, mirroring
        // SAT's two-watched-literal scheme but adapted to detect a set
        // becoming fully TRUE (an "all-active" trigger) rather than a
        // clause becoming fully FALSE:
        //   - Each core watches exactly one of its own literals, chosen (at
        //     any point it's checked) to currently be ABSENT from the live
        //     node's active set whenever possible. That invariant makes the
        //     core provably not-yet-fired: at least one of its literals is
        //     missing, so it cannot be fully contained.
        //   - The watched literal is only ever inspected when it is found
        //     among the node's *currently active* ids (see cache_lookup):
        //     that is the only event that can possibly have broken the
        //     invariant. All other literals joining or leaving the active
        //     set never need to touch this core's bookkeeping at all.
        //   - On such a hit, try_rewatch() scans the core's other literals
        //     for one that is still absent and moves the watch there
        //     (m_watch_list[old] -> m_watch_list[new]). If none exists, every
        //     literal of the core is active right now: the core is fully
        //     contained in the current node, which is therefore unsat.
        //   - Backtracking (pop()) only ever shrinks the active set, so a
        //     literal that was absent when chosen as a watch stays absent
        //     across any later pop() - the invariant needs no trail-scoped
        //     undo bookkeeping of its own; it is maintained purely by
        //     construction.
        //
        // The watch list itself is keyed not by a raw signature hash but
        // by a small dense "constraint id" that a global constraint_store
        // (below) assigns to each distinct constraint (per its `hash()`/
        // `equals()`) the first time it is seen - so m_watch_list can be a
        // plain `vector<vector<unsigned>>` indexed directly by id, instead
        // of a hash map keyed by some approximate signature value.
        bool                                    m_unsat_cache_enabled = true;

        // Maps a fact (any `constraint_i`, e.g. an `eq_facet::equation`,
        // `deq_facet::disequation`, or `mem_facet::str_mem` - see that
        // class's comment) to a small, dense, monotonically-assigned
        // unsigned id, so `m_watch_list` (and `unsat_core_entry::lits`)
        // can be plain vectors indexed by id. Unlike the earlier
        // uint64_t-hash-keyed scheme, lookups here are never fooled by a
        // hash collision: `hash()` only selects the bucket, `equals()`
        // (an exact, type-checked comparison - see `constraint_i`) is
        // always used to confirm a match.
        //
        // The store owns a permanent, independent `clone()` of every
        // constraint it interns (never a borrowed pointer into some
        // facet's live, about-to-be-backtracked container) - see
        // `intern()`.
        //
        // `solve()` reseeds this fresh on every call (see its cache-reset
        // block) with exactly the constraints present in the root node at
        // that point (`init()`), so the root's own constraints always get
        // the same small, stable ids for that call; any later fact never
        // seen in the root (e.g. one a split further down the tree
        // produces) is assigned the next free id the first time
        // `cache_insert()` needs one for it (`intern()`), growing the
        // store - and `m_watch_list` alongside it - incrementally as the
        // search proceeds. `cache_lookup()` only ever queries (`find()`),
        // never interns: a fact the store has never seen cannot possibly
        // be contained in any already-inserted core (every core's own
        // literals are themselves ids assigned by this store), so lookup
        // has no reason to grow the store itself.
        class constraint_store {
            // Hash/equality functors dispatch through the (borrowed or
            // owned - both are fine, only `hash()`/`equals()` are ever
            // called) pointer to the pointee's own virtual methods, so
            // `m_ids` transparently supports lookups keyed by a transient,
            // facet-owned pointer against buckets keyed by this store's
            // own permanent clones.
            struct ptr_hash {
                size_t operator()(constraint_i* c) const { return static_cast<size_t>(c->hash()); }
            };
            struct ptr_eq {
                bool operator()(constraint_i* a, constraint_i* b) const { return a == b || a->equals(*b); }
            };
            std::unordered_map<constraint_i*, unsigned, ptr_hash, ptr_eq> m_ids;
            scoped_ptr_vector<constraint_i>                               m_owned; // id -> owned canonical clone
        public:
            void clear() { m_ids.clear(); m_owned.reset(); }
            void init(vector<constraint_i const*> const& cs) {
                for (constraint_i const* c : cs)
                    intern(*c);
            }
            unsigned intern(constraint_i const& c) {
                constraint_i* key = const_cast<constraint_i*>(&c);
                auto it = m_ids.find(key);
                if (it != m_ids.end())
                    return it->second;
                constraint_i* owned = c.clone();
                unsigned id = m_owned.size();
                m_owned.push_back(owned);
                m_ids.emplace(owned, id);
                return id;
            }
            bool find(constraint_i const& c, unsigned& id) const {
                constraint_i* key = const_cast<constraint_i*>(&c);
                auto it = m_ids.find(key);
                if (it == m_ids.end())
                    return false;
                id = it->second;
                return true;
            }
            unsigned size() const { return m_owned.size(); }
        };
        constraint_store                       m_constraint_store;

        struct unsat_core_entry {
            vector<unsigned> lits;   // over-approximate unsat core, as constraint-store ids
            unsigned         watch;  // index into lits currently registered in m_watch_list
        };
        vector<unsat_core_entry>                          m_unsat_cores;
        // constraint-store id -> indices (into m_unsat_cores) of cores
        // currently watching it. Grown (via watch()) on demand as new ids
        // are interned; an id past the current size simply has no cores
        // watching it yet.
        vector<vector<unsigned>>                          m_watch_list;
        // Insertion-time dedup only (never consulted during lookup): hash of
        // a core's ids -> indices (into m_unsat_cores) of previously
        // inserted cores with that hash, so re-deriving the same closure
        // along a different path doesn't grow the cache without bound.
        std::unordered_map<uint64_t, vector<unsigned>>     m_unsat_core_index;

        // True iff every facet NOT contributing to the signature currently
        // holds no live content (is_satisfied()). This is the soundness
        // gate: if some excluded facet (e.g. the arithmetic backend) has
        // live, non-vacuous state, this node's UNSAT-ness (if any) might
        // depend on that excluded state, so it must not be cached or used
        // to prune via the cache - the node simply opts out, forfeiting
        // its own caching benefit without risking an unsound hit elsewhere.
        bool cache_eligible(node const& n) const {
            for (facet_id id = 0; id < n.num_facets(); ++id) {
                if (!n.has_facet(id))
                    continue;
                facet_i const& f = n.facet(id);
                if (!f.contributes_to_signature() && !f.is_satisfied())
                    return false;
            }
            return true;
        }

        // Canonical constraint list: concatenate every contributing
        // facet's own append_constraints() output (borrowed pointers into
        // the facet's own live, active elements), in ascending facet_id
        // order. facet_id order is fixed at root construction (unlike c3,
        // which must explicitly sort a flat untyped constraint list), so
        // cross-facet ordering is already canonical; unlike the earlier
        // uint64_t-hash scheme, a facet no longer needs to internally sort
        // its own contribution - any residual order-sensitivity (only
        // `cache_insert()`'s insertion-time dedup cares) is handled once,
        // centrally, by sorting the resulting dense constraint-store ids
        // (see `cache_insert()`).
        static vector<constraint_i const*> compute_constraints(node const& n) {
            vector<constraint_i const*> cs;
            for (facet_id id = 0; id < n.num_facets(); ++id)
                if (n.has_facet(id) && n.facet(id).contributes_to_signature())
                    n.facet(id).append_constraints(cs);
            return cs;
        }

        static uint64_t hash_ids(vector<unsigned> const& ids) {
            // FNV-1a over the (already dense, small) constraint-store ids;
            // used only to bucket `m_unsat_core_index` for insertion-time
            // dedup - collisions are handled by the exact-equality check
            // (`ids_eq`) that follows every bucket lookup, never trusted
            // alone. `ids` must already be sorted by the caller so that
            // the same set of constraints hashes identically regardless
            // of the order they were originally interned in.
            uint64_t h = 1469598103934665603ull;
            for (unsigned v : ids) {
                h ^= v;
                h *= 1099511628211ull;
            }
            return h;
        }

        static bool ids_eq(vector<unsigned> const& a, vector<unsigned> const& b) {
            if (a.size() != b.size())
                return false;
            for (unsigned i = 0; i < a.size(); ++i)
                if (a[i] != b[i])
                    return false;
            return true;
        }

        // Register `core_idx` as watching constraint-store id `id`,
        // growing `m_watch_list` on demand (ids are assigned densely from
        // 0 by `constraint_store`, so a plain resize-then-index keeps this
        // O(1) amortized, same as `vector::push_back`).
        void watch(unsigned id, unsigned core_idx) {
            if (id >= m_watch_list.size())
                m_watch_list.resize(id + 1);
            m_watch_list[id].push_back(core_idx);
        }

        // Remove one occurrence of `core_idx` from the watch bucket for
        // `id` (the core's watch is always moved away from `id` right
        // before this is called, so the bucket is left consistent).
        void unwatch(unsigned id, unsigned core_idx) {
            if (id >= m_watch_list.size())
                return;
            auto& bucket = m_watch_list[id];
            auto pos = std::find(bucket.begin(), bucket.end(), core_idx);
            if (pos != bucket.end())
                bucket.erase(pos);
        }

        // Precondition: m_unsat_cores[core_idx]'s watch literal is
        // currently `active` (that's the only reason cache_lookup() is
        // inspecting it at all). Looks for another of the core's literals
        // that is NOT active and moves the watch there.
        // Returns true  - watch moved, core has not fired (still some
        //                 absent literal, just a different one now).
        // Returns false - no absent literal exists anywhere in the core:
        //                 every one of its literals is active right now,
        //                 so the core is fully contained in the current
        //                 node, which is therefore unsat.
        bool try_rewatch(unsigned core_idx, std::unordered_set<unsigned> const& active) {
            unsat_core_entry& e = m_unsat_cores[core_idx];
            unsigned old_id = e.lits[e.watch];
            for (unsigned i = 0; i < e.lits.size(); ++i) {
                if (i == e.watch)
                    continue;
                if (!active.count(e.lits[i])) {
                    unwatch(old_id, core_idx);
                    e.watch = i;
                    watch(e.lits[i], core_idx);
                    return true;
                }
            }
            return false;
        }

        // Lookup: true iff this node's current (post-propagation) active
        // constraint set fully contains (as a superset) some previously-
        // cached unsat core - not merely an exact match against a past
        // node's full constraint set (see the watch-list comment above
        // `m_unsat_cache_enabled`). Ineligible/trivial (empty) nodes never
        // hit.
        bool cache_lookup(node const& n) {
            if (!m_unsat_cache_enabled || !cache_eligible(n))
                return false;
            vector<constraint_i const*> cs = compute_constraints(n);
            if (cs.empty())
                return false;
            // Only constraints the store already knows about (i.e. that
            // some previously-inserted core actually mentions) can
            // possibly be contained in any cached core - every core's own
            // literals are themselves store-assigned ids - so this is a
            // pure query (find(), never intern()): a brand-new fact this
            // node happens to hold never grows the store on its own.
            std::unordered_set<unsigned> active;
            active.reserve(cs.size());
            // Note: unlike std::vector, stx's `vector<T>::reserve(n)`
            // actually resizes (and default-fills) up to `n` - it is NOT
            // a capacity-only hint - so it must never be combined with
            // push_back() the way std::vector::reserve() commonly is;
            // just push_back() without pre-reserving here.
            vector<unsigned> active_ids;
            for (constraint_i const* c : cs) {
                unsigned id;
                if (m_constraint_store.find(*c, id)) {
                    active.insert(id);
                    active_ids.push_back(id);
                }
            }
            for (unsigned id : active_ids) {
                if (id >= m_watch_list.size())
                    continue;
                // Snapshot: try_rewatch()/unwatch() mutate m_watch_list
                // (including this very bucket), so the bucket itself must
                // not be relied on past this point - copy it first.
                vector<unsigned> watchers = m_watch_list[id];
                for (unsigned core_idx : watchers) {
                    if (!try_rewatch(core_idx, active)) {
                        ++m_stats.m_num_cache_hits;
                        return true;
                    }
                }
            }
            return false;
        }

        // Insert: memoize this node's current state as an (over-
        // approximate) unsat core, and register it in the watch list.
        // Only called at closure points the caller has already determined
        // are a pure function of the signature-contributing facets (see
        // dfs()); cache_eligible() is re-checked here regardless, as a
        // second, cheap safety net.
        //
        // The initial watch is picked arbitrarily (lits[0]): the "watch is
        // absent" invariant need not hold yet - this very node's active set
        // is exactly (a superset of) the core being inserted, so every
        // literal is present right now. It self-repairs the first time
        // cache_lookup() visits some other node containing lits[0]: if
        // every other literal is also active there, the core fires
        // immediately (correctly - that node is unsat too); otherwise
        // try_rewatch() moves the watch to a literal that is genuinely
        // absent there, restoring the invariant for future checks.
        void cache_insert(node const& n) {
            if (!m_unsat_cache_enabled || !cache_eligible(n))
                return;
            vector<constraint_i const*> cs = compute_constraints(n);
            if (cs.empty())
                return;
            // Every constraint in this node's active set becomes (or
            // already is) a constraint-store id: this is the only place
            // the store ever grows past its root-seeded initial contents
            // (see solve()'s cache-reset block). Note: unlike std::vector,
            // stx's own `vector<T>::reserve(n)` actually resizes (default-
            // filling) rather than just reserving capacity, so it must
            // not be combined with push_back() below - just push_back()
            // directly.
            vector<unsigned> ids;
            for (constraint_i const* c : cs)
                ids.push_back(m_constraint_store.intern(*c));
            // Sort once, centrally, so the dedup check below (and the
            // dedup bucket hash) are independent of the order this node's
            // facets/split path happened to produce their contributions
            // in - two nodes reaching the same active-constraint set via
            // different split orders must dedup against each other.
            std::sort(ids.begin(), ids.end());
            uint64_t h = hash_ids(ids);
            auto& dup_bucket = m_unsat_core_index[h];
            for (unsigned idx : dup_bucket)
                if (ids_eq(m_unsat_cores[idx].lits, ids))
                    return; // already memoized
            unsigned idx = m_unsat_cores.size();
            unsigned first_id = ids[0];
            m_unsat_cores.push_back({ std::move(ids), 0 });
            dup_bucket.push_back(idx);
            watch(first_id, idx);
        }

        unsigned unsat_cache_size() const {
            return m_unsat_cores.size();
        }

        // statistics::update() stores the raw char const* without copying
        // it, and statistics::copy() (used e.g. by check_sat_result to
        // snapshot stats for later display) shallow-copies that pointer
        // too - so a dynamically built key's backing storage must survive
        // for the rest of the process, not merely for the duration of this
        // collect_statistics() call. A function-local/member std::string
        // is not enough: by the time cmd_context::display_statistics()
        // actually prints the snapshot, this search_tree (and any member
        // buffer) may already be destroyed, leaving a dangling pointer
        // (a heap-use-after-free caught by ASan). Intern each built name
        // in a static, process-lifetime pool instead; insertion never
        // invalidates previously returned pointers.
        static char const* intern_stat_name(std::string&& s) {
            static std::unordered_set<std::string> pool;
            return pool.insert(std::move(s)).first->c_str();
        }

        // Hot-restart snapshot of the (unique, innermost) SAT leaf found by
        // the most recent `solve()` call, taken via the cold-path `clone()`
        // before the DFS unwind pops the trail scopes that produced it - so
        // callers can still inspect the satisfying facet state (e.g. read
        // off a model) after `solve()` has returned and the live node has
        // been restored to its pre-solve state.
        scoped_ptr<node>                       m_sat_snapshot;

        // --- Optional DOT-trace instrumentation (diagnostics only) ---
        //
        // Unlike the c3 branch's `nielsen_graph`, this engine keeps only
        // one live `node`, so there is no persistent tree object to dump.
        // When enabled (`enable_dot_trace(true)`), `dfs()` instead records
        // one `dot_node` per recursive call into `m_dot_nodes`, capturing
        // this call's parent (via `m_dot_stack`, the current root-to-here
        // path), the incoming edge's label, a text snapshot of every
        // installed facet's `display()` taken right after this call's own
        // `propagate_to_fixpoint()` (i.e. before any child branch further
        // mutates the live node), and (once known) this call's own
        // `search_result`/`node_status`/`backtrack_reason`. `to_dot()`
        // renders `m_dot_nodes` as a graphviz digraph, colouring nodes/
        // edges by result, mirroring `nielsen_graph::to_dot` in z3-tacas.
        //
        // `solve()`'s iterative deepening re-runs `dfs(0)` from scratch at
        // increasing depth bounds; recording every round would make the
        // trace an ever-growing, mostly-redundant prefix of itself, so the
        // trace is cleared at the start of each round - `to_dot()` after
        // `solve()` returns therefore always reflects only the *last*
        // (deepest, or externally cancelled) round, which is what a caller
        // actually wants to inspect.
        struct dot_node {
            unsigned      id = 0;
            int           parent_id = -1;
            std::string   edge_label;
            std::string   state_label;
            search_result result = search_result::unknown;
            node_status   status = node_status::unevaluated;
            backtrack_reason reason = br_unevaluated;
        };
        bool                 m_dot_trace_enabled = false;
        unsigned             m_max_dot_nodes = 200000; // cap to bound memory/file size
        vector<dot_node>     m_dot_nodes;
        vector<unsigned>     m_dot_stack; // current root-to-here path, by dot_node id
        // Optional "live" dump: if set, dfs() periodically overwrites this
        // file with the current to_dot() rendering as the search
        // progresses, instead of only after solve() returns. This is what
        // makes the trace usable when the process is torn down abruptly
        // (e.g. -T:'s timeout handler calls _Exit() directly, which never
        // unwinds the stack back to a post-solve() dump point).
        std::string          m_dot_live_path;
        std::chrono::steady_clock::time_point m_dot_live_last_write{};

        static std::string dot_escape(std::string const& s) {
            std::string out;
            out.reserve(s.size());
            for (char c : s) {
                switch (c) {
                case '"':  out += "\\\""; break;
                case '\\': out += "\\\\"; break;
                case '\n': out += "\\n"; break;
                default:   out += c; break;
                }
            }
            return out;
        }

        // Run every registered propagation plugin to a fixed point. The
        // fixed point is detected via each plugin's own report: a round
        // is a single pass over every plugin in registration order; we
        // stop once a full round has every plugin report `noop` (no
        // plugin changed anything), or a plugin reports
        // conflict/satisfied.
        simplify_result propagate_to_fixpoint(node& n) {
            // Bound the number of rounds by the number of plugins plus
            // facets: propagation must be confluent/terminating, so this
            // is a safety net against a misbehaving plugin, not a normal
            // termination condition.
            unsigned max_rounds = (m_prop_plugins.size() + n.num_facets() + 1) * 4 + 8;
            for (unsigned round = 0; round < max_rounds; ++round) {
                if (!m_limit.inc())
                    return simplify_result::proceed;
                bool any_change = false;
                for (auto* p : m_prop_plugins) {
                    m_stats.m_propagate_counts[p->name()]++;
                    simplify_result r = p->propagate(n);
                    if (r == simplify_result::conflict)
                        return r;
                    if (r != simplify_result::noop)
                        any_change = true;
                    // NOTE: a plugin reporting `satisfied` only means ITS
                    // OWN facet is discharged, not that every other facet
                    // in this node is - the node is only truly satisfied
                    // once ALL facets agree (n.is_satisfied(), an AND over
                    // every registered facet). Keep running the remaining
                    // plugins in this round (and further rounds, since
                    // other facets may still need to react/propagate)
                    // rather than short-circuiting here.
                }
                if (!any_change)
                    break;
            }
            return n.is_satisfied() ? simplify_result::satisfied : simplify_result::proceed;
        }

        // Pop one trail scope and fan out node::pop_facets() together -
        // the one-shot counterpart to scoped_push, for call sites that
        // pop a scope committed elsewhere (e.g. the dfs() recursion site,
        // which matches a scope a split already committed rather than
        // owning a fresh one itself). Always operates on the single live
        // node (m_root).
        void pop() {
            m_trail.pop_scope(1);
            m_root->pop_facets();
        }

        // Search for the cheapest available split, raising `cost` from 0.
        // Pushes exactly one trail scope immediately before each `split()`
        // call, popping it again if that call declines to commit a
        // branch. On success, `n`/the trail have already been mutated for
        // the first branch (inside that one pushed scope, left in place),
        // `out` holds that branch's edge, and `frame.m_iter` (possibly
        // null) holds the resumable iterator for the rest. Returns false
        // once every plugin has nothing left to offer at any cost (the
        // node is closed).
        bool extend_node(node& n, dfs_frame& frame, edge& out) {
            for (unsigned cost = 0; cost <= m_max_cost; ++cost) {
                bool any_offer = false;
                for (auto* sp : m_split_plugins) {
                    if (cost < sp->min_cost()) {
                        any_offer = true; // this plugin may still offer at a higher cost
                        continue;
                    }
                    m_stats.m_split_counts[sp->name()]++;
                    bool has_more = false;
                    bool committed = false;
                    scoped_push guard(*this);
                    auto it = sp->split(n, cost, out, has_more, committed);
                    if (committed) {
                        guard.release();
                        frame.m_iter = std::move(it);
                        return true;
                    }
                    if (has_more)
                        any_offer = true;
                }
                if (!any_offer)
                    return false;
            }
            return false;
        }

        // Pushes exactly one trail scope immediately before calling
        // `iter->next()`, popping it again if `next()` returns false (no
        // more branches). On success the pushed scope holds that branch's
        // mutations and is left in place for the caller.
        bool advance_iter(split_iterator_i& iter, edge& out) {
            scoped_push guard(*this);
            if (iter.next(out)) {
                guard.release();
                return true;
            }
            return false;
        }

        // `pure_out`, when non-null, is set (only meaningful when the
        // return value is `unsat`) to whether this call's UNSAT verdict
        // is a pure function of the signature-contributing facets
        // throughout the ENTIRE subtree explored here - not just this
        // frame's own current facet snapshot. A child branch may have
        // transiently relied on excluded-facet content (e.g. an
        // arithmetic split) that has already been popped/undone by the
        // time this frame resumes, so purity has to be threaded up from
        // where each conflict actually originated, mirroring c3's
        // per-subtree `all_string_only` tracking (`m_unsat_cacheable`) -
        // a point-in-time check at the aggregating parent alone cannot
        // see what its children depended on along the way.
        search_result dfs(unsigned depth, edge const* in_edge = nullptr, bool* pure_out = nullptr) {
            node& n = *m_root;
            m_stats.m_num_dfs_nodes++;
            if (m_max_nodes && m_stats.m_num_dfs_nodes > m_max_nodes)
                return search_result::unknown;
            if (!m_limit.inc())
                return search_result::unknown;
            // Stack-safety backstop: see m_raw_dfs_depth's comment. Treated
            // exactly like an ordinary depth_cutoff (both pure_out purity
            // tracking and the iterative-deepening retry above already
            // handle that result).
            if (m_raw_dfs_depth >= m_max_raw_dfs_depth)
                return search_result::depth_cutoff;
            flet<unsigned> _scoped_raw_depth(m_raw_dfs_depth, m_raw_dfs_depth + 1);

            dfs_frame frame;

            // --- dot trace: open this node's record, linked to the
            // current path via m_dot_stack, before any children recurse.
            int dot_id = -1;
            if (m_dot_trace_enabled && m_dot_nodes.size() < m_max_dot_nodes) {
                dot_id = static_cast<int>(m_dot_nodes.size());
                m_dot_nodes.push_back(dot_node());
                dot_node& rec = m_dot_nodes.back();
                rec.id = static_cast<unsigned>(dot_id);
                rec.parent_id = m_dot_stack.empty() ? -1 : static_cast<int>(m_dot_stack.back());
                if (in_edge) {
                    std::ostringstream es;
                    es << in_edge->rule_name();
                    if (in_edge->cost())
                        es << " (cost " << in_edge->cost() << ")";
                    rec.edge_label = es.str();
                }
                m_dot_stack.push_back(static_cast<unsigned>(dot_id));
                if (!m_dot_live_path.empty()) {
                    auto now = std::chrono::steady_clock::now();
                    if (m_dot_live_last_write.time_since_epoch().count() == 0 ||
                        now - m_dot_live_last_write >= std::chrono::milliseconds(200)) {
                        m_dot_live_last_write = now;
                        std::ofstream live_out(m_dot_live_path);
                        if (live_out)
                            to_dot(live_out);
                    }
                }
            }
            on_scope_exit dot_pop([&]() {
                if (dot_id >= 0)
                    m_dot_stack.pop_back();
            });

            search_result result;
            n.clear_status();
            simplify_result sr = propagate_to_fixpoint(n);

            // --- unsat cache lookup: only when propagation didn't already
            // resolve this node one way or the other, so a hit here always
            // replaces genuine further search (branching), never a
            // decision propagation already made for free.
            if (sr != simplify_result::conflict && sr != simplify_result::satisfied &&
                cache_lookup(n)) {
                n.set_conflict(br_children_failed, nullptr);
                sr = simplify_result::conflict;
            }

            // --- dot trace: snapshot this node's own facet state now -
            // before any child branch further mutates the (single, live)
            // node in place.
            if (dot_id >= 0) {
                std::ostringstream ss;
                for (facet_id id = 0; id < n.num_facets(); ++id)
                    if (n.has_facet(id))
                        n.facet(id).display(ss) << "\n";
                m_dot_nodes[dot_id].state_label = ss.str();
            }

            if (sr == simplify_result::conflict) {
                result = search_result::unsat;
                // Propagation-level conflict: sound to memoize whenever no
                // excluded facet holds live content (cache_insert re-checks
                // cache_eligible itself), mirroring c3's leaf-regex-
                // infeasible insert site.
                bool pure = cache_eligible(n);
                if (pure)
                    cache_insert(n);
                if (pure_out) *pure_out = pure;
            }
            else if (sr == simplify_result::satisfied) {
                result = search_result::sat;
                m_sat_snapshot = n.clone(m_trail);
            }
            else if (depth >= m_depth_bound) {
                result = search_result::depth_cutoff;
            }
            else {
                edge first_edge;
                bool has_children = extend_node(n, frame, first_edge);

                if (!has_children) {
                    // No propagation conflict/satisfaction and no split rule
                    // has anything left to offer: the node is stuck (a
                    // genuine "unknown", not a depth cutoff - retrying with
                    // a larger depth bound will not help). A split plugin may
                    // still have called n.set_conflict() itself (e.g.
                    // mem_monadic_split reporting a refuted membership
                    // conjunction) while declining to offer a branch -
                    // that conflict must be honored here, or a real unsat
                    // is misreported as unknown.
                    if (n.is_conflict()) {
                        result = search_result::unsat;
                        // A split plugin declared conflict directly (e.g. a
                        // refuted membership conjunction) with no further
                        // branching left to try: same leaf-level memoization
                        // opportunity as the propagation-conflict site above.
                        bool pure = cache_eligible(n);
                        if (pure)
                            cache_insert(n);
                        if (pure_out) *pure_out = pure;
                    }
                    else if (n.is_satisfied()) {
                        result = search_result::sat;
                        m_sat_snapshot = n.clone(m_trail);
                    }
                    else
                        result = search_result::unknown;
                }
                else {
                    bool saw_unknown = false;
                    bool saw_depth_cutoff = false;
                    bool all_children_pure = true; // AND-reduced across every UNSAT child
                    result = search_result::unsat;
                    edge cur_edge = first_edge;
                    bool have_branch = true;
                    while (have_branch) {
                        search_result cr;
                        bool child_pure = false;
                        // progress edges (a variable eliminated, an arithmetic decision) are
                        // free; only edges introducing fresh variables count towards the bound
                        cr = dfs(depth + (cur_edge.is_progress() ? 0 : 1), &cur_edge, &child_pure);
                        // Always pop back out of this branch, even on
                        // sat: the sat leaf's facet state was already
                        // captured by m_sat_snapshot (a cold-path
                        // clone taken where the leaf was found), so
                        // there is no need to leave any trail scopes
                        // suspended just to keep the live node in the
                        // satisfying state - callers that want to
                        // inspect it use sat_snapshot() instead.
                        pop(); // matches the scope the split committed for this branch
                        if (cr == search_result::sat) {
                            result = search_result::sat;
                            break;
                        }
                        if (cr == search_result::unsat && !child_pure)
                            all_children_pure = false;
                        if (cr == search_result::depth_cutoff)
                            saw_depth_cutoff = true;
                        else if (cr == search_result::unknown)
                            saw_unknown = true;
                        have_branch = frame.m_iter && advance_iter(*frame.m_iter, cur_edge);
                    }
                    if (result != search_result::sat) {
                        result = saw_depth_cutoff ? search_result::depth_cutoff
                               : saw_unknown       ? search_result::unknown
                               :                     search_result::unsat;
                        // Every branch failed with unsat (no unknown/
                        // depth-cutoff anywhere): the node itself is
                        // unsatisfiable. Each contributing branch already
                        // recorded its own dependency in m_conflict_deps
                        // when it hit conflict; join them here into one
                        // dependency so the caller (theory_nseq::
                        // final_check_eh) has something to report - an
                        // aggregate conflict with no dependency at all
                        // would otherwise fall back to a giveup and the
                        // real unsat would be misreported as unknown.
                        if (result == search_result::unsat) {
                            dep_tracker joined = nullptr;
                            for (dep_tracker d : n.conflict_deps())
                                joined = m_dep_mgr.mk_join(joined, d);
                            n.set_conflict(br_children_failed, joined);
                            // Only cache this aggregate closure if EVERY
                            // child's own unsat was itself pure (see the
                            // pure_out doc comment above dfs()) AND this
                            // node's own current (parent-level) facet
                            // state has nothing excluded live either -
                            // both conditions are required, since a
                            // spurious cache entry here would prune an
                            // unrelated node that legitimately still has
                            // arithmetic-dependent branches to try.
                            bool pure = all_children_pure && cache_eligible(n);
                            if (pure)
                                cache_insert(n);
                            if (pure_out) *pure_out = pure;
                        }
                    }
                }
            }
            if (dot_id >= 0) {
                dot_node& rec = m_dot_nodes[dot_id];
                rec.result = result;
                rec.status = n.status();
                rec.reason = n.reason();
            }
            return result;
        }

    public:
        search_tree(trail_stack& trail, reslimit& lim) : m_trail(trail), m_limit(lim) {}
        ~search_tree() = default;


        dep_manager_t& dep_mgr() { return m_dep_mgr; }
        trail_stack& trail() { return m_trail; }

        // Set the (opaque, not-owned) ambient-context handle on the root
        // node, so every facet registered against it can reach it via
        // `node::ambient()`. Typically called once, right after
        // `mk_root()`, before any facets are registered.
        void set_ambient_context(ambient_context_base* ac) { m_root->set_ambient(ac); }

        // Reserve a new facet slot; returns its stable id.
        facet_id register_facet() { return m_next_facet_id++; }

        // Reserve a new facet slot and construct+install `T` (forwarding
        // the shared trail_stack plus any extra constructor args) into `n`
        // (typically the root node, returned by a prior `mk_root()` call).
        template <typename T, typename... Args>
        facet_id register_facet(node& n, Args&&... args) {
            facet_id id = m_next_facet_id++;
            n.m_facets.resize(m_next_facet_id, nullptr);
            n.install_facet(id, alloc(T, m_trail, std::forward<Args>(args)...));
            return id;
        }

        // Same as above, but additionally invokes `bind(id)` right after
        // the new facet id is minted. `bind` is typically a small lambda
        // supplied by the domain layer that stashes `id` on the node's
        // ambient context (e.g. `[&](facet_id id){ ac->set_eq_id(id); }`),
        // so that registration and ambient-context id-binding happen as
        // one atomic step at the call site instead of two - without this
        // engine header needing to know anything about what an "ambient
        // context" or a "facet id setter" actually is (`Binder` is fully
        // generic; this stays domain-agnostic). Named differently from
        // the overload above (rather than overloaded on it) to avoid an
        // ambiguous-overload resolution between two same-name variadic
        // templates whenever `Args...` could itself begin with a
        // callable.
        template <typename T, typename Binder, typename... Args>
        facet_id register_facet_bound(node& n, Binder&& bind, Args&&... args) {
            facet_id id = register_facet<T>(n, std::forward<Args>(args)...);
            bind(id);
            return id;
        }

        void add_propagation_plugin(propagation_plugin_i* p) { m_prop_plugins.push_back(p); }
        void add_split_plugin(split_plugin_i* p) { m_split_plugins.push_back(p); }

        void set_max_search_depth(unsigned d) { m_max_search_depth = d; }
        void set_max_cost(unsigned c) { m_max_cost = c; }
        void set_max_nodes(unsigned n) { m_max_nodes = n; }
        // Sets the floor solve() starts its doubling loop from (default 1).
        // Intended to be called before each solve(), e.g. with the number of
        // top-level constraints just flushed into the tree, so solve() skips
        // depth_bound rounds that provably cannot yet touch every constraint
        // once. Clamped so it never exceeds m_max_search_depth.
        void set_min_search_depth(unsigned d) { m_min_search_depth = std::max(1u, std::min(d, m_max_search_depth)); }

        // Ablation switch for the unsat cache (default off until validated
        // by ablation on real benchmarks - see the c3 branch's analogous
        // nseq.unsat_cache toggle for the measurement methodology this
        // mirrors).
        void set_unsat_cache_enabled(bool b) { m_unsat_cache_enabled = b; }
        bool unsat_cache_enabled() const { return m_unsat_cache_enabled; }

        // Create the single root node (all facet slots initially null;
        // fill them in via the templated `register_facet<T>(node&, ...)`
        // overload above, or `node::install_facet` directly).
        node* mk_root() { SASSERT(!m_root); m_root = alloc(node, m_next_facet_id); return m_root.get(); }
        node* root() const { return m_root.get(); }

        // Called by the ambient owner (theory_nseq) in lockstep with its
        // own push_scope_eh()/pop_scope_eh(), i.e. at the SMT core's own
        // scope boundaries - distinct from DFS's internal scoped_push/
        // pop(), which additionally opens/closes a *trail* scope on the
        // shared trail_stack (already owned by the SMT core itself, see
        // m_tree's constructor). Only the facet-level push()/pop() hooks
        // need to be relayed here (any trail-scope bookkeeping the SMT
        // core does is already visible to every trail object pushed by a
        // facet, since m_trail *is* ctx.get_trail_stack()).
        void push_facets() { m_root->push_facets(); }
        void pop_facets() { m_root->pop_facets(); }

        // Deep-copy `src`'s current root facet state into this tree's own
        // root, re-binding each cloned facet to this tree's own trail_stack
        // (so subsequent mutations undo through *this* tree's trail, not
        // `src`'s). Used by e.g. `theory_nseq::mk_fresh` to make a cloned
        // context start out with the same accumulated facet state as the
        // context it was cloned from, rather than silently starting empty.
        // Both trees must have gone through the identical sequence of
        // `register_facet<T>(...)` calls (same facet ids/types/order) -
        // true whenever `src` and `*this` come from two `theory_nseq`
        // instances constructed the same way.
        void clone_state_from(search_tree const& src) {
            SASSERT(m_root && src.m_root);
            SASSERT(m_root->num_facets() == src.m_root->num_facets());
            node* new_root = src.m_root->clone(m_trail);
            for (facet_id id = 0; id < m_root->num_facets(); ++id) {
                if (!src.m_root->has_facet(id))
                    continue;
                dealloc(m_root->m_facets[id]);
                m_root->m_facets[id] = new_root->m_facets[id];
                new_root->m_facets[id] = nullptr;
            }
            m_root->m_status = new_root->m_status;
            m_root->m_reason = new_root->m_reason;
            m_root->m_conflict_dep = new_root->m_conflict_dep;
            dealloc(new_root);
        }

        // Non-null only immediately after a `solve()` call returned `sat`;
        // a standalone (trail-independent) snapshot of the satisfying
        // facet state. Overwritten/cleared by the next `solve()` call.
        node const* sat_snapshot() const { return m_sat_snapshot.get(); }

        stats const& get_stats() const { return m_stats; }
        void reset_stats() { m_stats.reset(); }

        // Engine-level stats plus a fan-out to every registered
        // propagation/split plugin's own collect_statistics(), so a
        // caller need only call this once to get both the generic
        // engine counters (solve/dfs/split counts, per-plugin
        // invocation counts) and every plugin's domain-specific
        // counters (e.g. "eq: word_eq_split applications").
        void collect_statistics(::statistics& st) const {
            st.update("seq-stx num solve calls", m_stats.m_num_solve_calls);
            st.update("seq-stx num dfs nodes", m_stats.m_num_dfs_nodes);
            st.update("seq-stx num sat", m_stats.m_num_sat);
            st.update("seq-stx num unsat", m_stats.m_num_unsat);
            st.update("seq-stx num unknown", m_stats.m_num_unknown);
            st.update("seq-stx max depth", m_stats.m_max_depth);
            st.update("seq-stx unsat-cache size", unsat_cache_size());
            st.update("seq-stx unsat-cache hits", m_stats.m_num_cache_hits);
            st.update("seq-stx constraint-store size", m_constraint_store.size());
            for (auto const& [k, v] : m_stats.m_propagate_counts)
                st.update(intern_stat_name(std::string("seq-stx propagate ") + k), v);
            for (auto const& [k, v] : m_stats.m_split_counts)
                st.update(intern_stat_name(std::string("seq-stx split ") + k), v);
            for (auto* p : m_prop_plugins)
                p->collect_statistics(st);
            for (auto* sp : m_split_plugins)
                sp->collect_statistics(st);
        }

        // Reset both the engine's own stats struct and every registered
        // plugin's own internal stats struct.
        void reset_statistics() {
            m_stats.reset();
            for (auto* p : m_prop_plugins)
                p->reset_statistics();
            for (auto* sp : m_split_plugins)
                sp->reset_statistics();
        }

        // Turn dot-trace recording on/off (default off: recording a
        // facet-state snapshot at every DFS node is not free). Disabling
        // also discards whatever was recorded so far.
        void enable_dot_trace(bool b = true) {
            m_dot_trace_enabled = b;
            if (!b) {
                m_dot_nodes.clear();
                m_dot_stack.clear();
            }
        }
        bool dot_trace_enabled() const { return m_dot_trace_enabled; }
        void set_max_dot_nodes(unsigned n) { m_max_dot_nodes = n; }

        // Optional "live" dump path: if set, dfs() periodically
        // overwrites this file with the current to_dot() rendering
        // (throttled to roughly once every 200ms), so a trace survives
        // an abrupt process teardown - e.g. the shell's -T: timeout
        // handler calls _Exit() directly on a background thread once
        // the deadline elapses, which never unwinds back to a normal
        // post-solve() dump point.
        void set_dot_live_file(std::string path) {
            m_dot_live_path = std::move(path);
            m_dot_live_last_write = std::chrono::steady_clock::time_point();
        }

        // Render the most recently recorded DFS round (see the comment on
        // `m_dot_nodes` above) as a graphviz digraph: one node per DFS
        // call, labelled with its id and a snapshot of every facet's
        // `display()` output at that point, coloured green/red/gray for
        // sat/unsat/unknown-or-depth_cutoff; edges labelled with the
        // split rule (and iterative-deepening cost, if non-zero) that
        // produced that child, coloured to match the child's outcome.
        // Available whether `solve()` ran to completion or was cut short
        // by cancellation/a resource limit - whatever was recorded before
        // that happened is still here (dfs() records incrementally, not
        // as a single post-hoc dump).
        std::ostream& to_dot(std::ostream& out) const {
            out << "digraph G {\n";
            out << "  node [shape=box, fontname=\"monospace\", fontsize=10];\n";
            for (auto const& rec : m_dot_nodes) {
                out << "  n" << rec.id << " [label=\"" << rec.id;
                if (!rec.state_label.empty())
                    out << ": " << dot_escape(rec.state_label);
                out << "\"";
                switch (rec.result) {
                case search_result::sat:          out << ", color=green, penwidth=2"; break;
                case search_result::unsat:         out << ", color=red"; break;
                case search_result::depth_cutoff:  out << ", color=orange"; break;
                case search_result::unknown:       out << ", color=gray"; break;
                }
                out << "];\n";
            }
            for (auto const& rec : m_dot_nodes) {
                if (rec.parent_id < 0)
                    continue;
                out << "  n" << rec.parent_id << " -> n" << rec.id << " [label=\"" << dot_escape(rec.edge_label) << "\"";
                if (rec.result == search_result::sat)
                    out << ", color=green, penwidth=2";
                else if (rec.result == search_result::unsat)
                    out << ", color=red";
                out << "];\n";
            }
            out << "}\n";
            return out;
        }
        std::string to_dot() const {
            std::ostringstream ss;
            to_dot(ss);
            return ss.str();
        }

        // Print the live node's installed facets (one per registered
        // facet_id), via each facet's own facet_i::display() override.
        // Diagnostics only; the engine itself never parses this output.
        std::ostream& display(std::ostream& out) const {
            if (!m_root)
                return out;
            for (facet_id id = 0; id < m_root->num_facets(); ++id)
                if (m_root->has_facet(id))
                    m_root->facet(id).display(out) << "\n";
            return out;
        }

        // Iterative-deepening DFS over the single live node (m_root).
        // Trail scopes opened during the search are always fully popped
        // back to their level on entry before `solve()` returns,
        // regardless of verdict, so the node's facet state is restored to
        // what it was on entry. On sat, callers inspect the satisfying
        // state via `sat_snapshot()` (a cold-path clone taken where the
        // leaf was found) rather than the live node.
        search_result solve() {
            SASSERT(m_root);
            m_stats.m_num_solve_calls++;
            // Mirrors c3's nielsen_graph::reset(): the cache is a pure
            // performance memo scoped to one solve() call, cleared here so
            // stale entries from a structurally different accumulated
            // problem never linger (conservative; a persistent cache across
            // solve() calls would also be sound since containment facts
            // never expire, but isn't validated for this engine's
            // clone_state_from/push/pop interactions yet).
            m_unsat_cores.clear();
            m_watch_list.clear();
            m_unsat_core_index.clear();
            // Reseed the constraint store with exactly the constraints
            // present in the root node right now (see constraint_store's
            // class comment): the root's own facts get the same small,
            // stable ids for this whole solve() call, before any
            // cache_insert() call (further down the tree) can intern a
            // fresh id for a fact the root doesn't have.
            m_constraint_store.clear();
            m_constraint_store.init(compute_constraints(*m_root));
            unsigned base_scopes = m_trail.get_num_scopes();
            on_scope_exit rewind([&]() {
                while (m_trail.get_num_scopes() > base_scopes)
                    pop();
            });
            m_sat_snapshot = nullptr;
            m_root->clear_conflict_deps();
            search_result res = search_result::depth_cutoff;
            for (unsigned depth_bound = m_min_search_depth; depth_bound <= m_max_search_depth && res == search_result::depth_cutoff; depth_bound = next_depth_bound(depth_bound)) {
                if (!m_limit.inc()) {
                    res = search_result::unknown;
                    break;
                }
                m_depth_bound = depth_bound;
                m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth_bound);
                // Each iterative-deepening round re-explores from the
                // root; keeping only the latest round's dot-trace (rather
                // than appending across rounds) is what makes to_dot()
                // useful - see the m_dot_nodes comment above.
                if (m_dot_trace_enabled) {
                    m_dot_nodes.clear();
                    m_dot_stack.clear();
                }
                res = dfs(0);
                if (res == search_result::sat) { m_stats.m_num_sat++; }
                if (res == search_result::unsat) { m_stats.m_num_unsat++; }
                // res == search_result::unknown: genuinely stuck (no
                // facets changed and no split available at any depth) -
                // retrying with a larger depth bound will not help, so
                // the loop condition below stops deepening.
                // res == search_result::depth_cutoff: retrying with a
                // larger depth bound may still resolve this subtree, so
                // the loop condition keeps deepening until the
                // search-depth budget is exhausted.
            }
            if (res == search_result::unknown || res == search_result::depth_cutoff) {
                m_stats.m_num_unknown++;
                res = search_result::unknown; // normalize: never leak depth_cutoff to callers
            }
            return res;
        }

    };

} // namespace stx

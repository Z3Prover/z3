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
    restart's post-solve snapshot of a SAT leaf, and cache-entry storage);
    it is never used on the DFS hot path itself.

    The two extension points are:
      - `propagation_plugin_i`: deterministic, non-branching simplification.
        Mutations MUST register with the trail; must NEVER call
        `push_scope()` itself (that is the DFS driver's job, via
        `scoped_pop`).
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

--*/
#pragma once

#include "util/util.h"
#include "util/vector.h"
#include "util/dependency.h"
#include "util/trail.h"
#include <string>
#include <memory>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <climits>

namespace stx {

    // Result of a deterministic propagation pass.
    enum class simplify_result { proceed, conflict, satisfied };

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
    // core reserves 0 for "unevaluated" and a couple of small values for its
    // own generic reasons (sibling cut, children all failed); plugins
    // should use values >= br_plugin_base.
    using backtrack_reason = unsigned;
    const backtrack_reason br_unevaluated     = 0;
    const backtrack_reason br_sibling         = 1;
    const backtrack_reason br_children_failed = 2;
    const backtrack_reason br_plugin_base     = 3; // first value free for plugin use

    /**
     * One constituent of a node's state. Plugins define concrete subclasses
     * (e.g. an `eq_facet`, an `arith_facet`); the engine interacts only
     * through this interface, and never inspects a facet's contents.
     *
     * Every concrete facet is constructed with a reference to the shared
     * `trail_stack`, so that its own destructive mutator methods (defined
     * by the plugin, not by this interface) can register undo objects
     * (`m_trail.push(some_trail_object)`) instead of allocating a fresh
     * clone per mutation. `push_scope()`/`pop_scope()` themselves are never
     * called by a facet or plugin - only the DFS driver (via `scoped_pop`)
     * owns scope boundaries.
     */
    class facet_i {
    protected:
        trail_stack& m_trail;
    public:
        explicit facet_i(trail_stack& trail) : m_trail(trail) {}
        virtual ~facet_i() = default;

        // Cold-path deep-clone, e.g. for a hot-restart snapshot of a SAT
        // leaf's facets (taken outside the live trail before it unwinds) or
        // for a cache entry that must survive later pop_scope() calls. NOT
        // used on the DFS hot path.
        virtual facet_i* clone(trail_stack& trail) const = 0;

        // Order/collision-insensitive hash contribution (canonicalized
        // internally by the facet, e.g. by sorting its own constraint
        // vector). Used to build the node's transposition/subsumption key.
        virtual unsigned hash() const = 0;

        // Are `this` and `other` equivalent for subsumption purposes? (same
        // facet_id assumed; the engine only ever compares facets that come
        // from the same registered slot.) Equality modulo representation,
        // not pointer identity.
        virtual bool similar(facet_i const& other) const = 0;

        // Is this facet's constraint set trivially/vacuously satisfied
        // (e.g. no equations left, or an empty membership set)?
        virtual bool is_satisfied() const = 0;
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
            // first), `satisfied` if `n` is now trivially satisfied, and
            // `proceed` otherwise (whether or not this pass changed `n`).
            virtual simplify_result propagate(node& n) = 0;
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
        public:
            virtual ~split_plugin_i() = default;
            virtual char const* name() const = 0;
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

            explicit node(unsigned num_facets) {
                m_facets.resize(num_facets, nullptr);
            }

        public:
            ~node() {
                for (auto* f : m_facets) dealloc(f);
            }

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

            node_status status() const { return m_status; }
            bool is_conflict() const { return m_status == node_status::conflict; }

            void set_conflict(backtrack_reason r, dep_tracker dep) {
                m_status = node_status::conflict;
                m_reason = r;
                m_conflict_dep = dep;
            }
            void set_satisfied() { m_status = node_status::satisfied; }
            void clear_status() { m_status = node_status::unevaluated; m_reason = br_unevaluated; m_conflict_dep = nullptr; }

            backtrack_reason reason() const { return m_reason; }
            dep_tracker conflict_dep() const { return m_conflict_dep; }

            // Canonicalized structural hash over all installed facets.
            // Always recomputed fresh (there is only ever one live node, so
            // there is nothing to cache against; the trail may have changed
            // any facet's contents since the last call).
            unsigned hash() const {
                unsigned h = m_facets.size() + 1;
                for (auto* f : m_facets)
                    h = combine_hash(h, f ? f->hash() : 0);
                return h ? h : 1; // 0 is reserved for "unset"
            }

            // Slot-wise `facet_i::similar`; used by the transposition and
            // sibling caches.
            bool similar(node const& other) const {
                if (m_facets.size() != other.m_facets.size())
                    return false;
                for (unsigned i = 0; i < m_facets.size(); ++i) {
                    facet_i* a = m_facets[i];
                    facet_i* b = other.m_facets[i];
                    if ((a == nullptr) != (b == nullptr))
                        return false;
                    if (a && !a->similar(*b))
                        return false;
                }
                return true;
            }

            // Cold-path: snapshot every installed facet into a standalone
            // node not tied to any live trail scope (used by hot restart to
            // preserve a SAT leaf's facet state across the trail unwinding
            // back to root, and by the unsat cache to store a comparison
            // key that survives pop_scope()).
            node* clone(trail_stack& trail) const {
                node* n = alloc(node, m_facets.size());
                for (facet_id id = 0; id < m_facets.size(); ++id)
                    if (m_facets[id])
                        n->m_facets[id] = m_facets[id]->clone(trail);
                n->m_status = m_status;
                n->m_reason = m_reason;
                n->m_conflict_dep = m_conflict_dep;
                return n;
            }
        };

        // RAII guard around one DFS branch descent: pushes a trail scope on
        // construction, pops it (unwinding every trail object registered
        // since) on destruction - including through an exception, so a
        // plugin/facet throwing mid-mutation cannot leave the shared node
        // and trail in a mismatched state relative to the DFS call stack.
        class scoped_pop {
            trail_stack& m_trail;
            unsigned     m_scopes;
            bool         m_active = true;
        public:
            explicit scoped_pop(trail_stack& trail, unsigned scopes = 1) : m_trail(trail), m_scopes(scopes) {}
            ~scoped_pop() { if (m_active) m_trail.pop_scope(m_scopes); }
            scoped_pop(scoped_pop const&) = delete;
            scoped_pop& operator=(scoped_pop const&) = delete;
            // Release without popping (ownership of the scope(s) has been
            // transferred elsewhere, e.g. to a surviving split_iterator_i).
            void release() { m_active = false; }
        };

        struct stats {
            unsigned m_num_solve_calls  = 0;
            unsigned m_num_dfs_nodes    = 0;
            unsigned m_num_sat          = 0;
            unsigned m_num_unsat        = 0;
            unsigned m_num_unknown      = 0;
            unsigned m_num_cache_hits   = 0;
            unsigned m_num_sibling_cuts = 0;
            unsigned m_max_depth        = 0;
            std::unordered_map<std::string, unsigned> m_propagate_counts;
            std::unordered_map<std::string, unsigned> m_split_counts;
            void reset() { *this = stats(); }
        };

    private:
        // A lightweight, trail-independent comparison key for a node,
        // captured at the point a frame is entered (for the sibling/
        // transposition caches). Since there is only one live node, we
        // cannot keep a pointer to "the node as it was" - instead we take a
        // cold-path `clone()` snapshot, exactly analogous to hot restart's
        // SAT-leaf snapshot. This is only paid for nodes actually inserted
        // into a cache bucket (not for every DFS frame).
        struct digest {
            unsigned                    m_hash;
            scoped_ptr<node>            m_snapshot; // owned, trail-independent
            digest() : m_hash(0) {}
            digest(unsigned h, node* snap) : m_hash(h), m_snapshot(snap) {}
        };
        struct digest_hash_functor { unsigned operator()(digest const* d) const { return d->m_hash; } };
        struct digest_eq_functor {
            bool operator()(digest const* a, digest const* b) const { return a->m_snapshot->similar(*b->m_snapshot); }
        };

        // Per-depth bookkeeping for the (recursive) DFS driver. Replaces
        // what used to live directly on a persistent `node` object: since
        // there is only one live node now, everything that varies by DFS
        // depth (loop-cut/subsumption participation, the winning split's
        // resumable iterator, its last-produced edge) must live on the
        // call stack instead.
        struct dfs_frame {
            bool                                  m_is_signature_alias = false;
            scoped_ptr<digest>                    m_sibling_digest;      // non-null while this frame is on the active path
            scoped_ptr<split_iterator_i>           m_iter;                // resumable remaining branches, if any
            edge                                   m_last_edge;
        };

        unsigned                              m_next_facet_id = 0;
        ptr_vector<propagation_plugin_i>       m_prop_plugins;  // not owned
        ptr_vector<split_plugin_i>             m_split_plugins; // not owned
        scoped_ptr<node>                      m_root;
        trail_stack                            m_trail;
        unsigned                               m_max_search_depth = 1000;
        unsigned                               m_max_cost = 1000;
        unsigned                               m_max_nodes = 0; // 0 == unlimited
        dep_manager_t                          m_dep_mgr;
        stats                                  m_stats;

        // Transposition table: digests of node states already proven UNSAT
        // for reasons intrinsic to their own facets (not a sibling cut). A
        // node whose digest matches one present here is unsatisfiable
        // regardless of how it was reached.
        std::unordered_set<digest*, digest_hash_functor, digest_eq_functor> m_unsat_cache;
        ptr_vector<digest>                     m_unsat_cache_storage; // owns entries in m_unsat_cache

        // Active-path index for the sibling (loop-cut) subsumption rule:
        // while a frame is on the DFS path its digest is present in this
        // bucket, so a non-empty match for a newly-visited node means the
        // search has looped back to an ancestor with the same facet state.
        std::unordered_map<digest*, unsigned, digest_hash_functor, digest_eq_functor> m_siblings;

        // Hot-restart snapshot of the (unique, innermost) SAT leaf found by
        // the most recent `solve()` call, taken via the cold-path `clone()`
        // before the DFS unwind pops the trail scopes that produced it - so
        // callers can still inspect the satisfying facet state (e.g. read
        // off a model) after `solve()` has returned and the live node has
        // been restored to its pre-solve state.
        scoped_ptr<node>                       m_sat_snapshot;
        bool                                   m_sat_snapshot_taken = false;

        // Run every registered propagation plugin to a fixed point. The
        // fixed point is detected generically (no extra plugin API): a
        // round is a single pass over every plugin in registration order;
        // we stop once a full round leaves the node's raw facet fingerprint
        // unchanged, or a plugin reports conflict/satisfied.
        unsigned raw_fingerprint(node const& n) const {
            unsigned h = n.num_facets() + 1;
            for (facet_id id = 0; id < n.num_facets(); ++id)
                if (n.has_facet(id))
                    h = combine_hash(h, n.facet(id).hash());
            return h;
        }

        simplify_result propagate_to_fixpoint(node& n) {
            // Bound the number of rounds by the number of plugins plus
            // facets: propagation must be confluent/terminating, so this
            // is a safety net against a misbehaving plugin, not a normal
            // termination condition.
            unsigned max_rounds = (m_prop_plugins.size() + n.num_facets() + 1) * 4 + 8;
            unsigned prev_fp = raw_fingerprint(n);
            for (unsigned round = 0; round < max_rounds; ++round) {
                for (auto* p : m_prop_plugins) {
                    m_stats.m_propagate_counts[p->name()]++;
                    simplify_result r = p->propagate(n);
                    if (r == simplify_result::conflict)
                        return r;
                    // NOTE: a plugin reporting `satisfied` only means ITS
                    // OWN facet is discharged, not that every other facet
                    // in this node is - the node is only truly satisfied
                    // once ALL facets agree (n.is_satisfied(), an AND over
                    // every registered facet). Keep running the remaining
                    // plugins in this round (and further rounds, since
                    // other facets may still need to react/propagate)
                    // rather than short-circuiting here.
                }
                unsigned fp = raw_fingerprint(n);
                if (fp == prev_fp)
                    break;
                prev_fp = fp;
            }
            return n.is_satisfied() ? simplify_result::satisfied : simplify_result::proceed;
        }

        scoped_ptr<digest> mk_digest(node& n) {
            return scoped_ptr<digest>(alloc(digest, n.hash(), n.clone(m_trail)));
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
                    m_stats.m_split_counts[sp->name()]++;
                    bool has_more = false;
                    bool committed = false;
                    m_trail.push_scope();
                    auto it = sp->split(n, cost, out, has_more, committed);
                    if (committed) {
                        frame.m_iter = std::move(it);
                        return true;
                    }
                    m_trail.pop_scope(1);
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
            m_trail.push_scope();
            if (iter.next(out))
                return true;
            m_trail.pop_scope(1);
            return false;
        }

        search_result dfs(node& n, unsigned depth_bound, unsigned depth) {
            m_stats.m_num_dfs_nodes++;
            if (m_max_nodes && m_stats.m_num_dfs_nodes > m_max_nodes)
                return search_result::unknown;

            dfs_frame frame;
            // Signature-alias frames (structural aliasing without genuine
            // recurrence, e.g. a lazily resumed split continuation) are
            // exempt from both caches; the engine has no generic way to
            // detect this itself in the trail-based model, so (as before)
            // it is plugin-driven - a facet can suppress caching for the
            // current frame by installing a sentinel via
            // `mark_signature_alias()` prior to re-entering dfs. For now,
            // this is left for facets to opt into via node state; the
            // generic engine simply always participates in both caches.
            {
                auto probe = mk_digest(n);
                auto it = m_unsat_cache.find(probe.get());
                if (it != m_unsat_cache.end()) {
                    m_stats.m_num_cache_hits++;
                    n.set_conflict(br_sibling, nullptr);
                    return search_result::unsat;
                }
                auto sib_it = m_siblings.find(probe.get());
                if (sib_it != m_siblings.end() && sib_it->second > 0) {
                    m_stats.m_num_sibling_cuts++;
                    n.set_conflict(br_sibling, nullptr);
                    return search_result::unsat;
                }
                frame.m_sibling_digest = std::move(probe);
            }

            search_result result;
            n.clear_status();
            simplify_result sr = propagate_to_fixpoint(n);
            if (sr == simplify_result::conflict) {
                result = search_result::unsat;
            }
            else if (sr == simplify_result::satisfied) {
                result = search_result::sat;
                m_sat_snapshot = n.clone(m_trail);
                m_sat_snapshot_taken = true;
            }
            else if (depth >= depth_bound) {
                result = search_result::depth_cutoff;
            }
            else {
                auto& bucket = m_siblings[frame.m_sibling_digest.get()];
                bucket++;

                edge first_edge;
                bool has_children = extend_node(n, frame, first_edge);

                if (!has_children) {
                    // No propagation conflict/satisfaction and no split rule
                    // has anything left to offer: the node is stuck (a
                    // genuine "unknown", not a depth cutoff - retrying with
                    // a larger depth bound will not help).
                    result = n.is_satisfied() ? search_result::sat : search_result::unknown;
                }
                else {
                    bool saw_unknown = false;
                    bool saw_depth_cutoff = false;
                    result = search_result::unsat;
                    edge cur_edge = first_edge;
                    bool have_branch = true;
                    while (have_branch) {
                        search_result cr;
                        {
                            scoped_pop pop(m_trail); // matches the scope the split committed for this branch
                            cr = dfs(n, depth_bound, depth + 1);
                            // Always pop back out of this branch, even on
                            // sat: the sat leaf's facet state was already
                            // captured by m_sat_snapshot (a cold-path
                            // clone taken where the leaf was found), so
                            // there is no need to leave any trail scopes
                            // suspended just to keep the live node in the
                            // satisfying state - callers that want to
                            // inspect it use sat_snapshot() instead.
                        }
                        if (cr == search_result::sat) {
                            result = search_result::sat;
                            break;
                        }
                        if (cr == search_result::depth_cutoff)
                            saw_depth_cutoff = true;
                        else if (cr == search_result::unknown)
                            saw_unknown = true;
                        have_branch = frame.m_iter && advance_iter(*frame.m_iter, cur_edge);
                    }
                    if (result != search_result::sat)
                        result = saw_depth_cutoff ? search_result::depth_cutoff
                               : saw_unknown       ? search_result::unknown
                               :                     search_result::unsat;
                }

                // Remove this frame's sibling-cache entry entirely rather
                // than just decrementing it to 0: `frame.m_sibling_digest`
                // (the map's key) is about to be destroyed when `frame`
                // goes out of scope (unless it gets promoted into
                // `m_unsat_cache` below, which re-inserts a fresh owned
                // key), so a lingering zero-count entry would leave a
                // dangling `digest*` key in `m_siblings` forever.
                auto sib_it2 = m_siblings.find(frame.m_sibling_digest.get());
                if (sib_it2 != m_siblings.end()) {
                    if (sib_it2->second > 1)
                        sib_it2->second--;
                    else
                        m_siblings.erase(sib_it2);
                }
            }

            // Cache the UNSAT verdict for this facet signature, regardless of
            // whether it came from an immediate propagation conflict or from
            // every child branch failing - both are properties of the node's
            // own facet state, and are safe to memoize across the rest of the
            // search.
            if (result == search_result::unsat && n.reason() != br_sibling) {
                auto* d = frame.m_sibling_digest.detach();
                if (m_unsat_cache.find(d) == m_unsat_cache.end()) {
                    m_unsat_cache.insert(d);
                    m_unsat_cache_storage.push_back(d);
                }
                else {
                    dealloc(d);
                }
            }
            return result;
        }

    public:
        search_tree() = default;
        ~search_tree() { for (auto* d : m_unsat_cache_storage) dealloc(d); }

        dep_manager_t& dep_mgr() { return m_dep_mgr; }
        trail_stack& trail() { return m_trail; }

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

        void add_propagation_plugin(propagation_plugin_i* p) { m_prop_plugins.push_back(p); }
        void add_split_plugin(split_plugin_i* p) { m_split_plugins.push_back(p); }

        void set_max_search_depth(unsigned d) { m_max_search_depth = d; }
        void set_max_cost(unsigned c) { m_max_cost = c; }
        void set_max_nodes(unsigned n) { m_max_nodes = n; }

        // Create the single root node (all facet slots initially null;
        // fill them in via the templated `register_facet<T>(node&, ...)`
        // overload above, or `node::install_facet` directly).
        node* mk_root() { SASSERT(!m_root); m_root = alloc(node, m_next_facet_id); return m_root.get(); }
        node* root() const { return m_root.get(); }

        // Non-null only immediately after a `solve()` call returned `sat`;
        // a standalone (trail-independent) snapshot of the satisfying
        // facet state. Overwritten/cleared by the next `solve()` call.
        node const* sat_snapshot() const { return m_sat_snapshot_taken ? m_sat_snapshot.get() : nullptr; }

        stats const& get_stats() const { return m_stats; }
        void reset_stats() { m_stats.reset(); }

        // Iterative-deepening DFS over the single live node (root, or a
        // caller-supplied node - almost always root). Trail scopes opened
        // during the search are always fully popped back to their level on
        // entry before `solve()` returns, regardless of verdict, so the
        // node's facet state is restored to what it was on entry. On sat,
        // callers inspect the satisfying state via `sat_snapshot()` (a
        // cold-path clone taken where the leaf was found) rather than the
        // live node.
        search_result solve(node* start = nullptr) {
            node* r = start ? start : m_root.get();
            SASSERT(r);
            m_stats.m_num_solve_calls++;
            unsigned base_scopes = m_trail.get_num_scopes();
            m_sat_snapshot = nullptr;
            m_sat_snapshot_taken = false;
            search_result final_res = search_result::unknown;
            for (unsigned depth_bound = 1; depth_bound <= m_max_search_depth; ++depth_bound) {
                m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth_bound);
                search_result res = dfs(*r, depth_bound, 0);
                SASSERT(m_trail.get_num_scopes() == base_scopes);
                if (res == search_result::sat) { m_stats.m_num_sat++; final_res = res; break; }
                if (res == search_result::unsat) { m_stats.m_num_unsat++; final_res = res; break; }
                if (res == search_result::unknown) {
                    // Genuinely stuck: no facets changed and no split
                    // available at any depth - retrying with a larger
                    // depth bound will not help, so stop deepening now.
                    final_res = res;
                    break;
                }
                // res == depth_cutoff: retrying with a larger depth bound
                // may still resolve this subtree, so keep deepening until
                // the search-depth budget is exhausted.
                final_res = res;
            }
            if (final_res == search_result::unknown || final_res == search_result::depth_cutoff) {
                m_stats.m_num_unknown++;
                final_res = search_result::unknown; // normalize: never leak depth_cutoff to callers
            }
            return final_res;
        }

    };

} // namespace stx

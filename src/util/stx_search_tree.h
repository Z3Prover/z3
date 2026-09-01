/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    stx_search_tree.h

Abstract:

    Domain-agnostic plugin-based search tree (namespace `stx`).

    This is "Phase 1" of the modular search-tree architecture described in
    the design document "A Modular Plugin-Based Search Tree for String
    Solving" (based on `theory_nseq` / `nielsen_graph` on the c3 branch).
    It provides a generic engine that knows nothing about sequences,
    strings, or automata: it manages nodes, edges, dependencies, conflict
    explanation, iterative deepening, subsumption, and backtracking over an
    abstract node *state*, which is a collection of *facets* contributed by
    plugins.

    The two extension points are:
      - `propagation_plugin_i`: deterministic, non-branching simplification.
      - `split_plugin_i`:       nondeterministic branching (search) rules,
                                selected lowest-cost-first.

    Everything domain-specific (string equalities, regex memberships,
    arithmetic constraints, ...) is expected to live *outside* this file, in
    facet/plugin implementations that only interact with the engine through
    `facet_i`, `propagation_plugin_i`, and `split_plugin_i`.

    Simplifications relative to the full `nielsen_graph` this design
    replaces (left for a later phase, once a concrete sequence
    instantiation exists to validate against):
      - The sibling/subsumption cut here is a plain "already on the active
        DFS path" cut. `nielsen_graph`'s Tarjan-style lowlink bookkeeping
        (`m_subtree_lowlink`/`m_subtree_has_cut`), which additionally proves
        *soundness* of caching a cut subtree's UNSAT verdict when arithmetic
        conflicts are mixed in, is not reproduced; here a node's UNSAT
        transposition-cache entry is only ever installed for nodes that are
        NOT signature aliases and were not themselves closed via a sibling
        cut, which is the simple, always-sound special case.
      - Hot restart is limited to reusing propagation results across
        iterative-deepening rounds within a single `solve()` call (the
        `m_simplify_stamp`/`solve_epoch` mechanism of §4.6); resuming a
        live search across separate external `solve()` invocations (as
        `nielsen_graph` does across incremental SMT `check()` calls) is
        future work.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#pragma once

#include "util/util.h"
#include "util/vector.h"
#include "util/dependency.h"
#include <string>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <climits>

namespace stx {

    // Result of a deterministic propagation pass.
    enum class simplify_result { proceed, conflict, satisfied };

    // Result of solve()/dfs().
    enum class search_result { sat, unsat, unknown };

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
     */
    class facet_i {
    public:
        virtual ~facet_i() = default;

        // Deep-clone this facet for a new child node. Nodes are persistent:
        // the parent facet is never mutated after a child has cloned it.
        virtual facet_i* clone() const = 0;

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

        // A named transformation producing a target node, with a
        // dependency-tracked justification. Substitutions/mutations are a
        // facet-level concept: an edge is materialized by a split plugin,
        // which clones the parent's facets (`search_tree::clone_node`),
        // mutates its own facet(s), and wraps the result in an edge. The
        // core only ever stores src/tgt/name/dep/is_progress.
        class edge {
            node*             m_src;
            node*             m_tgt;
            const char*       m_rule_name;
            dep_tracker       m_dep;
            bool              m_is_progress;
        public:
            edge(node* src, node* tgt, char const* rule_name, dep_tracker dep, bool is_progress) :
                m_src(src), m_tgt(tgt), m_rule_name(rule_name), m_dep(dep), m_is_progress(is_progress) {}
            node* src() const { return m_src; }
            node* tgt() const { return m_tgt; }
            char const* rule_name() const { return m_rule_name; }
            dep_tracker dep() const { return m_dep; }
            bool is_progress() const { return m_is_progress; }
        };

        // Deterministic, non-branching simplification. Must be confluent:
        // repeated application (in any order, interleaved with other
        // propagation plugins) converges to the same fixed point. May touch
        // only the facet kind(s) it was registered against.
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
        // at 0 and increasing.
        class split_plugin_i {
        public:
            virtual ~split_plugin_i() = default;
            virtual char const* name() const = 0;
            // - A split exists at exactly `cost`: append child edge(s) to
            //   `out` (each carrying a dep_tracker justification) and
            //   return true. A non-empty `out` claims this node for this
            //   plugin this round (lowest-cost, first-registered,
            //   non-empty result wins).
            // - No split at `cost` but one exists at a higher cost: leave
            //   `out` empty and return true (driver keeps raising `cost`).
            // - Nothing left to offer `n` at any cost: leave `out` empty
            //   and return false.
            virtual bool split(node& n, unsigned cost, ptr_vector<edge>& out) = 0;
        };

        enum class node_status { unevaluated, satisfied, conflict };

        // A node in the search tree. State = ordered vector of facet_i*,
        // one per registered facet_id, plus generic bookkeeping the core
        // owns directly.
        class node {
            friend class search_tree;

            unsigned            m_id;
            ptr_vector<facet_i> m_facets;          // indexed by facet_id
            ptr_vector<edge>    m_outgoing;
            node_status         m_status = node_status::unevaluated;
            backtrack_reason    m_reason = br_unevaluated;
            dep_tracker         m_conflict_dep = nullptr;
            mutable unsigned    m_hash = 0;         // 0 == unset

            // DFS bookkeeping for the sibling (loop-cut) subsumption rule:
            // structural depth of this node while it is on the active DFS
            // path (see search_tree::dfs).
            unsigned            m_dfs_path_pos = 0;
            bool                m_on_path = false;

            // True for nodes that structurally alias their parent's
            // signature without being a genuine recurrence (e.g. a lazily
            // resumed split continuation). Exempt from the sibling loop-cut
            // and from the unsat transposition cache, exactly as in
            // `nielsen_node::is_signature_alias`. Set by split plugins via
            // `mark_signature_alias()`.
            bool                m_signature_alias = false;

            // Simplification memo: the value of `search_tree::m_solve_epoch`
            // at the time `propagate_to_fixpoint` last completed on this
            // node. Cleared (0) whenever a facet is (re)installed via
            // `set_facet`.
            unsigned            m_simplify_stamp = 0;

            explicit node(unsigned id, unsigned num_facets) : m_id(id) {
                m_facets.resize(num_facets, nullptr);
            }

        public:
            ~node() {
                for (auto* f : m_facets) dealloc(f);
                for (auto* e : m_outgoing) dealloc(e);
            }

            unsigned id() const { return m_id; }
            unsigned num_facets() const { return m_facets.size(); }

            facet_i& facet(facet_id id) { SASSERT(m_facets[id]); return *m_facets[id]; }
            facet_i const& facet(facet_id id) const { SASSERT(m_facets[id]); return *m_facets[id]; }
            bool has_facet(facet_id id) const { return id < m_facets.size() && m_facets[id] != nullptr; }

            template <typename T> T& facet_as(facet_id id) { return static_cast<T&>(facet(id)); }
            template <typename T> T const& facet_as(facet_id id) const { return static_cast<T const&>(facet(id)); }

            // Install (or replace) the facet at `id`. Takes ownership.
            void set_facet(facet_id id, facet_i* f) {
                if (m_facets[id]) dealloc(m_facets[id]);
                m_facets[id] = f;
                m_hash = 0;
                m_simplify_stamp = 0;
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

            backtrack_reason reason() const { return m_reason; }
            dep_tracker conflict_dep() const { return m_conflict_dep; }

            void mark_signature_alias() { m_signature_alias = true; }
            bool is_signature_alias() const { return m_signature_alias; }

            // Canonicalized structural hash over all installed facets;
            // cached until a facet is replaced via set_facet.
            unsigned hash() const {
                if (m_hash)
                    return m_hash;
                unsigned h = m_facets.size() + 1;
                for (auto* f : m_facets)
                    h = combine_hash(h, f ? f->hash() : 0);
                m_hash = h ? h : 1; // 0 is reserved for "unset"
                return m_hash;
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

            ptr_vector<edge>& outgoing() { return m_outgoing; }
            ptr_vector<edge> const& outgoing() const { return m_outgoing; }
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
        struct node_hash_functor { unsigned operator()(node* n) const { return n->hash(); } };
        struct node_eq_functor   { bool operator()(node* a, node* b) const { return a->similar(*b); } };

        unsigned                              m_next_facet_id = 0;
        ptr_vector<node>                       m_nodes;         // owns every node ever created
        ptr_vector<propagation_plugin_i>       m_prop_plugins;  // not owned
        ptr_vector<split_plugin_i>             m_split_plugins; // not owned
        node*                                  m_root = nullptr;
        unsigned                               m_max_search_depth = 1000;
        unsigned                               m_max_cost = 1000;
        unsigned                               m_max_nodes = 0; // 0 == unlimited
        unsigned                               m_solve_epoch = 1;
        dep_manager_t                          m_dep_mgr;
        stats                                  m_stats;

        // Transposition table: signatures of nodes already proven UNSAT for
        // reasons intrinsic to their own facets (not a sibling cut). A node
        // whose signature is present is unsatisfiable regardless of how it
        // was reached.
        std::unordered_set<node*, node_hash_functor, node_eq_functor> m_unsat_cache;

        // Active-path index for the sibling (loop-cut) subsumption rule:
        // while a node is on the DFS path it is present in this bucket
        // keyed by its own signature, so a non-empty match for a
        // newly-visited node means the search has looped back to an
        // ancestor with the same facet state.
        std::unordered_map<node*, ptr_vector<node>, node_hash_functor, node_eq_functor> m_siblings;

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
            if (n.m_simplify_stamp == m_solve_epoch) {
                if (n.is_conflict()) return simplify_result::conflict;
                if (n.is_satisfied()) return simplify_result::satisfied;
                return simplify_result::proceed;
            }
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
                    if (r == simplify_result::conflict) {
                        n.m_simplify_stamp = m_solve_epoch;
                        return r;
                    }
                    if (r == simplify_result::satisfied) {
                        n.set_satisfied();
                        n.m_simplify_stamp = m_solve_epoch;
                        return r;
                    }
                }
                unsigned fp = raw_fingerprint(n);
                if (fp == prev_fp)
                    break;
                prev_fp = fp;
            }
            n.m_simplify_stamp = m_solve_epoch;
            return n.is_satisfied() ? simplify_result::satisfied : simplify_result::proceed;
        }

        // Search for the cheapest available split, raising `cost` from 0.
        // Returns false once every plugin has nothing left to offer at any
        // cost (the node is closed: no more splits).
        bool extend_node(node& n, ptr_vector<edge>& out) {
            for (unsigned cost = 0; cost <= m_max_cost; ++cost) {
                bool any_offer = false;
                for (auto* sp : m_split_plugins) {
                    out.reset();
                    m_stats.m_split_counts[sp->name()]++;
                    bool has_more = sp->split(n, cost, out);
                    if (!out.empty())
                        return true;
                    if (has_more)
                        any_offer = true;
                }
                if (!any_offer)
                    return false;
            }
            return false;
        }

        search_result dfs(node* n, unsigned depth_bound, unsigned depth) {
            m_stats.m_num_dfs_nodes++;
            if (m_max_nodes && m_stats.m_num_dfs_nodes > m_max_nodes)
                return search_result::unknown;

            if (!n->is_signature_alias()) {
                auto it = m_unsat_cache.find(n);
                if (it != m_unsat_cache.end()) {
                    m_stats.m_num_cache_hits++;
                    n->set_conflict(br_sibling, nullptr);
                    return search_result::unsat;
                }
                auto sib_it = m_siblings.find(n);
                if (sib_it != m_siblings.end() && !sib_it->second.empty()) {
                    m_stats.m_num_sibling_cuts++;
                    n->set_conflict(br_sibling, nullptr);
                    return search_result::unsat;
                }
            }

            search_result result;
            simplify_result sr = propagate_to_fixpoint(*n);
            if (sr == simplify_result::conflict) {
                result = search_result::unsat;
            }
            else if (sr == simplify_result::satisfied) {
                result = search_result::sat;
            }
            else if (depth >= depth_bound) {
                result = search_result::unknown;
            }
            else {
                n->m_on_path = true;
                n->m_dfs_path_pos = depth;
                if (!n->is_signature_alias())
                    m_siblings[n].push_back(n);

                ptr_vector<edge> children;
                bool has_children = extend_node(*n, children);

                if (!has_children) {
                    // No propagation conflict/satisfaction and no split rule
                    // has anything left to offer: the node is stuck.
                    result = n->is_satisfied() ? search_result::sat : search_result::unknown;
                }
                else {
                    bool saw_unknown = false;
                    result = search_result::unsat;
                    for (auto* e : children) {
                        n->m_outgoing.push_back(e);
                        search_result cr = dfs(e->tgt(), depth_bound, depth + 1);
                        if (cr == search_result::sat) {
                            result = search_result::sat;
                            break;
                        }
                        if (cr == search_result::unknown)
                            saw_unknown = true;
                    }
                    if (result != search_result::sat)
                        result = saw_unknown ? search_result::unknown : search_result::unsat;
                }

                n->m_on_path = false;
                if (!n->is_signature_alias()) {
                    auto& bucket = m_siblings[n];
                    if (!bucket.empty())
                        bucket.pop_back();
                }
            }

            // Cache the UNSAT verdict for this facet signature, regardless of
            // whether it came from an immediate propagation conflict or from
            // every child branch failing - both are properties of the node's
            // own facet state, and are safe to memoize across the rest of the
            // search (see the module comment for the soundness caveat this
            // Phase-1 implementation carries relative to nielsen_graph's
            // Tarjan lowlink bookkeeping).
            if (result == search_result::unsat && !n->is_signature_alias() && n->reason() != br_sibling)
                m_unsat_cache.insert(n);
            return result;
        }

    public:
        search_tree() = default;
        ~search_tree() { for (auto* n : m_nodes) dealloc(n); }

        dep_manager_t& dep_mgr() { return m_dep_mgr; }

        // Reserve a new facet slot; returns its stable id.
        facet_id register_facet() { return m_next_facet_id++; }

        void add_propagation_plugin(propagation_plugin_i* p) { m_prop_plugins.push_back(p); }
        void add_split_plugin(split_plugin_i* p) { m_split_plugins.push_back(p); }

        void set_max_search_depth(unsigned d) { m_max_search_depth = d; }
        void set_max_cost(unsigned c) { m_max_cost = c; }
        void set_max_nodes(unsigned n) { m_max_nodes = n; }

        // Allocate a fresh, facet-less node (all slots null). The caller
        // (typically the domain's root-construction code, or a split
        // plugin cloning a parent) must fill in facets via set_facet.
        node* mk_node() {
            node* n = alloc(node, m_nodes.size(), m_next_facet_id);
            m_nodes.push_back(n);
            return n;
        }

        // Deep-clone every installed facet of `parent` into a fresh node.
        // Used by split plugins to materialize a child before mutating
        // their own facet(s).
        node* clone_node(node const& parent) {
            node* n = mk_node();
            for (facet_id id = 0; id < parent.num_facets(); ++id)
                if (parent.has_facet(id))
                    n->set_facet(id, parent.facet(id).clone());
            return n;
        }

        node* mk_root() { SASSERT(!m_root); m_root = mk_node(); return m_root; }
        node* root() const { return m_root; }

        stats const& get_stats() const { return m_stats; }
        void reset_stats() { m_stats.reset(); }

        // Iterative-deepening DFS from `root` (or a caller-supplied node).
        // Bumps the solve epoch once (hot restart: propagation results are
        // reused across depth-bound increments within this call).
        search_result solve(node* start = nullptr) {
            node* r = start ? start : m_root;
            SASSERT(r);
            m_stats.m_num_solve_calls++;
            m_solve_epoch++;
            for (unsigned depth_bound = 1; depth_bound <= m_max_search_depth; ++depth_bound) {
                m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth_bound);
                search_result res = dfs(r, depth_bound, 0);
                if (res == search_result::sat) { m_stats.m_num_sat++; return res; }
                if (res == search_result::unsat) { m_stats.m_num_unsat++; return res; }
                // res == unknown: either genuinely stuck (no facets changed
                // and no split available - retrying with a larger depth
                // bound will not help) or a depth cutoff (retrying helps).
                // We cannot distinguish those two cases from the return
                // value alone, so we simply keep deepening until the
                // search-depth budget is exhausted.
            }
            m_stats.m_num_unknown++;
            return search_result::unknown;
        }
    };

} // namespace stx

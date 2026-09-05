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
#include <climits>
#include <ostream>

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

        // Order/collision-insensitive hash contribution (canonicalized
        // internally by the facet, e.g. by sorting its own constraint
        // vector). Currently unused by the generic engine (the
        // transposition/sibling caches that consumed it were removed);
        // kept as part of the facet contract for possible future reuse.
        virtual unsigned hash() const = 0;

        // Are `this` and `other` equivalent for subsumption purposes? (same
        // facet_id assumed; the engine only ever compares facets that come
        // from the same registered slot.) Equality modulo representation,
        // not pointer identity. Currently unused by the generic engine.
        virtual bool similar(facet_i const& other) const = 0;

        // Is this facet's constraint set trivially/vacuously satisfied
        // (e.g. no equations left, or an empty membership set)?
        virtual bool is_satisfied() const = 0;

        // Print this facet's internal state (e.g. its pending equations/
        // disequations/memberships) for diagnostics. Default: print
        // nothing (a facet only needs to override this to be useful in
        // debugging output); the engine never relies on the output being
        // present.
        virtual std::ostream& display(std::ostream& out) const { return out; }
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

            // Canonicalized structural hash over all installed facets.
            // Always recomputed fresh (there is only ever one live node).
            // Currently unused by the generic engine (kept for possible
            // future reuse alongside facet_i::hash()).
            unsigned hash() const {
                unsigned h = m_facets.size() + 1;
                for (auto* f : m_facets)
                    h = combine_hash(h, f ? f->hash() : 0);
                return h ? h : 1; // 0 is reserved for "unset"
            }

            // Slot-wise `facet_i::similar`. Currently unused by the generic
            // engine (kept for possible future reuse).
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
        dep_manager_t                          m_dep_mgr;
        stats                                  m_stats;

        // Hot-restart snapshot of the (unique, innermost) SAT leaf found by
        // the most recent `solve()` call, taken via the cold-path `clone()`
        // before the DFS unwind pops the trail scopes that produced it - so
        // callers can still inspect the satisfying facet state (e.g. read
        // off a model) after `solve()` has returned and the live node has
        // been restored to its pre-solve state.
        scoped_ptr<node>                       m_sat_snapshot;

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

        search_result dfs(unsigned depth) {
            node& n = *m_root;
            m_stats.m_num_dfs_nodes++;
            if (m_max_nodes && m_stats.m_num_dfs_nodes > m_max_nodes)
                return search_result::unknown;
            if (!m_limit.inc())
                return search_result::unknown;

            dfs_frame frame;

            search_result result;
            n.clear_status();
            simplify_result sr = propagate_to_fixpoint(n);
            if (sr == simplify_result::conflict) {
                result = search_result::unsat;
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
                    // a larger depth bound will not help).
                    if (n.is_satisfied()) {
                        result = search_result::sat;
                        m_sat_snapshot = n.clone(m_trail);
                    }
                    else
                        result = search_result::unknown;
                }
                else {
                    bool saw_unknown = false;
                    bool saw_depth_cutoff = false;
                    result = search_result::unsat;
                    edge cur_edge = first_edge;
                    bool have_branch = true;
                    while (have_branch) {
                        search_result cr;
                        cr = dfs(depth + 1);
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
                        // when it hit conflict, so there is nothing to
                        // join here.
                        if (result == search_result::unsat)
                            n.set_conflict(br_children_failed, nullptr);
                    }
                }
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

        // Create the single root node (all facet slots initially null;
        // fill them in via the templated `register_facet<T>(node&, ...)`
        // overload above, or `node::install_facet` directly).
        node* mk_root() { SASSERT(!m_root); m_root = alloc(node, m_next_facet_id); return m_root.get(); }
        node* root() const { return m_root.get(); }

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
            st.update("stx num solve calls", m_stats.m_num_solve_calls);
            st.update("stx num dfs nodes", m_stats.m_num_dfs_nodes);
            st.update("stx num sat", m_stats.m_num_sat);
            st.update("stx num unsat", m_stats.m_num_unsat);
            st.update("stx num unknown", m_stats.m_num_unknown);
            st.update("stx max depth", m_stats.m_max_depth);
            for (auto const& [k, v] : m_stats.m_propagate_counts)
                st.update((std::string("stx propagate ") + k).c_str(), v);
            for (auto const& [k, v] : m_stats.m_split_counts)
                st.update((std::string("stx split ") + k).c_str(), v);
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
            unsigned base_scopes = m_trail.get_num_scopes();
            on_scope_exit rewind([&]() {
                while (m_trail.get_num_scopes() > base_scopes)
                    pop();
            });
            m_sat_snapshot = nullptr;
            m_root->clear_conflict_deps();
            search_result res = search_result::depth_cutoff;
            for (unsigned depth_bound = 1; depth_bound <= m_max_search_depth && res == search_result::depth_cutoff; ++depth_bound) {
                if (!m_limit.inc()) {
                    res = search_result::unknown;
                    break;
                }
                m_depth_bound = depth_bound;
                m_stats.m_max_depth = std::max(m_stats.m_max_depth, depth_bound);
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

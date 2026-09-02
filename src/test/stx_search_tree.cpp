/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    stx_search_tree.cpp

Abstract:

    Unit test for the domain-agnostic `stx::search_tree` engine
    (util/stx_search_tree.h), exercising propagation, branching search,
    conflict detection, satisfied-node detection, the transposition/unsat
    cache, and the depth-bound ("unknown") path with a small toy facet: a
    single integer counter that is incremented by 1 or 2 per branch, with an
    optional set of forbidden intermediate totals.

    This exercises the trail/iterator-based engine: there is one live node,
    mutated in place by `counter_facet::add()`, which registers a
    `value_trail<int>` undo object rather than being cloned; `step_split`
    materializes its first branch ("+1") immediately (mutating and pushing
    one trail scope) and returns a `split_iterator_i` that produces the
    second branch ("+2") on resumption.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "util/stx_search_tree.h"
#include "util/util.h"
#include "util/trail.h"
#include <iostream>
#include <unordered_set>

namespace {

    using tree_t = stx::search_tree<unsigned>;

    struct counter_config {
        int                       m_target;
        std::unordered_set<int>   m_forbidden;
    };

    // Toy facet: a single non-negative integer counter, mutated in place.
    class counter_facet : public stx::facet_i {
        counter_config const* m_cfg;
        int                    m_total;
    public:
        counter_facet(trail_stack& trail, counter_config const* cfg, int total) :
            facet_i(trail), m_cfg(cfg), m_total(total) {}
        int total() const { return m_total; }

        // Destructive mutator: registers a trail undo object instead of
        // being cloned. `m_trail.push(value_trail<int>(m_total))` snapshots
        // the current value and restores it on pop_scope(). Callers push
        // the enclosing scope themselves (via `push_scope()`) before the
        // first mutation of a branch.
        void push_scope() { m_trail.push_scope(); }
        void add(int delta) {
            m_trail.push(value_trail<int>(m_total));
            m_total += delta;
        }

        facet_i* clone(trail_stack& trail) const override { return alloc(counter_facet, trail, m_cfg, m_total); }
        unsigned hash() const override { return combine_hash(17u, static_cast<unsigned>(m_total)); }
        bool similar(facet_i const& other) const override {
            return m_total == static_cast<counter_facet const&>(other).m_total;
        }
        bool is_satisfied() const override { return m_total == m_cfg->m_target; }
    };

    // Propagation: fail as soon as the total overshoots the target or lands
    // on a forbidden value; otherwise a no-op (satisfaction is handled by
    // counter_facet::is_satisfied(), consulted generically by the engine).
    class overshoot_propagation : public tree_t::propagation_plugin_i {
        stx::facet_id          m_id;
        counter_config const*  m_cfg;
    public:
        overshoot_propagation(stx::facet_id id, counter_config const* cfg) : m_id(id), m_cfg(cfg) {}
        char const* name() const override { return "overshoot"; }
        stx::simplify_result propagate(tree_t::node& n) override {
            auto& f = n.facet_as<counter_facet>(m_id);
            if (f.total() > m_cfg->m_target || m_cfg->m_forbidden.count(f.total())) {
                n.set_conflict(stx::br_plugin_base, nullptr);
                return stx::simplify_result::conflict;
            }
            if (f.total() == m_cfg->m_target)
                return stx::simplify_result::satisfied;
            return stx::simplify_result::proceed;
        }
    };

    // Split: branch into "+1" and "+2" as two alternative edges at cost 0.
    // The first branch is materialized immediately by `split()`; the
    // second is produced lazily, on resumption, by `iterator::next()`.
    class step_split : public tree_t::split_plugin_i {
        stx::facet_id           m_id;
        counter_config const*   m_cfg;

        class iterator : public tree_t::split_iterator_i {
            tree_t::node&  m_n;
            stx::facet_id  m_id;
            bool           m_done = false;
        public:
            iterator(tree_t::node& n, stx::facet_id id) : m_n(n), m_id(id) {}
            bool next(tree_t::edge& out) override {
                if (m_done)
                    return false;
                m_done = true;
                auto& f = m_n.facet_as<counter_facet>(m_id);
                f.push_scope();
                f.add(2);
                out = tree_t::edge("+2", nullptr, true, 0);
                return true;
            }
        };

    public:
        step_split(stx::facet_id id, counter_config const* cfg) : m_id(id), m_cfg(cfg) {}
        char const* name() const override { return "step"; }
        std::unique_ptr<tree_t::split_iterator_i> split(tree_t::node& n, unsigned cost, tree_t::edge& out, bool& has_more) override {
            has_more = false;
            if (cost != 0)
                return nullptr;
            auto& f = n.facet_as<counter_facet>(m_id);
            if (f.total() >= m_cfg->m_target)
                return nullptr;
            f.push_scope();
            f.add(1);
            out = tree_t::edge("+1", nullptr, true, 0);
            return std::make_unique<iterator>(n, m_id);
        }
    };

    // Build a fresh engine + root for the given config; caller owns nothing
    // extra to clean up (search_tree's destructor frees all state).
    tree_t::node* mk_root(tree_t& tree, stx::facet_id& id, counter_config const* cfg) {
        tree_t::node* root = tree.mk_root();
        id = tree.register_facet<counter_facet>(*root, cfg, 0);
        return root;
    }

    static void tst_sat() {
        counter_config cfg{ 5, { 3 } };
        tree_t tree;
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        overshoot_propagation prop(id, &cfg);
        step_split split(id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        tree.set_max_search_depth(10);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::sat);
        ENSURE(tree.get_stats().m_num_sat == 1);
        ENSURE(tree.sat_snapshot() != nullptr);
        ENSURE(tree.sat_snapshot()->facet_as<counter_facet>(id).total() == 5);
        // The live root's facet state must be fully restored after solve().
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

    static void tst_unsat() {
        // target itself is forbidden: every path to reach it conflicts, and
        // overshooting past it (target=3, step +2 from total=2) also
        // conflicts, so the whole tree is UNSAT.
        counter_config cfg{ 3, { 3 } };
        tree_t tree;
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        overshoot_propagation prop(id, &cfg);
        step_split split(id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        tree.set_max_search_depth(10);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::unsat);
        ENSURE(tree.get_stats().m_num_unsat == 1);
        // total==2 is reachable via both [1,1] and [2]; once one of those
        // subtrees is fully explored and cached as UNSAT the other occurrence
        // should hit the transposition cache.
        ENSURE(tree.get_stats().m_num_cache_hits > 0);
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

    static void tst_unknown_depth_cutoff() {
        // Unreachable within the depth bound (target requires >2 steps),
        // and not otherwise refutable, so the search reports unknown.
        counter_config cfg{ 100, {} };
        tree_t tree;
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        overshoot_propagation prop(id, &cfg);
        step_split split(id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        tree.set_max_search_depth(2);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::unknown);
        ENSURE(tree.get_stats().m_num_unknown == 1);
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

    static void tst_trivially_satisfied_root() {
        counter_config cfg{ 0, {} };
        tree_t tree;
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        overshoot_propagation prop(id, &cfg);
        step_split split(id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        tree.set_max_search_depth(5);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::sat);
    }

} // namespace

void tst_stx_search_tree() {
    tst_sat();
    tst_unsat();
    tst_unknown_depth_cutoff();
    tst_trivially_satisfied_root();
    std::cout << "stx_search_tree: all tests passed\n";
}

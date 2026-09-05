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
        // the current value and restores it on pop_scope(). The engine
        // pushes the enclosing scope before calling split()/next(); the
        // facet/plugin code never calls push_scope()/pop_scope() itself.
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
            return stx::simplify_result::noop;
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
                f.add(2);
                out = tree_t::edge("+2", nullptr, true, 0);
                return true;
            }
        };

    public:
        step_split(stx::facet_id id, counter_config const* cfg) : m_id(id), m_cfg(cfg) {}
        char const* name() const override { return "step"; }
        scoped_ptr<tree_t::split_iterator_i> split(tree_t::node& n, unsigned cost, tree_t::edge& out, bool& has_more, bool& committed) override {
            has_more = false;
            committed = false;
            if (cost != 0)
                return nullptr;
            auto& f = n.facet_as<counter_facet>(m_id);
            if (f.total() >= m_cfg->m_target)
                return nullptr;
            f.add(1);
            out = tree_t::edge("+1", nullptr, true, 0);
            committed = true;
            return alloc(iterator, n, m_id);
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
        trail_stack tr;
        reslimit lim;
        tree_t tree(tr, lim);
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        tree.add_propagation_plugin(alloc(overshoot_propagation, id, &cfg));
        tree.add_split_plugin(alloc(step_split, id, &cfg));
        tree.set_max_search_depth(10);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::sat);
        ENSURE(tree.get_stats().m_num_sat == 1);
        ENSURE(tree.sat_snapshot() != nullptr);
        ENSURE(tree.sat_snapshot()->facet_as<counter_facet>(id).total() == 5);
        // The live root's trail scopes are always fully popped back to
        // base level by solve() before it returns, regardless of verdict:
        // the satisfying state is only available via sat_snapshot().
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

    static void tst_unsat() {
        // target itself is forbidden: every path to reach it conflicts, and
        // overshooting past it (target=3, step +2 from total=2) also
        // conflicts, so the whole tree is UNSAT.
        counter_config cfg{ 3, { 3 } };
        trail_stack tr;
        reslimit lim;
        tree_t tree(tr, lim);
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        tree.add_propagation_plugin(alloc(overshoot_propagation, id, &cfg));
        tree.add_split_plugin(alloc(step_split, id, &cfg));
        tree.set_max_search_depth(10);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::unsat);
        ENSURE(tree.get_stats().m_num_unsat == 1);
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

    static void tst_unknown_depth_cutoff() {
        // Unreachable within the depth bound (target requires >2 steps),
        // and not otherwise refutable, so the search reports unknown.
        counter_config cfg{ 100, {} };
        trail_stack tr;
        reslimit lim;
        tree_t tree(tr, lim);
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        tree.add_propagation_plugin(alloc(overshoot_propagation, id, &cfg));
        tree.add_split_plugin(alloc(step_split, id, &cfg));
        tree.set_max_search_depth(2);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::unknown);
        ENSURE(tree.get_stats().m_num_unknown == 1);
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

    static void tst_trivially_satisfied_root() {
        counter_config cfg{ 0, {} };
        trail_stack tr;
        reslimit lim;
        tree_t tree(tr, lim);
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        tree.add_propagation_plugin(alloc(overshoot_propagation, id, &cfg));
        tree.add_split_plugin(alloc(step_split, id, &cfg));
        tree.set_max_search_depth(5);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::sat);
    }

    // A second solve() call (e.g. after the caller has mutated facets, or
    // just re-solving as-is) must still find the same sat result: the live
    // root is always back at base level after a solve() call (sat or not),
    // so there is no suspended-scope state to leak/compound across calls.
    static void tst_resolve_after_sat_resumes_base_level() {
        counter_config cfg{ 5, { 3 } };
        trail_stack tr;
        reslimit lim;
        tree_t tree(tr, lim);
        stx::facet_id id;
        mk_root(tree, id, &cfg);
        tree.add_propagation_plugin(alloc(overshoot_propagation, id, &cfg));
        tree.add_split_plugin(alloc(step_split, id, &cfg));
        tree.set_max_search_depth(10);

        ENSURE(tree.solve() == stx::search_result::sat);
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);

        ENSURE(tree.solve() == stx::search_result::sat);
        ENSURE(tree.root()->facet_as<counter_facet>(id).total() == 0);
    }

} // namespace

void tst_stx_search_tree() {
    tst_sat();
    tst_unsat();
    tst_unknown_depth_cutoff();
    tst_trivially_satisfied_root();
    tst_resolve_after_sat_resumes_base_level();
    std::cout << "stx_search_tree: all tests passed\n";
}


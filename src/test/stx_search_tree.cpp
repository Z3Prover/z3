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

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "util/stx_search_tree.h"
#include "util/util.h"
#include <iostream>
#include <unordered_set>

namespace {

    using tree_t = stx::search_tree<unsigned>;

    struct counter_config {
        int                       m_target;
        std::unordered_set<int>   m_forbidden;
    };

    // Toy facet: a single non-negative integer counter.
    class counter_facet : public stx::facet_i {
        counter_config const* m_cfg;
        int                    m_total;
    public:
        counter_facet(counter_config const* cfg, int total) : m_cfg(cfg), m_total(total) {}
        int total() const { return m_total; }
        facet_i* clone() const override { return alloc(counter_facet, m_cfg, m_total); }
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
    class step_split : public tree_t::split_plugin_i {
        tree_t&                m_tree;
        stx::facet_id           m_id;
        counter_config const*   m_cfg;
    public:
        step_split(tree_t& tree, stx::facet_id id, counter_config const* cfg) :
            m_tree(tree), m_id(id), m_cfg(cfg) {}
        char const* name() const override { return "step"; }
        bool split(tree_t::node& n, unsigned cost, ptr_vector<tree_t::edge>& out) override {
            if (cost != 0)
                return false;
            auto& f = n.facet_as<counter_facet>(m_id);
            if (f.total() >= m_cfg->m_target)
                return false;
            for (int delta : {1, 2}) {
                tree_t::node* child = m_tree.clone_node(n);
                child->set_facet(m_id, alloc(counter_facet, m_cfg, f.total() + delta));
                out.push_back(alloc(tree_t::edge, &n, child, delta == 1 ? "+1" : "+2", nullptr, true));
            }
            return true;
        }
    };

    // Build a fresh engine + root for the given config; caller owns nothing
    // extra to clean up (search_tree's destructor frees all nodes).
    tree_t::node* mk_root(tree_t& tree, stx::facet_id id, counter_config const* cfg) {
        tree_t::node* root = tree.mk_root();
        root->set_facet(id, alloc(counter_facet, cfg, 0));
        return root;
    }

    static void tst_sat() {
        counter_config cfg{ 5, { 3 } };
        tree_t tree;
        stx::facet_id id = tree.register_facet();
        overshoot_propagation prop(id, &cfg);
        step_split split(tree, id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        mk_root(tree, id, &cfg);
        tree.set_max_search_depth(10);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::sat);
        ENSURE(tree.get_stats().m_num_sat == 1);
    }

    static void tst_unsat() {
        // target itself is forbidden: every path to reach it conflicts, and
        // overshooting past it (target=3, step +2 from total=2) also
        // conflicts, so the whole tree is UNSAT.
        counter_config cfg{ 3, { 3 } };
        tree_t tree;
        stx::facet_id id = tree.register_facet();
        overshoot_propagation prop(id, &cfg);
        step_split split(tree, id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        mk_root(tree, id, &cfg);
        tree.set_max_search_depth(10);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::unsat);
        ENSURE(tree.get_stats().m_num_unsat == 1);
        // total==2 is reachable via both [1,1] and [2]; once one of those
        // subtrees is fully explored and cached as UNSAT the other occurrence
        // should hit the transposition cache.
        ENSURE(tree.get_stats().m_num_cache_hits > 0);
    }

    static void tst_unknown_depth_cutoff() {
        // Unreachable within the depth bound (target requires >2 steps),
        // and not otherwise refutable, so the search reports unknown.
        counter_config cfg{ 100, {} };
        tree_t tree;
        stx::facet_id id = tree.register_facet();
        overshoot_propagation prop(id, &cfg);
        step_split split(tree, id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        mk_root(tree, id, &cfg);
        tree.set_max_search_depth(2);
        stx::search_result r = tree.solve();
        ENSURE(r == stx::search_result::unknown);
        ENSURE(tree.get_stats().m_num_unknown == 1);
    }

    static void tst_trivially_satisfied_root() {
        counter_config cfg{ 0, {} };
        tree_t tree;
        stx::facet_id id = tree.register_facet();
        overshoot_propagation prop(id, &cfg);
        step_split split(tree, id, &cfg);
        tree.add_propagation_plugin(&prop);
        tree.add_split_plugin(&split);
        mk_root(tree, id, &cfg);
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

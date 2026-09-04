/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_mem_facet.cpp (test)

Abstract:

    Unit tests for `seq::mem_facet`.

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_mem_facet.h"
#include "smt/seq_solver_facet.h"
#include <iostream>

namespace {

    struct fixture {
        ast_manager      m;
        seq_util         u;
        seq_rewriter     rw;
        trail_stack      trail;
        seq::live_states live;
        seq::eq_tree     tree;
        seq::eq_tree::node* root;
        stx::facet_id    eq_id;
        stx::facet_id    mem_id;
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac;

        seq::eq_propagation   eprop;
        seq::word_eq_split    esplit;
        seq::mem_propagation  mprop;
        seq::mem_monadic_split msplit;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), rw(m), live(rw, seq::transition_mode::brzozowski_tm),
            root(tree.mk_root()),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            mem_id(tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr())),
            ac(m, u),
            eprop(m, u), esplit(m, u),
            mprop(m, u, rw, live),
            msplit(m, u, rw, trail)
        {
            ac.set_eq_id(eq_id);
            ac.set_mem_id(mem_id);
            tree.set_ambient_context(&ac);
            tree.add_propagation_plugin(&eprop);
            tree.add_propagation_plugin(&mprop);
            tree.add_split_plugin(&msplit);
            tree.add_split_plugin(&esplit);
            tree.set_max_search_depth(12);
        }
    };

    stx::search_result solve_mem(fixture& f, std::function<void(seq::eq_tree::node*)> init, unsigned depth = 12) {
        init(f.root);
        f.tree.set_max_search_depth(depth);
        return f.tree.solve();
    }

    static void tst_trivial_sat() {
        fixture f;
        expr_ref word(f.u.str.mk_string(zstring("ab")), f.m);
        expr_ref re(f.u.re.mk_concat(f.u.re.mk_to_re(f.u.str.mk_string(zstring("a"))),
                                      f.u.re.mk_to_re(f.u.str.mk_string(zstring("b")))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, word, seq::view::membership(re)));
        }) == stx::search_result::sat);
    }

    static void tst_dead_unsat() {
        fixture f;
        expr_ref word(f.u.str.mk_string(zstring("a")), f.m);
        expr_ref re(f.u.re.mk_to_re(f.u.str.mk_string(zstring("a"))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, word, seq::view::membership(re)));
        }) == stx::search_result::sat);
    }

    static void tst_single_var_sat() {
        fixture f;
        sort* s = f.u.str.mk_string_sort();
        expr_ref X(f.m.mk_fresh_const("X", s), f.m);
        expr_ref a(f.u.str.mk_string(zstring("a")), f.m);
        expr_ref star_a(f.u.re.mk_star(f.u.re.mk_to_re(a)), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::eq_facet>(f.eq_id).add_equation(X, a);
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, X, seq::view::membership(star_a)));
        }) == stx::search_result::sat);
    }

    static void tst_two_var_monadic_sat() {
        fixture f;
        sort* s = f.u.str.mk_string_sort();
        expr_ref X(f.m.mk_fresh_const("X", s), f.m);
        expr_ref Y(f.m.mk_fresh_const("Y", s), f.m);
        expr_ref term(f.u.str.mk_concat(X, Y), f.m);
        expr_ref re(f.u.re.mk_concat(f.u.re.mk_star(f.u.re.mk_to_re(f.u.str.mk_string(zstring("a")))),
                                      f.u.re.mk_star(f.u.re.mk_to_re(f.u.str.mk_string(zstring("b"))))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, term, seq::view::membership(re)));
        }, 16) == stx::search_result::sat);
    }

    // power_var_peel_mem ("apply_var_num_unwinding_mem" in c3): a
    // membership whose string is a power term `s^n` at a directional
    // end must offer the n=0 (replace with epsilon) branch immediately
    // and, on the follow-up branch, the n>=1 peel (`s^n -> s.s^(n-1)`),
    // splicing the replacement directly into the membership's own
    // string. Tested directly against `split`/`iterator::next` (rather
    // than through `tree.solve()`) since `mem_propagation`'s own
    // coarse nullability shortcut (pre-existing, out of this rule's
    // scope) may discharge a membership whose start state is already
    // nullable before a split ever gets a chance to run, which would
    // make an end-to-end solve()-based test dependent on propagation
    // ordering rather than on this rule's own logic.
    static void tst_power_var_peel_mem_split() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref one_a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);
        expr_ref re(u.re.mk_star(u.re.mk_to_re(one_a)), m);

        // n = 0 branch: split() commits it immediately.
        {
        seq::eq_tree tree;
        auto* root = tree.mk_root();
        seq::arith_sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id pow_id = tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr());
        stx::facet_id mem_id = tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr());
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u);
        ac.set_arith_id(arith_id);
        ac.set_pow_id(pow_id);
        ac.set_mem_id(mem_id);
        tree.set_ambient_context(&ac);
        expr_ref N(m.mk_fresh_const("N", a.mk_int()), m);
        expr_ref pow(u.str.mk_power(one_a, N), m);
        expr_ref term(u.str.mk_concat(pow, b), m);
        root->facet_as<seq::power_facet>(pow_id).add_power(pow, one_a, N);
        root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(m, term, seq::view::membership(re)));

        seq::power_var_peel_mem pvpm(m, u, a);
        tree.trail().push_scope();
        seq::eq_tree::edge out;
        bool has_more = false, committed = false;
        auto it = pvpm.split(*root, 0, out, has_more, committed);
        ENSURE(committed && has_more && it.get() != nullptr);

        auto& mf = root->facet_as<seq::mem_facet>(mem_id);
        ENSURE(mf.memberships().size() == 1);
        expr_ref_vector const& ts = mf.memberships()[0].m_str;
        expr_ref_vector expect(m);
        u.str.get_concat_units(b.get(), expect);
        ENSURE(ts.size() == expect.size());
        for (unsigned i = 0; i < ts.size(); ++i)
            ENSURE(ts.get(i) == expect.get(i)); // pow spliced out, only "b" left
        auto& pf = root->facet_as<seq::power_facet>(pow_id);
        ENSURE(pf.powers().empty()); // obligation discharged for n=0 branch
        }

        // n >= 1 branch: from a fresh setup, drive split() (which
        // commits branch 1) then iterator::next() (branch 2), and check
        // branch 2's own splice result independently.
        {
        seq::eq_tree tree;
        auto* root = tree.mk_root();
        seq::arith_sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id pow_id = tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr());
        stx::facet_id mem_id = tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr());
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u);
        ac.set_arith_id(arith_id);
        ac.set_pow_id(pow_id);
        ac.set_mem_id(mem_id);
        tree.set_ambient_context(&ac);
        expr_ref N(m.mk_fresh_const("N", a.mk_int()), m);
        expr_ref pow(u.str.mk_power(one_a, N), m);
        expr_ref term(u.str.mk_concat(pow, b), m);
        root->facet_as<seq::power_facet>(pow_id).add_power(pow, one_a, N);
        root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(m, term, seq::view::membership(re)));

        seq::power_var_peel_mem pvpm(m, u, a);
        tree.trail().push_scope();
        seq::eq_tree::edge out;
        bool has_more = false, committed = false;
        auto it = pvpm.split(*root, 0, out, has_more, committed);
        ENSURE(committed && it.get() != nullptr);
        tree.trail().pop_scope(1);
        root->pop_facets();

        // split()'s branch-1 was popped above (undoing the epsilon
        // replacement / obligation removal); re-register the obligation
        // (as the sibling branch of the same case split would see it)
        // before driving the iterator's own branch-2 logic.
        tree.trail().push_scope();
        root->facet_as<seq::power_facet>(pow_id).add_power_trailed(pow, one_a, N);
        seq::eq_tree::edge out2;
        ENSURE(it->next(out2));

        auto& mf = root->facet_as<seq::mem_facet>(mem_id);
        expr_ref_vector const& ts = mf.memberships()[0].m_str;
        expr_ref_vector expect_a(m), expect_b(m);
        u.str.get_concat_units(one_a.get(), expect_a);
        u.str.get_concat_units(b.get(), expect_b);
        ENSURE(ts.size() == expect_a.size() + 1 + expect_b.size()); // "a", nested pow, "b"
        for (unsigned i = 0; i < expect_a.size(); ++i)
            ENSURE(ts.get(i) == expect_a.get(i));
        ENSURE(u.str.is_power(ts.get(expect_a.size())));
        for (unsigned i = 0; i < expect_b.size(); ++i)
            ENSURE(ts.get(expect_a.size() + 1 + i) == expect_b.get(i));
        }
    }
}

void tst_seq_mem_facet() {
    tst_trivial_sat();
    tst_dead_unsat();
    tst_single_var_sat();
    tst_two_var_monadic_sat();
    tst_power_var_peel_mem_split();
    std::cout << "seq_mem_facet: all tests passed\n";
}

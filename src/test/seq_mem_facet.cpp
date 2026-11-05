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
#include "ast/seq/seq_assumption_facet.h"
#include "smt/seq_solver_facet.h"
#include "util/rlimit.h"
#include "util/z3_exception.h"
#include <iostream>
#include <string>

namespace {

    struct fixture {
        struct ambient_context : seq::null_ambient_context<seq::eq_tree::dep_tracker> {
            using null_ambient_context::null_ambient_context;
            theory_seq_params params;
            theory_seq_params const& fparams() const override { return params; }
        };
        ast_manager      m;
        seq_util         u;
        arith_util       a;
        seq_rewriter     rw;
        trail_stack      trail;
        ambient_context  ac;
        seq::eq_tree     tree;
        seq::eq_tree::node* root;
        seq::sub_solver  solver;
        stx::facet_id    eq_id;
        stx::facet_id    deq_id;
        stx::facet_id    mem_id;
        stx::facet_id    arith_id;
        stx::facet_id    assumption_id;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), rw(m),
            ac(m, u, trail),
            tree(trail, m.limit()),
            root(tree.mk_root()),
            solver(m, a, tree.dep_mgr()),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            deq_id(tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr())),
            mem_id(tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac)),
            arith_id(tree.register_facet<seq::solver_facet>(*root, m, u, solver)),
            assumption_id(tree.register_facet<seq::assumption_facet>(*root, m))
        {
            ac.set_eq_id(eq_id);
            ac.set_deq_id(deq_id);
            ac.set_mem_id(mem_id);
            ac.set_arith_id(arith_id);
            ac.set_assumption_id(assumption_id);
            tree.set_ambient_context(&ac);
            tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::mem_propagation, m, u, rw));
            tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
            tree.add_split_plugin(alloc(seq::mem_monadic_split, m, u, rw, ac));
            tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
            tree.set_max_search_depth(12);
        }
    };

    stx::search_result solve_mem(fixture& f, std::function<void(seq::eq_tree::node*)> init, unsigned depth = 12) {
        init(f.root);
        f.tree.set_max_search_depth(depth);
        return f.tree.solve();
    }

    // mem_facet updates append new entries and deactivate old ones, so
    // tests must look for the single active membership.
    static seq::str_mem const& only_active_membership(seq::mem_facet const& mf) {
        seq::str_mem const* found = nullptr;
        for (auto const& sm : mf.memberships()) {
            if (!sm.active())
                continue;
            ENSURE(!found);   // exactly one active membership expected
            found = &sm;
        }
        ENSURE(found);
        return *found;
    }

    // All words over {a,b,c} with #letter == residue (mod modulus).
    static expr_ref count_regex(fixture& f, char letter, unsigned modulus, unsigned residue) {
        expr_ref other(f.u.re.mk_empty(f.u.re.mk_re(f.u.str.mk_string_sort())), f.m);
        for (char c : {'a', 'b', 'c'})
            if (c != letter) {
                char text[] = {c, 0};
                expr_ref r(f.u.re.mk_to_re(f.u.str.mk_string(text)), f.m);
                other = f.u.re.mk_union(other, r);
            }
        other = f.u.re.mk_star(other);
        char text[] = {letter, 0};
        expr_ref one(f.u.re.mk_to_re(f.u.str.mk_string(text)), f.m);
        one = f.u.re.mk_concat(one, other);
        expr_ref period(f.u.re.mk_loop(one, modulus, modulus), f.m);
        period = f.u.re.mk_star(period);
        expr_ref re(f.u.re.mk_concat(other, period), f.m);
        for (unsigned i = 0; i < residue; ++i)
            re = f.u.re.mk_concat(re, one);
        return re;
    }

    static void tst_letter_count_benchmark(bool mod5) {
        fixture f;
        expr_ref_vector x(f.m);
        for (unsigned i = 0; i < 3; ++i)
            x.push_back(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()));
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& dm = f.tree.dep_mgr();
        auto add = [&](std::initializer_list<unsigned> ids, char const* constant, unsigned residue, unsigned dep) {
            expr_ref_vector ts(f.m);
            for (unsigned i : ids)
                ts.push_back(x.get(i));
            // Keep a concrete string token as well as the usual exploded units.
            ts.push_back(f.u.str.mk_string(constant));
            expr_ref re = count_regex(f, mod5 ? 'b' : 'a', mod5 ? 5 : 3, residue);
            mf.add(seq::str_mem(f.m, ts, seq::view::membership(re, f.m), dm.mk_leaf(dep)));
        };
        if (mod5) {
            // Reduced easy_unsat0026, including its constant offsets.
            add({0, 1, 2}, "cabcc", 3, 1);
            add({2, 2, 0}, "bbb", 4, 2);
            add({0, 0, 1, 2}, "aa", 0, 3);
            add({0, 2}, "c", 1, 4);
        }
        else {
            // Reduced medium_unsat0057: four cross-subject membership rows.
            add({1, 1, 2}, "", 1, 1);
            add({1, 2}, "", 1, 2);
            add({0, 1, 2, 2}, "", 1, 3);
            add({0, 2, 2}, "", 0, 4);
        }
        seq::eq_tree::dep_tracker dep = nullptr;
        ENSURE(mf.check_letter_conflict(ef, dep));
        for (unsigned i = 1; i <= 4; ++i)
            ENSURE(dm.contains(dep, i));
        // Also exercise production branch propagation, before witness search.
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        ENSURE(propagation.propagate(*f.root) == stx::simplify_result::conflict);
        ENSURE(!mf.witness_extracted());
    }

    static void tst_letter_count_equations_scopes() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref y(f.m.mk_fresh_const("y", f.u.str.mk_string_sort()), f.m);
        expr_ref even = count_regex(f, 'a', 2, 0);
        expr_ref odd = count_regex(f, 'a', 2, 1);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& dm = f.tree.dep_mgr();
        mf.add(seq::str_mem(f.m, x, seq::view::membership(even, f.m), dm.mk_leaf(1)));
        mf.add(seq::str_mem(f.m, y, seq::view::membership(odd, f.m), dm.mk_leaf(2)));
        seq::eq_tree::dep_tracker dep = nullptr;
        // A previously materialized epsilon witness must NOT fix a free count.
        mf.set_witness(y, f.u.str.mk_string(""));
        ENSURE(!mf.check_letter_conflict(ef, dep) && !dep);
        f.trail.push_scope();
        ef.add_equation(x, y, dm.mk_leaf(3));
        ENSURE(mf.check_letter_conflict(ef, dep));
        for (unsigned i : {1u, 2u, 3u})
            ENSURE(dm.contains(dep, i));
        ef.remove_equation_trailed(0);
        ENSURE(!mf.check_letter_conflict(ef, dep));
        f.trail.pop_scope(1);
        ENSURE(!mf.check_letter_conflict(ef, dep));
        f.trail.push_scope();
        expr_ref_vector repl(f.m);
        repl.push_back(y);
        mf.apply_subst(x, repl, dm.mk_leaf(4));
        ENSURE(mf.check_letter_conflict(ef, dep));
        ENSURE(dm.contains(dep, 1) && dm.contains(dep, 2) && dm.contains(dep, 4));
        // apply_subst leaves the original membership inactive.
        mf.remove(2);
        ENSURE(!mf.check_letter_conflict(ef, dep));
        f.trail.pop_scope(1);
        ENSURE(!mf.check_letter_conflict(ef, dep));
    }

    static void tst_letter_count_constants() {
        fixture f;
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& dm = f.tree.dep_mgr();
        expr_ref even = count_regex(f, 'a', 2, 0);
        expr_ref odd = count_regex(f, 'a', 2, 1);
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        mf.add(seq::str_mem(f.m, x, seq::view::membership(even, f.m), dm.mk_leaf(1)));
        expr_ref unit(f.u.str.mk_unit(f.u.mk_char('a')), f.m);
        expr_ref rhs(f.u.str.mk_concat(f.u.str.mk_string("aa"), unit), f.m);
        ef.add_equation(x, rhs, dm.mk_leaf(2));
        seq::eq_tree::dep_tracker dep = nullptr;
        ENSURE(mf.check_letter_conflict(ef, dep));
        ENSURE(dm.contains(dep, 1) && dm.contains(dep, 2));
        // Negative equation constants and a closed zero-variable row.
        f.trail.push_scope();
        ef.remove_equation_trailed(0);
        mf.remove(0);
        mf.add(seq::str_mem(f.m, f.u.str.mk_string("aa"), seq::view::membership(odd, f.m), dm.mk_leaf(3)));
        ENSURE(mf.check_letter_conflict(ef, dep) && dm.contains(dep, 3));
        f.trail.pop_scope(1);
    }

    static void tst_letter_count_opaque_tokens() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref y(f.m.mk_fresh_const("y", f.u.str.mk_string_sort()), f.m);
        expr_ref zero(f.a.mk_int(0), f.m);
        expr_ref opaque(f.u.str.mk_at(x, zero), f.m);
        expr_ref symbol(f.m.mk_fresh_const("ch", f.u.mk_char_sort()), f.m);
        expr_ref unit(f.u.str.mk_unit(symbol), f.m);
        expr_ref odd = count_regex(f, 'a', 2, 1);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& dm = f.tree.dep_mgr();
        mf.add(seq::str_mem(f.m, opaque, seq::view::membership(odd, f.m), dm.mk_leaf(1)));
        mf.add(seq::str_mem(f.m, unit, seq::view::membership(odd, f.m), dm.mk_leaf(2)));
        mf.set_witness(opaque, f.u.str.mk_string(""));
        mf.set_witness(unit, f.u.str.mk_string(""));
        seq::eq_tree::dep_tracker dep = nullptr;
        ENSURE(!mf.check_letter_conflict(ef, dep));
        // The shared opaque token has coefficient two across the subject.
        expr_ref doubled(f.u.str.mk_concat(opaque, opaque), f.m);
        expr_ref term(f.u.str.mk_concat(doubled, y), f.m);
        mf.add(seq::str_mem(f.m, term, seq::view::membership(odd, f.m), dm.mk_leaf(3)));
        ENSURE(!mf.check_letter_conflict(ef, dep));
        ef.add_equation(y, unit, dm.mk_leaf(4));
        ENSURE(!mf.check_letter_conflict(ef, dep)); // 2*odd + odd remains odd.
        expr_ref even = count_regex(f, 'a', 2, 0);
        f.trail.push_scope();
        mf.remove(2);
        mf.add(seq::str_mem(f.m, term, seq::view::membership(even, f.m), dm.mk_leaf(5)));
        ENSURE(mf.check_letter_conflict(ef, dep));
        ENSURE(dm.contains(dep, 2) && dm.contains(dep, 4) && dm.contains(dep, 5));
        f.trail.pop_scope(1);
        ENSURE(!mf.check_letter_conflict(ef, dep));
    }

    static void tst_letter_count_fallbacks() {
        fixture f;
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        seq::eq_tree::dep_tracker dep = nullptr;
        expr_ref a(f.u.str.mk_string("a"), f.m);
        sort_ref re_sort(f.u.re.mk_re(a->get_sort()), f.m);
        expr_ref empty(f.u.re.mk_empty(re_sort), f.m);
        expr_ref target(f.u.re.mk_to_re(a), f.m);
        mf.add(seq::str_mem(f.m, a, seq::view::reach(empty, target, f.m)));
        ENSURE(!mf.check_letter_conflict(ef, dep));
        expr_ref unknown(f.m.mk_fresh_const("R", re_sort), f.m);
        mf.add(seq::str_mem(f.m, a, seq::view::membership(unknown, f.m)));
        ENSURE(!mf.check_letter_conflict(ef, dep));
        sort_ref ints(f.u.str.mk_seq(f.a.mk_int()), f.m);
        sort_ref int_re(f.u.re.mk_re(ints), f.m);
        expr_ref i(f.u.str.mk_unit(f.a.mk_int(97)), f.m);
        expr_ref int_empty(f.u.re.mk_empty(int_re), f.m);
        mf.add(seq::str_mem(f.m, i, seq::view::membership(int_empty, f.m)));
        ef.add_equation(i, f.u.str.mk_empty(ints));
        ENSURE(!mf.check_letter_conflict(ef, dep) && !dep);
        expr_ref_vector ts(f.m);
        for (unsigned j = 0; j < 20; ++j)
            ts.push_back(f.m.mk_fresh_const("x", a->get_sort()));
        expr_ref even = count_regex(f, 'a', 2, 0);
        expr_ref odd = count_regex(f, 'a', 2, 1);
        mf.add(seq::str_mem(f.m, ts, seq::view::membership(even, f.m)));
        mf.add(seq::str_mem(f.m, ts, seq::view::membership(odd, f.m)));
        // 2^20 exceeds the assignment budget; decline, not refute.
        ENSURE(!mf.check_letter_conflict(ef, dep) && !dep);
        bool canceled = false;
        {
            scoped_rlimit limit(f.m.limit(), 1);
            try { mf.check_letter_conflict(ef, dep); }
            catch (default_exception const&) { canceled = true; }
        }
        ENSURE(canceled);
    }

    static void tst_letter_count_regex_depth() {
        for (unsigned nesting : {254u, 256u, 16384u}) {
            fixture f;
            auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
            auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
            expr_ref a(f.u.str.mk_string("a"), f.m);
            expr_ref re(f.u.re.mk_empty(f.u.re.mk_re(a->get_sort())), f.m);
            for (unsigned i = 0; i < nesting; ++i)
                re = f.u.re.mk_complement(re);
            ENSURE(get_depth(re) == nesting + 1);
            mf.add(seq::str_mem(f.m, a, seq::view::membership(re, f.m)));
            seq::eq_tree::dep_tracker dep = nullptr;
            // An even number of complements of empty remains empty, but the
            // consumer must decline deep regexes before the recursive abstraction.
            ENSURE(mf.check_letter_conflict(ef, dep) == (nesting == 254));
        }
    }

    static void tst_trivial_sat() {
        fixture f;
        expr_ref word(f.u.str.mk_string(zstring("ab")), f.m);
        expr_ref re(f.u.re.mk_concat(f.u.re.mk_to_re(f.u.str.mk_string(zstring("a"))),
                                      f.u.re.mk_to_re(f.u.str.mk_string(zstring("b")))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, word, seq::view::membership(re, f.m)));
        }) == stx::search_result::sat);
    }

    static void tst_dead_unsat() {
        fixture f;
        expr_ref word(f.u.str.mk_string(zstring("a")), f.m);
        expr_ref re(f.u.re.mk_to_re(f.u.str.mk_string(zstring("a"))), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, word, seq::view::membership(re, f.m)));
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
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, X, seq::view::membership(star_a, f.m)));
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
            root->facet_as<seq::mem_facet>(f.mem_id).add(seq::str_mem(f.m, term, seq::view::membership(re, f.m)));
        }, 16) == stx::search_result::sat);
    }

    static void tst_root_refute_before_equation_substitution() {
        fixture f;
        sort* s = f.u.str.mk_string_sort();
        expr_ref X(f.m.mk_fresh_const("X", s), f.m);
        expr_ref Y(f.m.mk_fresh_const("Y", s), f.m);
        expr_ref A(f.m.mk_fresh_const("A", s), f.m);
        expr_ref B(f.m.mk_fresh_const("B", s), f.m);
        expr_ref term(f.u.str.mk_concat(X, Y), f.m);
        expr_ref a(f.u.str.mk_string(zstring("a")), f.m);
        expr_ref b(f.u.str.mk_string(zstring("b")), f.m);
        expr_ref re_a(f.u.re.mk_to_re(a), f.m);
        expr_ref re_b(f.u.re.mk_to_re(b), f.m);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        ef.add_equation(X, f.u.str.mk_concat(A, B));
        mf.add(seq::str_mem(f.m, term, seq::view::membership(re_a, f.m)));
        mf.add(seq::str_mem(f.m, term, seq::view::membership(re_b, f.m)));

        seq::mem_leaf_split precheck(f.m, f.u, f.rw, f.ac);
        seq::eq_tree::dep_tracker dep = nullptr;
        bool checked = false;
        ENSURE(precheck.root_refute(mf, dep, checked) == l_false);
        ENSURE(checked);
    }

    static unsigned leaf_stat(seq::mem_leaf_split const& leaf, char const* key) {
        statistics st;
        leaf.collect_statistics(st);
        for (unsigned i = 0; i < st.size(); ++i)
            if (std::string(st.get_key(i)) == key)
                return st.get_uint_value(i);
        ENSURE(false);
        return 0;
    }

    static void tst_root_witness_retention(bool disequation) {
        fixture f;
        f.ac.params.m_seq_monadic_leaf = true;
        f.ac.params.m_seq_monadic_leaf_budget = 0;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref y(f.m.mk_fresh_const("y", x->get_sort()), f.m);
        expr_ref z(f.m.mk_fresh_const("z", x->get_sort()), f.m);
        expr_ref term(f.u.str.mk_concat(x, y), f.m);
        expr_ref a(f.u.str.mk_string("a"), f.m), b(f.u.str.mk_string("b"), f.m);
        expr_ref ab(f.u.str.mk_string("ab"), f.m), ba(f.u.str.mk_string("ba"), f.m);
        expr_ref re_a(f.u.re.mk_to_re(a), f.m);
        expr_ref re_ab(f.u.re.mk_to_re(ab), f.m), re_ba(f.u.re.mk_to_re(ba), f.m);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& df = f.root->facet_as<seq::deq_facet>(f.deq_id);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& af = f.root->facet_as<seq::assumption_facet>(f.assumption_id);
        auto& dm = f.tree.dep_mgr();
        seq::mem_leaf_split leaf(f.m, f.u, f.rw, f.ac);
        auto settle = [&]() {
            if (disequation)
                df.remove_disequation_trailed(0);
            else
                ef.remove_equation_trailed(0);
        };
        for (unsigned round = 0; round < 2; ++round) {
            f.trail.push_scope();
            term = f.u.str.mk_concat(x, y);
            seq::str_mem joint(f.m, term, seq::view::membership(re_ab, f.m), dm.mk_leaf(10 * round + 1));
            seq::str_mem single(f.m, x, seq::view::membership(re_a, f.m), dm.mk_leaf(10 * round + 2));
            mf.add(round ? single : joint);
            mf.add(round ? joint : single);
            term = nullptr;
            if (disequation) {
                expr_ref_vector lhs(f.m), rhs(f.m);
                lhs.push_back(x);
                rhs.push_back(z);
                df.add_disequation(lhs, rhs);
            }
            else
                ef.add_equation(x, z);
            seq::eq_tree::dep_tracker dep = nullptr;
            bool checked = false;
            ENSURE(leaf.root_refute(mf, dep, checked) == l_undef && checked);
            ENSURE(dm.contains(dep, 10 * round + 1) && dm.contains(dep, 10 * round + 2));
            ENSURE(leaf_stat(leaf, "seq-mem-leaf num asked") == 1);
            ENSURE(!mf.witness_extracted() && af.assumptions().empty());
            seq::eq_tree::edge out;
            bool has_more = false, committed = false;
            auto pending = leaf.split(*f.root, 0, out, has_more, committed);
            ENSURE(!pending && !committed);
            ENSURE(ef.equations().size() == (disequation ? 0u : 1u));

            f.trail.push_scope();
            settle();
            auto it = leaf.split(*f.root, 0, out, has_more, committed);
            ENSURE(it && committed && has_more);
            ENSURE(leaf_stat(leaf, "seq-mem-leaf num asked") == 1);
            unsigned assignments = 0;
            for (auto const& eq : ef.equations()) {
                if (!eq.active())
                    continue;
                ENSURE(eq.m_lhs.size() == 1);
                expr_ref word(f.u.str.mk_concat(eq.m_rhs.size(), eq.m_rhs.data(), x->get_sort()), f.m);
                th_rewriter normalize(f.m);
                normalize(word);
                ENSURE((eq.m_lhs[0] == x && word == a) || (eq.m_lhs[0] == y && word == b));
                ENSURE(dm.contains(eq.m_dep, 10 * round + 1) && dm.contains(eq.m_dep, 10 * round + 2));
                if (round)
                    ENSURE(!dm.contains(eq.m_dep, 1) && !dm.contains(eq.m_dep, 2));
                ++assignments;
            }
            ENSURE(assignments == 2);
            f.trail.pop_scope(1);
            ENSURE(ef.equations().size() == (disequation ? 0u : 1u));
            ENSURE(disequation ? !df.is_satisfied() : !ef.is_satisfied());

            f.trail.push_scope();
            settle();
            ENSURE(it->next(out));
            auto declined = leaf.split(*f.root, 0, out, has_more, committed);
            ENSURE(!declined && !committed && ef.is_satisfied());
            f.trail.pop_scope(1);
            f.trail.pop_scope(1);
            ENSURE(mf.memberships().empty() && ef.is_satisfied() && df.is_satisfied());
            ENSURE(!mf.witness_extracted() && af.assumptions().empty());
        }
        ENSURE(leaf_stat(leaf, "seq-mem-leaf num committed") == 2);
        ENSURE(leaf_stat(leaf, "seq-mem-leaf num cache hits") >= 3);

        f.trail.push_scope();
        term = f.u.str.mk_concat(x, y);
        mf.add(seq::str_mem(f.m, term, seq::view::membership(re_ba, f.m), dm.mk_leaf(21)));
        mf.add(seq::str_mem(f.m, x, seq::view::membership(re_a, f.m), dm.mk_leaf(22)));
        seq::eq_tree::dep_tracker dep = nullptr;
        bool checked = false;
        ENSURE(leaf.root_refute(mf, dep, checked) == l_false && checked);
        ENSURE(dm.contains(dep, 21) && dm.contains(dep, 22));
        ENSURE(leaf_stat(leaf, "seq-mem-leaf num asked") == 2);
        f.trail.pop_scope(1);
    }

    static void tst_symbolic_unit_derivative_not_rejected() {
        fixture f;
        sort* s = f.u.str.mk_string_sort();
        expr_ref X(f.m.mk_fresh_const("X", s), f.m);
        expr_ref zero(f.a.mk_int(0), f.m);
        expr_ref nth(f.u.str.mk_nth_i(X, zero), f.m);
        expr_ref unit(f.u.str.mk_unit(nth), f.m);
        expr_ref digit(f.u.re.mk_range(f.u.str.mk_string("0"), f.u.str.mk_string("9")), f.m);
        expr_ref digits(f.u.re.mk_plus(digit), f.m);
        ENSURE(solve_mem(f, [&](seq::eq_tree::node* root) {
            root->facet_as<seq::mem_facet>(f.mem_id).add(
                seq::str_mem(f.m, unit, seq::view::membership(digits, f.m)));
        }) == stx::search_result::sat);
    }

    static void tst_symbolic_unit_no_cost_retry() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref y(f.m.mk_fresh_const("y", x->get_sort()), f.m);
        expr_ref zero(f.a.mk_int(0), f.m);
        expr_ref ch(f.u.str.mk_nth_i(x, zero), f.m);
        expr_ref unit(f.u.str.mk_unit(ch), f.m);
        expr_ref str(f.u.str.mk_concat(unit, y), f.m);
        expr_ref a(f.u.str.mk_string("a"), f.m);
        expr_ref re(f.u.re.mk_to_re(a), f.m);
        re = f.u.re.mk_star(re);
        f.root->facet_as<seq::mem_facet>(f.mem_id).add(
            seq::str_mem(f.m, str, seq::view::membership(re, f.m)));
        ENSURE(f.tree.solve() == stx::search_result::unknown);
        ENSURE(f.tree.get_stats().m_split_counts.at("mem-monadic") == 1);
    }

    static void tst_witness_waits_for_word_constraints(bool disequation) {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref y(f.m.mk_fresh_const("y", x->get_sort()), f.m);
        expr_ref a(f.u.str.mk_string("a"), f.m);
        expr_ref re(f.u.re.mk_to_re(a), f.m);
        re = f.u.re.mk_star(re);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& df = f.root->facet_as<seq::deq_facet>(f.deq_id);
        auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
        auto& af = f.root->facet_as<seq::assumption_facet>(f.assumption_id);
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        for (unsigned len : {2u, 3u}) {
            f.trail.push_scope();
            mf.add(seq::str_mem(f.m, x, seq::view::membership(re, f.m)));
            expr_ref length(f.u.str.mk_length(x), f.m);
            expr_ref value(f.a.mk_int(len), f.m);
            sf.add_constraint(f.m.mk_eq(length, value));
            if (disequation) {
                expr_ref_vector lhs(f.m), rhs(f.m);
                lhs.push_back(x);
                rhs.push_back(y);
                df.add_disequation(lhs, rhs);
            }
            else
                ef.add_equation(x, y);
            ENSURE(mf.is_satisfied());
            ENSURE(propagation.propagate(*f.root) != stx::simplify_result::conflict);
            ENSURE(!mf.witness_extracted() && af.assumptions().empty());
            unsigned num_views = mf.vw().size();
            f.trail.push_scope();
            if (disequation)
                df.remove_disequation_trailed(0);
            else
                ef.remove_equation_trailed(0);
            ENSURE(propagation.propagate(*f.root) != stx::simplify_result::conflict);
            ENSURE(mf.witness_extracted() && af.assumptions().size() == 1);
            expr_ref word(f.m);
            ENSURE(mf.get_witness(x, word));
            th_rewriter normalize(f.m);
            normalize(word);
            zstring s;
            ENSURE(f.u.str.is_string(word, s) && s.length() == len);
            for (unsigned i = 0; i < len; ++i)
                ENSURE(s[i] == 'a');
            f.trail.pop_scope(1);
            ENSURE(!mf.witness_extracted() && af.assumptions().empty());
            ENSURE(!mf.get_witness(x, word) && mf.vw().size() == num_views);
            ENSURE(disequation ? !df.is_satisfied() : !ef.is_satisfied());
            ENSURE(propagation.propagate(*f.root) != stx::simplify_result::conflict);
            ENSURE(!mf.witness_extracted() && af.assumptions().empty());
            f.trail.pop_scope(1);
            f.root->clear_status();
            ENSURE(mf.memberships().empty() && mf.qhead() == 0);
            ENSURE(ef.is_satisfied() && df.is_satisfied());
            ENSURE(!sf.has_conflict() && mf.vw().size() == 0);
        }
    }

    static void tst_pending_equation_membership_refutation() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref y(f.m.mk_fresh_const("y", x->get_sort()), f.m);
        expr_ref ab(f.u.str.mk_string("ab"), f.m);
        expr_ref ba(f.u.str.mk_string("ba"), f.m);
        expr_ref r1(f.u.re.mk_to_re(ab), f.m), r2(f.u.re.mk_to_re(ba), f.m);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& ef = f.root->facet_as<seq::eq_facet>(f.eq_id);
        auto& dm = f.tree.dep_mgr();
        ef.add_equation(x, y);
        mf.add(seq::str_mem(f.m, x, seq::view::membership(r1, f.m), dm.mk_leaf(1)));
        mf.add(seq::str_mem(f.m, x, seq::view::membership(r2, f.m), dm.mk_leaf(2)));
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        ENSURE(propagation.propagate(*f.root) == stx::simplify_result::conflict);
        ENSURE(dm.contains(f.root->conflict_dep(), 1) && dm.contains(f.root->conflict_dep(), 2));
        ENSURE(!mf.witness_extracted());
    }

    static void tst_regex_length_refutation(bool concat, bool generic = false) {
        fixture f;
        scoped_rlimit limit(f.m.limit(), 10000);
        sort_ref seq_sort(generic ? f.u.str.mk_seq(f.a.mk_int()) : f.u.str.mk_string_sort(), f.m);
        expr_ref x(f.m.mk_fresh_const("x", seq_sort), f.m);
        expr_ref y(f.m.mk_fresh_const("y", x->get_sort()), f.m);
        expr_ref term(concat ? f.u.str.mk_concat(x, y) : x.get(), f.m);
        expr_ref re(f.m);
        if (generic) {
            sort_ref re_sort(f.u.re.mk_re(seq_sort), f.m);
            expr_ref full_char(f.u.re.mk_full_char(re_sort), f.m);
            re = f.u.re.mk_concat(full_char, full_char);
            re = f.u.re.mk_concat(re, full_char);
        }
        else {
            expr_ref abc(f.u.str.mk_string("abc"), f.m);
            re = f.u.re.mk_to_re(abc);
        }
        re = f.u.re.mk_star(re);
        auto& dm = f.tree.dep_mgr();
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
        mf.add(seq::str_mem(f.m, term, seq::view::membership(re, f.m), dm.mk_leaf(1)));
        expr_ref len_x(f.u.str.mk_length(x), f.m);
        expr_ref bound(f.a.mk_int(concat ? 150000001 : 300000002), f.m);
        sf.add_constraint(f.m.mk_eq(len_x, bound), dm.mk_leaf(2));
        if (concat) {
            expr_ref len_y(f.u.str.mk_length(y), f.m);
            sf.add_constraint(f.m.mk_eq(len_y, bound), dm.mk_leaf(3));
        }
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        ENSURE(propagation.propagate(*f.root) == stx::simplify_result::conflict);
        ENSURE(dm.contains(f.root->conflict_dep(), 1));
        ENSURE(dm.contains(f.root->conflict_dep(), 2));
        ENSURE(!concat || dm.contains(f.root->conflict_dep(), 3));
        ENSURE(!mf.witness_extracted());
    }

    static void tst_regex_length_union() {
        for (unsigned len : {0u, 2u, 3u, 4u, 5u, 6u, 7u}) {
            fixture f;
            expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
            expr_ref aa(f.u.str.mk_string("aa"), f.m);
            expr_ref bbb(f.u.str.mk_string("bbb"), f.m);
            expr_ref r1(f.u.re.mk_to_re(aa), f.m), r2(f.u.re.mk_to_re(bbb), f.m);
            r1 = f.u.re.mk_star(r1);
            r2 = f.u.re.mk_star(r2);
            expr_ref re(f.u.re.mk_union(r1, r2), f.m);
            auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
            auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
            mf.add(seq::str_mem(f.m, x, seq::view::membership(re, f.m)));
            expr_ref length(f.u.str.mk_length(x), f.m);
            expr_ref value(f.a.mk_int(len), f.m);
            sf.add_constraint(f.m.mk_eq(length, value));
            seq::mem_propagation propagation(f.m, f.u, f.rw);
            bool unsat = len == 5 || len == 7;
            ENSURE((propagation.propagate(*f.root) == stx::simplify_result::conflict) == unsat);
            ENSURE(sf.has_conflict() == unsat);
            if (!unsat) {
                expr_ref word(f.m);
                ENSURE(mf.get_witness(x, word));
                th_rewriter normalize(f.m);
                normalize(word);
                zstring s;
                ENSURE(f.u.str.is_string(word, s) && s.length() == len);
            }
        }
    }

    static void tst_regex_length_scopes() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref abc(f.u.str.mk_string("abc"), f.m);
        expr_ref re(f.u.re.mk_to_re(abc), f.m);
        re = f.u.re.mk_star(re);
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
        for (unsigned len : {3u, 2u, 6u}) {
            f.trail.push_scope();
            mf.add(seq::str_mem(f.m, x, seq::view::membership(re, f.m)));
            expr_ref length(f.u.str.mk_length(x), f.m);
            expr_ref value(f.a.mk_int(len), f.m);
            sf.add_constraint(f.m.mk_eq(length, value));
            ENSURE((propagation.propagate(*f.root) == stx::simplify_result::conflict) == (len == 2));
            ENSURE(sf.has_conflict() == (len == 2));
            f.trail.pop_scope(1);
            f.root->clear_status();
            ENSURE(mf.memberships().empty() && mf.qhead() == 0);
            ENSURE(!sf.has_conflict());
        }
    }

    static void tst_regex_length_reach_view() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref abc(f.u.str.mk_string("abc"), f.m);
        expr_ref bc(f.u.str.mk_string("bc"), f.m);
        expr_ref start(f.u.re.mk_to_re(abc), f.m);
        expr_ref target(f.u.re.mk_to_re(bc), f.m);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
        mf.add(seq::str_mem(f.m, x, seq::view::reach(start, target, f.m)));
        expr_ref length(f.u.str.mk_length(x), f.m);
        expr_ref one(f.a.mk_int(1), f.m);
        sf.add_constraint(f.m.mk_eq(length, one));
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        ENSURE(propagation.propagate(*f.root) != stx::simplify_result::conflict);
        ENSURE(!sf.has_conflict());
        expr_ref word(f.m);
        ENSURE(mf.get_witness(x, word));
        th_rewriter normalize(f.m);
        normalize(word);
        zstring s;
        ENSURE(f.u.str.is_string(word, s) && s == zstring("a"));
    }

    static void tst_regex_length_large_loop() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref a(f.u.str.mk_string("a"), f.m);
        expr_ref re(f.u.re.mk_to_re(a), f.m);
        re = f.u.re.mk_loop_proper(re, 0, 0x80000000u);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
        mf.add(seq::str_mem(f.m, x, seq::view::membership(re, f.m)));
        expr_ref length(f.u.str.mk_length(x), f.m);
        expr_ref zero(f.a.mk_int(0), f.m);
        sf.add_constraint(f.m.mk_eq(length, zero));
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        ENSURE(propagation.propagate(*f.root) != stx::simplify_result::conflict);
        ENSURE(!sf.has_conflict());
    }

    static void tst_regex_length_extended() {
        for (unsigned len : {1u, 6u}) {
            fixture f;
            expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
            expr_ref aa(f.u.str.mk_string("aa"), f.m);
            expr_ref aaa(f.u.str.mk_string("aaa"), f.m);
            expr_ref r1(f.u.re.mk_to_re(aa), f.m), r2(f.u.re.mk_to_re(aaa), f.m);
            r1 = f.u.re.mk_star(r1);
            r2 = f.u.re.mk_star(r2);
            expr_ref re(f.u.re.mk_inter(r1, r2), f.m);
            re = f.u.re.mk_concat(r1, re);
            auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
            auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
            mf.add(seq::str_mem(f.m, x, seq::view::membership(re, f.m)));
            expr_ref length(f.u.str.mk_length(x), f.m);
            expr_ref value(f.a.mk_int(len), f.m);
            sf.add_constraint(f.m.mk_eq(length, value));
            seq::mem_propagation propagation(f.m, f.u, f.rw);
            ENSURE((propagation.propagate(*f.root) == stx::simplify_result::conflict) == (len == 1));
            ENSURE(!sf.has_conflict());
            if (len == 6)
                ENSURE(mf.witness_extracted());
        }
    }

    static void tst_regex_length_equivalent_keys() {
        fixture f;
        expr_ref x(f.m.mk_fresh_const("x", f.u.str.mk_string_sort()), f.m);
        expr_ref aa(f.u.str.mk_string("aa"), f.m);
        expr_ref re(f.u.re.mk_to_re(aa), f.m);
        re = f.u.re.mk_star(re);
        expr_ref duplicate(f.u.re.mk_union(re, re), f.m);
        auto& mf = f.root->facet_as<seq::mem_facet>(f.mem_id);
        auto& sf = f.root->facet_as<seq::solver_facet>(f.arith_id);
        mf.add(seq::str_mem(f.m, x, seq::view::membership(re, f.m)));
        mf.add(seq::str_mem(f.m, x, seq::view::membership(duplicate, f.m)));
        expr_ref length(f.u.str.mk_length(x), f.m);
        expr_ref four(f.a.mk_int(4), f.m);
        sf.add_constraint(f.m.mk_eq(length, four));
        seq::mem_propagation propagation(f.m, f.u, f.rw);
        ENSURE(propagation.propagate(*f.root) != stx::simplify_result::conflict);
        ENSURE(!sf.has_conflict());
    }

    // power_peel_mem should first try the `n = 0` branch, then peel one
    // copy for the `n >= 1` branch. This test drives the split iterator
    // directly to inspect both rewrites.
    static void tst_power_peel_mem_split() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref one_a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);
        expr_ref re(u.re.mk_star(u.re.mk_to_re(one_a)), m);
        seq_rewriter rw(m);

        // n = 0 branch: split() commits it immediately.
        {
        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id pow_id = tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr());
        stx::facet_id mem_id = tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac);
        stx::facet_id assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        ac.set_arith_id(arith_id);
        ac.set_pow_id(pow_id);
        ac.set_mem_id(mem_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);
        expr_ref N(m.mk_fresh_const("N", a.mk_int()), m);
        expr_ref pow(u.str.mk_power(one_a, N), m);
        expr_ref term(u.str.mk_concat(pow, b), m);
        root->facet_as<seq::power_facet>(pow_id).add_power(pow, one_a, N);
        root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(m, term, seq::view::membership(re, m)));

        tree.trail().push_scope();
        seq::eq_tree::edge out;
        bool has_more = false, committed = false;
        seq::power_peel_mem pvpm(m, u, a);
        auto it = pvpm.split(*root, 0, out, has_more, committed);
        ENSURE(committed && has_more && it.get() != nullptr);

        auto& mf = root->facet_as<seq::mem_facet>(mem_id);
        expr_ref_vector const& ts = only_active_membership(mf).m_str;
        expr_ref_vector expect(m);
        u.str.get_concat_units(b.get(), expect);
        ENSURE(ts.size() == expect.size());
        for (unsigned i = 0; i < ts.size(); ++i)
            ENSURE(ts.get(i) == expect.get(i)); // pow spliced out, only "b" left
        auto& pf = root->facet_as<seq::power_facet>(pow_id);
        ENSURE(std::all_of(pf.powers().begin(), pf.powers().end(), [](seq::str_power const& p) { return !p.active(); })); // obligation discharged for n=0 branch
        }

        // n >= 1 branch: from a fresh setup, drive split() (which
        // commits branch 1) then iterator::next() (branch 2), and check
        // branch 2's own splice result independently.
        {
        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id pow_id = tree.register_facet<seq::power_facet>(*root, m, u, a, tree.dep_mgr());
        stx::facet_id mem_id = tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac);
        stx::facet_id assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        ac.set_arith_id(arith_id);
        ac.set_pow_id(pow_id);
        ac.set_mem_id(mem_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);
        expr_ref N(m.mk_fresh_const("N", a.mk_int()), m);
        expr_ref pow(u.str.mk_power(one_a, N), m);
        expr_ref term(u.str.mk_concat(pow, b), m);
        root->facet_as<seq::power_facet>(pow_id).add_power(pow, one_a, N);
        root->facet_as<seq::mem_facet>(mem_id).add(seq::str_mem(m, term, seq::view::membership(re, m)));

        tree.trail().push_scope();
        seq::eq_tree::edge out;
        bool has_more = false, committed = false;
        seq::power_peel_mem pvpm(m, u, a);
        auto it = pvpm.split(*root, 0, out, has_more, committed);
        ENSURE(committed && it.get() != nullptr);
        tree.trail().pop_scope(1);
        root->pop_facets();

        // Restore the original obligation, then drive the iterator's
        // second branch independently.
        tree.trail().push_scope();
        root->facet_as<seq::power_facet>(pow_id).add_power(pow, one_a, N);
        seq::eq_tree::edge out2;
        ENSURE(it->next(out2));

        auto& mf = root->facet_as<seq::mem_facet>(mem_id);
        expr_ref_vector const& ts = only_active_membership(mf).m_str;
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
    tst_letter_count_benchmark(false);
    tst_letter_count_benchmark(true);
    tst_letter_count_equations_scopes();
    tst_letter_count_constants();
    tst_letter_count_opaque_tokens();
    tst_letter_count_fallbacks();
    tst_letter_count_regex_depth();
    tst_trivial_sat();
    tst_dead_unsat();
    tst_single_var_sat();
    tst_two_var_monadic_sat();
    tst_root_refute_before_equation_substitution();
    tst_root_witness_retention(false);
    tst_root_witness_retention(true);
    tst_symbolic_unit_derivative_not_rejected();
    tst_symbolic_unit_no_cost_retry();
    tst_witness_waits_for_word_constraints(false);
    tst_witness_waits_for_word_constraints(true);
    tst_pending_equation_membership_refutation();
    tst_regex_length_refutation(false);
    tst_regex_length_refutation(true);
    tst_regex_length_refutation(false, true);
    tst_regex_length_union();
    tst_regex_length_scopes();
    tst_regex_length_reach_view();
    tst_regex_length_large_loop();
    tst_regex_length_extended();
    tst_regex_length_equivalent_keys();
    tst_power_peel_mem_split();
    std::cout << "seq_mem_facet: all tests passed\n";
}

/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_ncontains_facet.cpp (test)

Abstract:

    Unit test for `seq::ncontains_facet` / `seq::ncontains_propagation` /
    `seq::ncontains_split` (ast/seq/seq_ncontains_facet.h): the
    negative str.contains facet, combined with `eq_facet`/`solver_facet`.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_ncontains_facet.h"
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_stoi_facet.h"
#include "ast/seq/seq_skolem.h"
#include "ast/rewriter/th_rewriter.h"
#include "smt/smt_solver.h"
#include "smt/seq_solver_facet.h"
#include "solver/solver.h"
#include <iostream>

namespace {

    static void tst_ncontains_fixed_length_choices() {
        ast_manager m;
        reg_decl_plugins(m);
        scoped_rlimit limit(m.limit(), 5000000);
        seq_util u(m);
        arith_util a(m);
        expr_ref haystack(m.mk_const("haystack", u.str.mk_string_sort()), m);
        expr_ref x(m.mk_const("x", u.str.mk_string_sort()), m);
        expr_ref y(m.mk_const("y", u.str.mk_string_sort()), m);
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
        s->assert_expr(u.str.mk_contains(haystack, x));
        s->assert_expr(u.str.mk_contains(haystack, y));
        s->assert_expr(m.mk_not(u.str.mk_contains(x, y)));
        s->assert_expr(m.mk_not(u.str.mk_contains(y, x)));
        ENSURE(s->check_sat(0, nullptr) == l_true);
        s->push();
        s->assert_expr(m.mk_eq(x, y));
        ENSURE(s->check_sat(0, nullptr) == l_false);
        s->pop(1);
        ENSURE(s->check_sat(0, nullptr) == l_true);
        s->push();
        expr_ref len_x(u.str.mk_length(x), m);
        expr_ref len_y(u.str.mk_length(y), m);
        s->assert_expr(m.mk_eq(len_x, a.mk_int(3)));
        s->assert_expr(m.mk_eq(len_y, a.mk_int(2)));
        ENSURE(s->check_sat(0, nullptr) == l_true);
        s->pop(1);
        ENSURE(s->check_sat(0, nullptr) == l_true);
    }

    static void tst_ncontains_unit_tail_preimage_scope() {
        for (unsigned code : {45u, 0x1f600u}) {
            ast_manager m;
            reg_decl_plugins(m);
            scoped_rlimit limit(m.limit(), 5000000);
            seq_util u(m);
            arith_util a(m);
            th_rewriter rw(m);
            expr_ref source(m.mk_const("source", u.str.mk_string_sort()), m);
            expr_ref character(u.str.mk_char(code), m);
            expr_ref needle(u.str.mk_unit(character), m);
            rw(needle);
            expr_ref letter(u.str.mk_string("a"), m);
            expr_ref length(u.str.mk_length(source), m);
            expr_ref one(a.mk_int(1), m);
            expr_ref tail(u.str.mk_substr(source, one, length), m);
            params_ref p;
            p.set_sym("string_solver", symbol("nseq"));
            ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
            s->push();
            s->assert_expr(m.mk_not(u.str.mk_contains(tail, needle)));
            ENSURE(s->check_sat(0, nullptr) == l_true);
            expr_ref_vector words(m);
            words.push_back(u.str.mk_empty(source->get_sort()));
            words.push_back(needle);
            words.push_back(letter);
            words.push_back(u.str.mk_concat(needle, letter));
            words.push_back(u.str.mk_concat(letter, needle));
            words.push_back(u.str.mk_concat(needle, needle));
            bool expected[] = {true, true, true, true, false, false};
            for (unsigned j = 0; j < words.size(); ++j) {
                s->push();
                s->assert_expr(m.mk_eq(source, words.get(j)));
                ENSURE(s->check_sat(0, nullptr) == (expected[j] ? l_true : l_false));
                s->pop(1);
            }
            s->push();
            expr_ref ten(a.mk_int(10), m);
            expr_ref later(u.str.mk_substr(source, ten, length), m);
            s->assert_expr(u.str.mk_contains(later, needle));
            ENSURE(s->check_sat(0, nullptr) == l_false);
            s->pop(2);
            s->push();
            s->assert_expr(m.mk_eq(source, words.get(4)));
            ENSURE(s->check_sat(0, nullptr) == l_true);
            s->pop(1);
            s->push();
            expr_ref partial(u.str.mk_substr(source, one, one), m);
            expr_ref pair(u.str.mk_concat(letter, letter), m);
            expr_ref word(u.str.mk_concat(pair, needle), m);
            s->assert_expr(m.mk_not(u.str.mk_contains(partial, needle)));
            s->assert_expr(m.mk_eq(source, word));
            ENSURE(s->check_sat(0, nullptr) == l_true);
            s->pop(1);
        }
    }

    static void tst_ncontains_replace_witness_scope() {
        for (unsigned mode = 0; mode < 4; ++mode) {
            bool fixed_pattern = mode % 2 != 0;
            ast_manager m;
            reg_decl_plugins(m);
            scoped_rlimit limit(m.limit(), 5000000);
            seq_util u(m);
            arith_util a(m);
            expr_ref source(m.mk_const("source", u.str.mk_string_sort()), m);
            expr_ref literal(u.str.mk_string("aba"), m);
            expr_ref pattern(m);
            if (fixed_pattern)
                pattern = literal;
            else
                pattern = m.mk_const("pattern", source->get_sort());
            expr_ref empty(u.str.mk_empty(source->get_sort()), m);
            expr_ref replaced(u.str.mk_replace(source, pattern, empty), m);
            expr_ref source_length(u.str.mk_length(source), m);
            expr_ref pattern_length(u.str.mk_length(pattern), m);
            expr_ref result_length(u.str.mk_length(replaced), m);
            params_ref p;
            p.set_sym("string_solver", symbol("nseq"));
            ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
            if (mode >= 2) {
                expr_ref parsed(u.str.mk_stoi(replaced), m);
                s->assert_expr(a.mk_le(parsed, a.mk_int(0)));
            }
            s->push();
            s->assert_expr(a.mk_ge(source_length, a.mk_int(4)));
            s->assert_expr(a.mk_gt(pattern_length, a.mk_int(0)));
            s->assert_expr(a.mk_le(result_length, a.mk_int(2)));
            ENSURE(s->check_sat(0, nullptr) == l_true);
            s->push();
            expr_ref word(u.str.mk_string("ababa"), m);
            s->assert_expr(m.mk_eq(source, word));
            if (!fixed_pattern)
                s->assert_expr(m.mk_eq(pattern, literal));
            ENSURE(s->check_sat(0, nullptr) == l_true);
            s->push();
            expr_ref expected(u.str.mk_string("ba"), m);
            s->assert_expr(m.mk_not(m.mk_eq(replaced, expected)));
            ENSURE(s->check_sat(0, nullptr) == l_false);
            s->pop(1);
            ENSURE(s->check_sat(0, nullptr) == l_true);
            s->pop(2);
            s->push();
            s->assert_expr(m.mk_eq(source, empty));
            if (!fixed_pattern)
                s->assert_expr(m.mk_eq(pattern, empty));
            s->assert_expr(m.mk_eq(replaced, empty));
            ENSURE(s->check_sat(0, nullptr) == l_true);
            s->pop(1);
        }
    }

    static void tst_ncontains_self_replace_witness_scope() {
        for (unsigned code : {65u, 66u, 0x1f600u}) {
            ast_manager m;
            reg_decl_plugins(m);
            scoped_rlimit limit(m.limit(), 5000000);
            seq_util u(m);
            th_rewriter rw(m);
            expr_ref source(m.mk_const("source", u.str.mk_string_sort()), m);
            expr_ref pattern(m.mk_const("pattern", source->get_sort()), m);
            expr_ref empty(u.str.mk_empty(source->get_sort()), m);
            expr_ref character(u.str.mk_char(code), m);
            expr_ref literal(u.str.mk_unit(character), m);
            rw(literal);
            expr_ref self(u.str.mk_replace(source, pattern, source), m);
            expr_ref left(u.str.mk_replace(self, pattern, literal), m);
            expr_ref inner(u.str.mk_replace(source, pattern, literal), m);
            expr_ref right(u.str.mk_replace(source, pattern, inner), m);
            expr_ref same(m.mk_eq(left, right), m);
            params_ref p;
            p.set_sym("string_solver", symbol("nseq"));
            ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
            auto check = [&](lbool expected, char const* phase) {
                lbool actual = s->check_sat(0, nullptr);
                if (actual != expected)
                    std::cerr << "self-replace " << code << " " << phase << ": " << actual << std::endl;
                ENSURE(actual == expected);
            };
            s->assert_expr(m.mk_not(same));
            s->push();
            expr_ref word(u.str.mk_string("abba"), m);
            expr_ref needle(u.str.mk_string("ba"), m);
            s->assert_expr(m.mk_eq(source, word));
            s->assert_expr(m.mk_eq(pattern, needle));
            check(l_true, "fixed counterexample");
            s->pop(1);
            s->push();
            expr_ref letter(u.str.mk_string("a"), m);
            s->assert_expr(m.mk_eq(source, letter));
            s->assert_expr(m.mk_eq(pattern, empty));
            check(l_false, "empty needle");
            s->pop(1);
            s->assert_expr(m.mk_eq(source, word));
            s->assert_expr(m.mk_eq(pattern, needle));
            check(l_true, "rollback fixed counterexample");
        }
    }

    static void tst_ncontains_reverse_stoi_alphabet_scope() {
        for (unsigned first : {0u, 2u}) {
            for (unsigned count : {1u, 4u, 5u}) {
                ast_manager m;
                reg_decl_plugins(m);
                scoped_rlimit limit(m.limit(), 5000000);
                seq_util u(m);
                arith_util a(m);
                th_rewriter rw(m);
                expr_ref source(m.mk_const("source", u.str.mk_string_sort()), m);
                expr_ref length(u.str.mk_length(source), m);
                expr_ref bound(a.mk_int(5), m);
                params_ref p;
                p.set_sym("string_solver", symbol("nseq"));
                ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
                s->assert_expr(a.mk_le(length, bound));
                for (unsigned i = 1; i <= count; ++i) {
                    expr_ref offset(a.mk_int(i), m);
                    expr_ref index(a.mk_sub(length, offset), m);
                    rw(index);
                    expr_ref digit(u.str.mk_at(source, index), m);
                    expr_ref value(u.str.mk_stoi(digit), m);
                    expr_ref numeral(a.mk_int(first + (i - 1) % 2), m);
                    s->assert_expr(m.mk_eq(value, numeral));
                }
                expr_ref lo(u.str.mk_string(first == 0 ? "0" : "2"), m);
                expr_ref hi(u.str.mk_string(first == 0 ? "1" : "3"), m);
                expr_ref range(u.re.mk_range(lo, hi), m);
                expr_ref digits(u.re.mk_plus(range), m);
                expr_ref member(u.re.mk_in_re(source, digits), m);
                expr_ref word(u.str.mk_string(first == 0 ? "01010" : "23232"), m);
                expr_ref wrong(u.str.mk_string(first == 0 ? "01011" : "23233"), m);
                expr_ref empty(u.str.mk_empty(source->get_sort()), m);
                s->push();
                s->assert_expr(member);
                ENSURE(s->check_sat(0, nullptr) == l_true);
                s->push();
                s->assert_expr(m.mk_eq(source, word));
                ENSURE(s->check_sat(0, nullptr) == l_true);
                s->pop(1);
                s->push();
                s->assert_expr(m.mk_eq(source, wrong));
                ENSURE(s->check_sat(0, nullptr) == l_false);
                s->pop(1);
                s->push();
                s->assert_expr(m.mk_eq(source, empty));
                ENSURE(s->check_sat(0, nullptr) == l_false);
                s->pop(2);
                s->push();
                s->assert_expr(m.mk_not(member));
                s->assert_expr(m.mk_eq(source, word));
                ENSURE(s->check_sat(0, nullptr) == l_false);
                s->pop(1);
                s->assert_expr(member);
                s->assert_expr(m.mk_eq(source, word));
                ENSURE(s->check_sat(0, nullptr) == l_true);
            }
        }
    }

    class counted_sub_solver : public seq::sub_solver {
    public:
        using seq::sub_solver::sub_solver;
        unsigned m_num_pushes = 0;
        void push() override {
            ++m_num_pushes;
            seq::sub_solver::push();
        }
    };

    class controlled_ambient_context : public seq::null_ambient_context<seq::eq_tree::dep_tracker> {
    public:
        using seq::null_ambient_context<seq::eq_tree::dep_tracker>::null_ambient_context;
        expr* m_false = nullptr;
        seq::eq_tree::dep_tracker m_false_dep = nullptr;
        seq::eq_tree::dep_tracker literal_if_false(expr* e) override {
            return e == m_false ? m_false_dep : nullptr;
        }
    };

    struct fixture {
        ast_manager      m;
        seq_util         u;
        arith_util       a;
        sort*            s;
        trail_stack      trail;
        seq::eq_tree     tree;
        seq::eq_tree::node* root;
        counted_sub_solver solver;
        seq_rewriter     rw;
        controlled_ambient_context ac;
        stx::facet_id    eq_id;
        stx::facet_id    deq_id;
        stx::facet_id    arith_id;
        stx::facet_id    nc_id;
        stx::facet_id    mem_id;
        stx::facet_id    assumption_id;
        stx::facet_id    stoi_id;

        static ast_manager& init_plugins(ast_manager& m) { reg_decl_plugins(m); return m; }

        fixture() :
            u((init_plugins(m), m)), a(m), s(u.str.mk_string_sort()),
            tree(trail, m.limit()),
            root(tree.mk_root()),
            solver(m, a, tree.dep_mgr()),
            rw(m), ac(m, u, trail),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            deq_id(tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr())),
            arith_id(tree.register_facet<seq::solver_facet>(*root, m, u, solver)),
            nc_id(tree.register_facet<seq::ncontains_facet>(*root, m, u, tree.dep_mgr())),
            mem_id(tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac)),
            assumption_id(tree.register_facet<seq::assumption_facet>(*root, m)),
            stoi_id(tree.register_facet<seq::stoi_facet>(*root, m, u, a))
        {
            ac.set_eq_id(eq_id);
            ac.set_deq_id(deq_id);
            ac.set_arith_id(arith_id);
            ac.set_ncontains_id(nc_id);
            ac.set_mem_id(mem_id);
            ac.set_assumption_id(assumption_id);
            ac.set_stoi_id(stoi_id);
            tree.set_ambient_context(&ac);
            tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
            tree.add_propagation_plugin(alloc(seq::ncontains_propagation, m, u, a));
            tree.add_propagation_plugin(alloc(seq::mem_propagation, m, u, rw));
            tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
            tree.set_max_search_depth(12);
        }
    };

    static void tst_ncontains_symbolic_unit_clauses() {
        for (unsigned pos : { 0u, 1u }) {
            fixture fx;
            expr_ref_vector chars(fx.m), units(fx.m);
            for (unsigned i = 0; i < 5; ++i) {
                chars.push_back(fx.m.mk_fresh_const("c", fx.u.mk_char_sort()));
                units.push_back(fx.u.str.mk_unit(chars.back()));
            }
            expr_ref h(fx.u.str.mk_concat(3, units.data(), fx.s), fx.m);
            expr_ref needle(fx.u.str.mk_concat(2, units.data() + 3, fx.s), fx.m);
            auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
            auto& sf = fx.root->facet_as<seq::solver_facet>(fx.arith_id);
            auto& af = fx.root->facet_as<seq::assumption_facet>(fx.assumption_id);
            auto& dm = fx.tree.dep_mgr();
            if (pos == 1) {
                expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
                expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
                fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(x, y);
            }
            nf.add_ncontains(h, needle, dm.mk_leaf(8));
            fx.trail.push_scope();
            seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
            ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::satisfied);
            ENSURE(nf.is_satisfied() && af.assumptions().size() == 2);
            fx.trail.push_scope();
            for (unsigned i = 0; i < 2; ++i) {
                expr_ref equal(fx.m.mk_eq(chars.get(3 + i), chars.get(pos + i)), fx.m);
                sf.add_constraint(equal, dm.mk_leaf(9));
            }
            ENSURE(sf.has_conflict());
            ENSURE(dm.contains(sf.conflict_dep(), 8) && dm.contains(sf.conflict_dep(), 9));
            fx.trail.pop_scope(1);
            ENSURE(!sf.has_conflict());
            unsigned values[] = { 97, 98, 99, 97, 99 };
            for (unsigned i = 0; i < 5; ++i) {
                expr_ref value(fx.u.str.mk_char(values[i]), fx.m);
                expr_ref equal(fx.m.mk_eq(chars.get(i), value), fx.m);
                sf.add_constraint(equal);
            }
            ENSURE(!sf.has_conflict());
            fx.trail.pop_scope(1);
            ENSURE(!nf.is_satisfied() && af.assumptions().empty() && !sf.has_conflict());
            ENSURE(fx.solver.get_scope_level() == 0);
        }
    }

    static void tst_ncontains_symbolic_unit_false_clause() {
        fixture fx;
        expr_ref_vector chars(fx.m), units(fx.m), different(fx.m);
        for (unsigned i = 0; i < 4; ++i) {
            chars.push_back(fx.m.mk_fresh_const("c", fx.u.mk_char_sort()));
            units.push_back(fx.u.str.mk_unit(chars.back()));
        }
        expr_ref h(fx.u.str.mk_concat(2, units.data(), fx.s), fx.m);
        expr_ref needle(fx.u.str.mk_concat(2, units.data() + 2, fx.s), fx.m);
        for (unsigned i = 0; i < 2; ++i)
            different.push_back(fx.m.mk_not(fx.m.mk_eq(chars.get(i), chars.get(i + 2))));
        expr_ref clause(fx.m.mk_or(different.size(), different.data()), fx.m);
        auto& dm = fx.tree.dep_mgr();
        fx.ac.m_false = clause;
        fx.ac.m_false_dep = dm.mk_leaf(9);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, needle, dm.mk_leaf(8));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::conflict);
        ENSURE(dm.contains(fx.root->conflict_dep(), 8) && dm.contains(fx.root->conflict_dep(), 9));
        ENSURE(fx.root->facet_as<seq::assumption_facet>(fx.assumption_id).assumptions().empty());
    }

    static void tst_ncontains_large_symbolic_units_deferred() {
        fixture fx;
        expr_ref c(fx.m.mk_fresh_const("c", fx.u.mk_char_sort()), fx.m);
        expr_ref d(fx.m.mk_fresh_const("d", fx.u.mk_char_sort()), fx.m);
        expr_ref uc(fx.u.str.mk_unit(c), fx.m), ud(fx.u.str.mk_unit(d), fx.m);
        expr_ref_vector h(fx.m), needle(fx.m);
        for (unsigned i = 0; i < 80; ++i)
            h.push_back(uc);
        for (unsigned i = 0; i < 40; ++i)
            needle.push_back(ud);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& af = fx.root->facet_as<seq::assumption_facet>(fx.assumption_id);
        nf.add_ncontains(h, needle);
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        propagation.propagate(*fx.root);
        ENSURE(!nf.is_satisfied() && af.assumptions().empty());
    }

    static void tst_ncontains_symbolic_needle_nonempty(bool int_sequence) {
        fixture fx;
        sort_ref s(int_sequence ? fx.u.str.mk_seq(fx.a.mk_int()) : fx.s, fx.m);
        expr_ref h(fx.m.mk_fresh_const("haystack", s), fx.m);
        expr_ref needle(fx.m.mk_fresh_const("needle", s), fx.m);
        expr_ref length(fx.u.str.mk_length(needle), fx.m);
        expr_ref empty_length(fx.m.mk_eq(length, fx.a.mk_int(0)), fx.m);
        auto& sf = fx.root->facet_as<seq::solver_facet>(fx.arith_id);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& dm = fx.tree.dep_mgr();
        nf.add_ncontains(h, needle, dm.mk_leaf(8));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        fx.trail.push_scope();
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::proceed);
        fx.trail.push_scope();
        sf.add_constraint(empty_length, dm.mk_leaf(9));
        ENSURE(sf.has_conflict());
        ENSURE(dm.contains(sf.conflict_dep(), 8) && dm.contains(sf.conflict_dep(), 9));
        fx.trail.pop_scope(1);
        ENSURE(!sf.has_conflict());
        fx.trail.pop_scope(1);
        sf.add_constraint(empty_length);
        ENSURE(!sf.has_conflict() && fx.solver.get_scope_level() == 0);
    }

    static void tst_ncontains_unit_length_bound() {
        fixture fx;
        auto& sf = fx.root->facet_as<seq::solver_facet>(fx.arith_id);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        expr_ref c(fx.m.mk_fresh_const("c", fx.u.mk_char_sort()), fx.m);
        expr_ref d(fx.m.mk_fresh_const("d", fx.u.mk_char_sort()), fx.m);
        expr_ref tail(fx.m.mk_fresh_const("tail", fx.s), fx.m);
        expr_ref uc(fx.u.str.mk_unit(c), fx.m);
        expr_ref ud(fx.u.str.mk_unit(d), fx.m);
        expr_ref prefix(fx.u.str.mk_concat(ud, tail), fx.m);
        expr_ref h(fx.u.str.mk_concat(prefix, ud), fx.m);
        expr_ref fixed_needle(fx.u.str.mk_concat(uc, uc), fx.m);
        expr_ref needle(fx.m.mk_fresh_const("needle", fx.s), fx.m);
        expr_ref lh(fx.u.str.mk_length(h), fx.m);
        expr_ref ln(fx.u.str.mk_length(needle), fx.m);
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);

        fx.trail.push_scope();
        nf.add_ncontains(h, fixed_needle);
        unsigned pushes = fx.solver.m_num_pushes;
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(fx.solver.m_num_pushes == pushes);
        ENSURE(!nf.is_satisfied());
        fx.trail.pop_scope(1);
        ENSURE(nf.is_satisfied());

        fx.trail.push_scope();
        nf.add_ncontains(h, needle);
        sf.add_constraint(fx.m.mk_eq(lh, fx.a.mk_int(2)));
        sf.add_constraint(fx.m.mk_eq(ln, fx.a.mk_int(3)));
        pushes = fx.solver.m_num_pushes;
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(fx.solver.m_num_pushes == pushes + 1);
        ENSURE(nf.is_satisfied());
        fx.trail.pop_scope(1);

        fx.trail.push_scope();
        nf.add_ncontains(prefix, fixed_needle);
        sf.add_constraint(fx.m.mk_eq(fx.u.str.mk_length(tail), fx.a.mk_int(0)));
        pushes = fx.solver.m_num_pushes;
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(fx.solver.m_num_pushes == pushes + 1);
        ENSURE(nf.is_satisfied());
        fx.trail.pop_scope(1);
        ENSURE(fx.solver.get_scope_level() == 0);
    }

    // `len(h) < len(n)` is asserted directly: `not contains("a","ab")`
    // must be vacuously satisfied by the length-gate propagation alone
    // (no split needed).
    static void tst_ncontains_length_gate_discharges() {
        fixture fx;
        expr_ref h(fx.u.str.mk_string(zstring("a")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("ab")), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, n);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // `not contains(h, "")` (empty needle) is always false - the empty
    // string is contained in everything - so this must be unsat.
    static void tst_ncontains_empty_needle_conflict() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref empty(fx.u.str.mk_empty(fx.s), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(X, empty);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // Ground negative containment with no matching position should be sat.
    static void tst_ncontains_ground_no_occurrence_sat() {
        fixture fx;
        expr_ref h(fx.u.str.mk_string(zstring("abc")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("d")), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, n);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
    }

    // Ground/ground case where the needle DOES occur as a genuine infix:
    // `not contains("abc", "b")` must be unsat - the deterministic
    // prefix-unrolling propagation must find the alignment (at position
    // 1) and report a conflict.
    static void tst_ncontains_ground_occurrence_unsat() {
        fixture fx;
        expr_ref h(fx.u.str.mk_string(zstring("abc")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("b")), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, n);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // After solving `X = "b"`, the substitution must be reflected in
    // `not contains(X, "b")`, yielding a conflict.
    static void tst_ncontains_resolved_by_substitution_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref b(fx.u.str.mk_string(zstring("b")), fx.m);
        expr_ref n(fx.u.str.mk_string(zstring("b")), fx.m);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, b);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(X, n);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // A definite match at a later position should still make
    // `not contains(X ++ "b", "b")` unsat.
    static void tst_ncontains_match_not_at_first_position_unsat() {
        fixture fx;
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref b(fx.u.str.mk_string(zstring("b")), fx.m);
        expr_ref h(fx.u.str.mk_concat(X, b), fx.m);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(h, b);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    // An indexof-style guarded equation can contain self-referential
    // skolems, so equation propagation cannot substitute X. The exposed
    // literal still directly contradicts not-contains(X, "=").
    static void tst_ncontains_conflicts_with_cyclic_equation() {
        fixture fx;
        th_rewriter rw(fx.m);
        seq::skolem sk(fx.m, rw);
        expr_ref X(fx.m.mk_fresh_const("X", fx.s), fx.m);
        expr_ref eq(fx.u.str.mk_string(zstring("=")), fx.m);
        expr_ref lhs(sk.mk_indexof_left(X, eq), fx.m);
        expr_ref rhs(sk.mk_indexof_right(X, eq), fx.m);
        expr_ref decomposition(fx.u.str.mk_concat(lhs, eq, rhs), fx.m);
        fx.root->facet_as<seq::eq_facet>(fx.eq_id).add_equation(X, decomposition);
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(X, eq);
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
    }

    static void tst_ncontains_joint_witness() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        expr_ref bc(fx.u.str.mk_string("bc"), fx.m);
        expr_ref a(fx.u.str.mk_string("a"), fx.m);
        expr_ref first(fx.u.re.mk_to_re(ab), fx.m);
        expr_ref second(fx.u.re.mk_to_re(bc), fx.m);
        expr_ref language(fx.u.re.mk_union(first, second), fx.m);
        fx.root->facet_as<seq::mem_facet>(fx.mem_id).add(
            seq::str_mem(fx.m, x, seq::view::membership(language, fx.m)));
        fx.root->facet_as<seq::ncontains_facet>(fx.nc_id).add_ncontains(x, a);
        ENSURE(fx.tree.solve() == stx::search_result::sat);
        auto* snapshot = fx.tree.sat_snapshot();
        ENSURE(snapshot);
        expr_ref word(fx.m);
        ENSURE(snapshot->facet_as<seq::mem_facet>(fx.mem_id).get_witness(x, word));
        th_rewriter normalize(fx.m);
        normalize(word);
        ENSURE(word == bc);
    }

    static void tst_ncontains_cross_boundary_conflict() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
        expr_ref h(fx.u.str.mk_concat(x, y), fx.m);
        expr_ref a(fx.u.str.mk_string("a"), fx.m);
        expr_ref b(fx.u.str.mk_string("b"), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& ef = fx.root->facet_as<seq::eq_facet>(fx.eq_id);
        nf.add_ncontains(h, ab, fx.tree.dep_mgr().mk_leaf(1));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(nf.is_satisfied());
        ef.add_equation(x, a, fx.tree.dep_mgr().mk_leaf(2));
        ef.add_equation(y, b, fx.tree.dep_mgr().mk_leaf(3));
        ENSURE(fx.tree.solve() == stx::search_result::unsat);
        auto& dm = fx.tree.dep_mgr();
        ENSURE(dm.contains(fx.root->conflict_dep(), 1));
        ENSURE(dm.contains(fx.root->conflict_dep(), 2));
        ENSURE(dm.contains(fx.root->conflict_dep(), 3));
    }

    static void tst_ncontains_substitution_scope() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref needle(fx.m.mk_fresh_const("needle", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
        auto& dm = fx.tree.dep_mgr();
        nf.add_ncontains(x, needle, dm.mk_leaf(4));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(!nf.is_satisfied() && mf.memberships().empty());
        fx.trail.push_scope();
        expr_ref_vector tokens(fx.m);
        fx.u.str.get_concat_units(ab, tokens);
        nf.apply_subst(needle, tokens, dm.mk_leaf(5));
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(nf.is_satisfied() && mf.memberships().size() == 1);
        ENSURE(dm.contains(mf.memberships()[0].m_dep, 4));
        ENSURE(dm.contains(mf.memberships()[0].m_dep, 5));
        fx.trail.pop_scope(1);
        ENSURE(!nf.is_satisfied() && mf.memberships().empty());
        ENSURE(propagation.propagate(*fx.root) != stx::simplify_result::conflict);
        ENSURE(!nf.is_satisfied() && mf.memberships().empty());
    }

    static void tst_ncontains_literal_with_pending_equation_scope() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
        expr_ref h(fx.m.mk_fresh_const("h", fx.s), fx.m);
        expr_ref needle(fx.m.mk_fresh_const("needle", fx.s), fx.m);
        expr_ref ab(fx.u.str.mk_string("ab"), fx.m);
        auto& ef = fx.root->facet_as<seq::eq_facet>(fx.eq_id);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
        auto& dm = fx.tree.dep_mgr();
        ef.add_equation(x, y);
        nf.add_ncontains(h, needle);
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::proceed);
        ENSURE(nf.qhead() == 1 && mf.memberships().empty());
        fx.trail.push_scope();
        nf.add_ncontains(h, ab, dm.mk_leaf(7));
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::proceed);
        ENSURE(!ef.is_satisfied());
        ENSURE(!nf.ncontains()[1].active() && mf.memberships().size() == 1);
        ENSURE(dm.contains(mf.memberships()[0].m_dep, 7));
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::noop);
        fx.trail.pop_scope(1);
        ENSURE(!ef.is_satisfied() && nf.ncontains().size() == 1);
        ENSURE(nf.qhead() == 1 && mf.memberships().empty());
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::noop);
    }

    static void tst_ncontains_literal_reach_substitution() {
        for (char const* text : {"A", "ab"}) {
            fixture fx;
            expr_ref h(fx.m.mk_fresh_const("h", fx.s), fx.m);
            expr_ref needle(fx.u.str.mk_string(text), fx.m);
            expr_ref word(fx.u.str.mk_string("i"), fx.m);
            expr_ref word_re(fx.u.re.mk_to_re(word), fx.m);
            auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
            auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
            nf.add_ncontains(h, needle);
            seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
            ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::satisfied);
            auto const& membership = mf.memberships()[0];
            auto live = mf.live().reachable_live(membership.m_view);
            expr_ref_vector units(fx.m);
            fx.u.str.get_concat_units(word, units);
            seq::mem_split split(fx.m, fx.u, fx.rw, mf.live());
            bool accepted = false;
            for (unsigned i = 0; expr* target = live.at(i); ++i) {
                seq::view reach = seq::view::reach(membership.m_view.m_state, target, fx.m);
                seq::view_vector views;
                views.push_back(reach);
                views.push_back(seq::view::membership(word_re, fx.m));
                lbool feasible = mf.vw().product_nonempty(h, views, nullptr);
                ENSURE(feasible != l_undef);
                if (feasible == l_false)
                    continue;
                // Substituting a word certified by the symbolic reach view
                // must not turn that same view into a conflict.
                seq::mem_split::branch branch;
                auto it = split.iterate(units, reach);
                ENSURE(it.next(branch) && !it.gave_up());
                accepted = true;
            }
            ENSURE(accepted && !live.failed());
        }
    }

    static void tst_ncontains_completion_after_literal_lowering_scope() {
        fixture fx;
        expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
        expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
        expr_ref h(fx.m.mk_fresh_const("h", fx.s), fx.m);
        expr_ref needle(fx.u.str.mk_string("="), fx.m);
        auto& ef = fx.root->facet_as<seq::eq_facet>(fx.eq_id);
        auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
        auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
        auto& sf = fx.root->facet_as<seq::solver_facet>(fx.arith_id);
        auto& af = fx.root->facet_as<seq::assumption_facet>(fx.assumption_id);
        ef.add_equation(x, y);
        nf.add_ncontains(h, needle, fx.tree.dep_mgr().mk_leaf(7));
        seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::satisfied);
        ENSURE(nf.is_satisfied() && mf.memberships().size() == 1);
        fx.trail.push_scope();
        ef.remove_equation_trailed(0);
        expr_ref length(fx.u.str.mk_length(h), fx.m);
        sf.add_constraint(fx.m.mk_eq(length, fx.a.mk_int(257)));
        ENSURE(fx.solver.check() == l_true);
        seq::model_completion_split completion(fx.m, fx.u);
        seq::eq_tree::edge edge;
        bool more = false, committed = false;
        ENSURE(!completion.split(*fx.root, 0, edge, more, committed));
        ENSURE(!more && !committed && !af.model_completion_blocked());
        ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::noop);
        ENSURE(mf.memberships().size() == 1);
        ENSURE(fx.tree.dep_mgr().contains(mf.memberships()[0].m_dep, 7));
        fx.trail.pop_scope(1);
        ENSURE(!af.model_completion_blocked() && mf.memberships().size() == 1);
        ENSURE(nf.is_satisfied() && nf.qhead() == 1 && !ef.is_satisfied());
    }

    static void tst_ncontains_character_projection_scope(bool surrounded) {
        for (unsigned code : { 97u, 0x1f600u }) {
            fixture fx;
            expr_ref x(fx.m.mk_fresh_const("x", fx.s), fx.m);
            expr_ref y(fx.m.mk_fresh_const("y", fx.s), fx.m);
            expr_ref c(fx.m.mk_fresh_const("c", fx.u.mk_char_sort()), fx.m);
            expr_ref unit(fx.u.str.mk_unit(c), fx.m);
            expr_ref haystack(unit, fx.m);
            if (surrounded)
                haystack = fx.u.str.mk_concat(x, unit, y);
            expr_ref forbidden(fx.u.str.mk_char(code), fx.m);
            expr_ref needle(fx.u.str.mk_unit(forbidden), fx.m);
            auto& nf = fx.root->facet_as<seq::ncontains_facet>(fx.nc_id);
            auto& mf = fx.root->facet_as<seq::mem_facet>(fx.mem_id);
            auto& sf = fx.root->facet_as<seq::solver_facet>(fx.arith_id);
            auto& af = fx.root->facet_as<seq::assumption_facet>(fx.assumption_id);
            auto& dm = fx.tree.dep_mgr();
            nf.add_ncontains(haystack, needle, dm.mk_leaf(8));
            fx.trail.push_scope();
            seq::ncontains_propagation propagation(fx.m, fx.u, fx.a);
            ENSURE(propagation.propagate(*fx.root) == stx::simplify_result::satisfied);
            ENSURE(mf.memberships().size() == (surrounded ? 2u : 0u) && af.assumptions().size() == 1);
            for (auto const& membership : mf.memberships())
                ENSURE(dm.contains(membership.m_dep, 8));
            expr_ref equal(fx.m.mk_eq(c, forbidden), fx.m);
            sf.add_constraint(equal, dm.mk_leaf(9));
            ENSURE(sf.has_conflict());
            ENSURE(dm.contains(sf.conflict_dep(), 8));
            ENSURE(dm.contains(sf.conflict_dep(), 9));
            fx.trail.pop_scope(1);
            ENSURE(!nf.is_satisfied() && mf.memberships().empty());
            ENSURE(af.assumptions().empty() && !sf.has_conflict());
            expr_ref other(fx.u.str.mk_char(code + 1), fx.m);
            expr_ref different(fx.m.mk_eq(c, other), fx.m);
            sf.add_constraint(different);
            ENSURE(fx.tree.solve() == stx::search_result::sat);
        }
    }

} // namespace

void tst_seq_ncontains_facet() {
    tst_ncontains_fixed_length_choices();
    tst_ncontains_unit_tail_preimage_scope();
    tst_ncontains_replace_witness_scope();
    tst_ncontains_self_replace_witness_scope();
    tst_ncontains_reverse_stoi_alphabet_scope();
    tst_ncontains_symbolic_needle_nonempty(false);
    tst_ncontains_symbolic_needle_nonempty(true);
    tst_ncontains_symbolic_unit_clauses();
    tst_ncontains_symbolic_unit_false_clause();
    tst_ncontains_large_symbolic_units_deferred();
    tst_ncontains_unit_length_bound();
    tst_ncontains_length_gate_discharges();
    tst_ncontains_empty_needle_conflict();
    tst_ncontains_ground_no_occurrence_sat();
    tst_ncontains_ground_occurrence_unsat();
    tst_ncontains_resolved_by_substitution_unsat();
    tst_ncontains_match_not_at_first_position_unsat();
    tst_ncontains_conflicts_with_cyclic_equation();
    tst_ncontains_joint_witness();
    tst_ncontains_cross_boundary_conflict();
    tst_ncontains_substitution_scope();
    tst_ncontains_literal_with_pending_equation_scope();
    tst_ncontains_literal_reach_substitution();
    tst_ncontains_completion_after_literal_lowering_scope();
    tst_ncontains_character_projection_scope(false);
    tst_ncontains_character_projection_scope(true);
    std::cout << "seq_ncontains_facet: all tests passed\n";
}

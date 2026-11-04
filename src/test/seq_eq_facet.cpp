/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_eq_facet.cpp (test)

Abstract:

    Unit test for `seq::eq_facet` / `seq::eq_propagation` / `seq::word_eq_split`
    (ast/seq/seq_eq_facet.h): word-equation solving via the Nielsen
    transformation, running on top of the generic `stx::search_tree` core
    (util/stx_search_tree.h).

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/
#include "ast/ast.h"
#include "ast/reg_decl_plugins.h"
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq/seq_eq_facet.h"
#include "ast/seq/seq_assumption_facet.h"
#include "ast/seq/seq_mem_facet.h"
#include "ast/seq/seq_ncontains_facet.h"
#include "smt/seq_solver_facet.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include <iostream>
#include <sstream>

namespace {
    struct eq_approx_fixture {
        struct context : seq::null_ambient_context<seq::eq_tree::dep_tracker> {
            theory_seq_params params;
            context(ast_manager& m, seq_util& u, trail_stack& trail) :
                null_ambient_context(m, u, trail) {}
            theory_seq_params const& fparams() const override { return params; }
        };
        ast_manager m;
        seq_util u;
        arith_util a;
        seq_rewriter rw;
        trail_stack trail;
        context ac;
        seq::eq_tree tree;
        seq::eq_tree::node* root;
        stx::facet_id eq_id, mem_id;
        seq::eq_approx_split approx;

        static ast_manager& init(ast_manager& m) { reg_decl_plugins(m); return m; }
        eq_approx_fixture(unsigned max_states = 1u << 12) :
            u(init(m)), a(m), rw(m), ac(m, u, trail), tree(trail, m.limit()),
            root(tree.mk_root()),
            eq_id(tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr())),
            mem_id(tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac)),
            approx(m, u, rw, max_states) {
            ac.set_eq_id(eq_id);
            ac.set_mem_id(mem_id);
            ac.params.m_seq_eq_approx = true;
            tree.set_ambient_context(&ac);
        }
        seq::eq_facet& eqs() { return root->facet_as<seq::eq_facet>(eq_id); }
        seq::mem_facet& mems() { return root->facet_as<seq::mem_facet>(mem_id); }
        expr_ref var(char const* name) {
            return expr_ref(m.mk_fresh_const(name, u.str.mk_string_sort()), m);
        }
        expr_ref word(char const* value) {
            return expr_ref(u.re.mk_to_re(u.str.mk_string(value)), m);
        }
        void add(expr* term, expr* regex, unsigned dep) {
            mems().add(seq::str_mem(m, term, seq::view::membership(regex, m), tree.dep_mgr().mk_leaf(dep)));
        }
        bool refuted() {
            root->clear_status();
            seq::eq_tree::edge edge;
            bool more = true, committed = true;
            ENSURE(!approx.split(*root, 0, edge, more, committed));
            ENSURE(!more && !committed);
            return root->is_conflict();
        }
    };

    static void tst_eq_approx_memberships() {
        eq_approx_fixture f;
        expr_ref x = f.var("x"), y = f.var("y"), p = f.var("p"), q = f.var("q"), z = f.var("z");
        expr_ref at(f.u.str.mk_string("@"), f.m), colon(f.u.str.mk_string(":"), f.m);
        expr* lhs_args[] = { x, at, y };
        expr* rhs_args[] = { p, colon, q };
        expr_ref lhs(f.u.str.mk_concat(3, lhs_args, x->get_sort()), f.m);
        expr_ref rhs(f.u.str.mk_concat(3, rhs_args, x->get_sort()), f.m);
        f.eqs().add_equation(lhs, rhs, f.tree.dep_mgr().mk_leaf(1));
        expr_ref a = f.word("a"), b = f.word("b"), c = f.word("c");
        expr_ref as(f.u.re.mk_star(a), f.m), bs(f.u.re.mk_star(b), f.m), cs(f.u.re.mk_star(c), f.m);
        f.add(x, as, 2);
        f.add(y, bs, 3);
        f.add(z, cs, 4);
        f.ac.params.m_seq_eq_approx = false;
        ENSURE(!f.refuted());
        f.ac.params.m_seq_eq_approx = true;
        ENSURE(f.refuted());
        auto& dm = f.tree.dep_mgr();
        for (unsigned dep : {1u, 2u, 3u})
            ENSURE(dm.contains(f.root->conflict_dep(), dep));
        ENSURE(!dm.contains(f.root->conflict_dep(), 4));
    }

    static void tst_eq_approx_conjunctive_views() {
        eq_approx_fixture f;
        expr_ref x = f.var("x"), y = f.var("y");
        expr_ref a = f.word("a"), b = f.word("b"), c = f.word("c");
        expr_ref ab(f.u.re.mk_union(a, b), f.m);
        expr_ref ac(f.u.re.mk_union(a, c), f.m);
        expr_ref bc(f.u.re.mk_union(b, c), f.m);
        f.eqs().add_equation(x, y, f.tree.dep_mgr().mk_leaf(1));
        f.add(x, ab, 2);
        f.add(y, bc, 3);
        ENSURE(!f.refuted());
        f.add(x, ac, 4);
        ENSURE(f.refuted());
        for (unsigned dep : {1u, 2u, 3u, 4u})
            ENSURE(f.tree.dep_mgr().contains(f.root->conflict_dep(), dep));
    }

    static void tst_eq_approx_scopes() {
        eq_approx_fixture f;
        expr_ref x = f.var("x"), b(f.u.str.mk_string("b"), f.m);
        expr_ref a = f.word("a");
        expr_ref as(f.u.re.mk_star(a), f.m);
        f.eqs().add_equation(x, b, f.tree.dep_mgr().mk_leaf(1));
        ENSURE(!f.refuted());
        f.trail.push_scope();
        f.add(x, as, 2);
        ENSURE(f.refuted());
        f.trail.pop_scope(1);
        ENSURE(!f.refuted());
        f.trail.push_scope();
        f.add(x, as, 3);
        f.mems().remove(f.mems().memberships().size() - 1);
        ENSURE(!f.refuted());
        f.trail.pop_scope(1);
        ENSURE(!f.refuted());
        f.trail.push_scope();
        f.add(x, as, 4);
        f.eqs().remove_equation_trailed(0);
        ENSURE(!f.refuted());
        f.trail.pop_scope(1);
        ENSURE(!f.refuted());
    }

    static void tst_eq_approx_unsupported_views() {
        eq_approx_fixture f;
        expr_ref x = f.var("x"), a(f.u.str.mk_string("a"), f.m);
        f.eqs().add_equation(x, a);
        expr_ref ab = f.word("ab"), b = f.word("b");
        f.mems().add(seq::str_mem(f.m, x, seq::view::reach(ab, b, f.m)));
        ENSURE(!f.refuted()); // The reach language is {"a"}, not {"ab"}.
        expr_ref r(f.m.mk_fresh_const("R", ab->get_sort()), f.m);
        ENSURE(!f.u.re.is_ground(r));
        f.add(x, r, 1);
        ENSURE(!f.refuted());
        expr_ref y = f.var("y");
        expr_ref symbolic(f.u.re.mk_to_re(y), f.m);
        ENSURE(!f.u.re.is_ground(symbolic));
        f.add(x, symbolic, 2);
        ENSURE(!f.refuted());
    }

    static void tst_eq_approx_generic_sequences() {
        eq_approx_fixture f;
        sort_ref seq_sort(f.u.str.mk_seq(f.a.mk_int()), f.m);
        expr_ref x(f.m.mk_fresh_const("x", seq_sort), f.m);
        expr_ref zero(f.u.str.mk_unit(f.a.mk_int(0)), f.m);
        expr_ref one(f.u.str.mk_unit(f.a.mk_int(1)), f.m);
        expr_ref regex(f.u.re.mk_to_re(zero), f.m);
        f.eqs().add_equation(x, one, f.tree.dep_mgr().mk_leaf(1));
        f.add(x, regex, 2);
        ENSURE(f.refuted());
        ENSURE(f.tree.dep_mgr().contains(f.root->conflict_dep(), 2));
        f.trail.push_scope();
        f.eqs().remove_equation_trailed(0);
        expr_ref empty(f.u.str.mk_empty(seq_sort), f.m);
        f.eqs().add_equation(empty, zero);
        ENSURE(f.refuted());
        f.trail.pop_scope(1);
    }

    static void tst_eq_approx_symbolic_predicate() {
        eq_approx_fixture f;
        sort* elem_sort = f.a.mk_int();
        sort_ref seq_sort(f.u.str.mk_seq(elem_sort), f.m);
        expr_ref x(f.m.mk_fresh_const("x", seq_sort), f.m);
        expr_ref p(f.m.mk_fresh_const("p", elem_sort), f.m);
        expr_ref q(f.m.mk_fresh_const("q", elem_sort), f.m);
        expr_ref v(f.m.mk_var(0, elem_sort), f.m);
        expr_ref vp(f.m.mk_eq(v, p), f.m), vq(f.m.mk_eq(v, q), f.m);
        expr_ref body(f.m.mk_and(vp, vq), f.m);
        symbol name("v");
        expr_ref pred(f.m.mk_lambda(1, &elem_sort, &name, body), f.m);
        expr_ref regex(f.u.re.mk_of_pred(pred), f.m);
        ENSURE(f.u.re.is_ground(regex)); // The regex-info flag does not inspect predicates.
        expr_ref zero(f.u.str.mk_unit(f.a.mk_int(0)), f.m);
        f.eqs().add_equation(x, zero);
        f.add(x, regex, 1);
        ENSURE(!f.refuted()); // p = q = 0 is consistent.
    }

    static void tst_eq_approx_budget() {
        eq_approx_fixture f(0);
        expr_ref x = f.var("x"), b(f.u.str.mk_string("b"), f.m);
        expr_ref a = f.word("a");
        f.eqs().add_equation(x, b);
        f.add(x, a, 1);
        ENSURE(!f.refuted());
    }

    static expr_ref mk_unit_char(ast_manager& m, seq_util& u, char ch) {
        return expr_ref(u.str.mk_unit(u.str.mk_char(static_cast<unsigned>(ch))), m);
    }

    // deq_facet::add_disequation only takes token vectors (no expr*/expr*
    // convenience overload); tests that build a disequation from whole
    // terms go through get_concat_units themselves.
    static expr_ref_vector mk_toks(seq_util& u, ast_manager& m, expr* e) {
        expr_ref_vector ts(m);
        u.str.get_concat_units(e, ts);
        return ts;
    }

    stx::search_result solve_eq(ast_manager& m, seq_util& u, expr* lhs, expr* rhs, unsigned max_depth = 12) {
        trail_stack tr;
        arith_util a(m);
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        root->facet_as<seq::eq_facet>(id).add_equation(lhs, rhs);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(id);
        ac.set_arith_id(arith_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));

        tree.set_max_search_depth(max_depth);
        return tree.solve();
    }

    static void tst_trivial_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref lhs(u.str.mk_string(zstring("ab")), m);
        expr_ref rhs(u.str.mk_string(zstring("ab")), m);
        (void)s;
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::sat);
    }

    static void tst_symbol_clash_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref lhs(u.str.mk_string(zstring("ab")), m);
        expr_ref rhs(u.str.mk_string(zstring("ba")), m);
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::unsat);
    }

    // X ++ "a" = "a" ++ X is satisfiable (e.g. X = epsilon), and reachable
    // via the Nielsen transformation in a single branch.
    static void tst_commute_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref lhs(u.str.mk_concat(X, a), m);
        expr_ref rhs(u.str.mk_concat(a, X), m);
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::sat);
    }

    static void tst_model_completion_records_string_witness() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref T(m.mk_fresh_const("T", s), m);
        expr_ref K(m.mk_fresh_const("K", s), m);
        expr_ref nth0(u.str.mk_nth_i(X, a.mk_int(0)), m);
        expr_ref nth1(u.str.mk_nth_i(X, a.mk_int(1)), m);
        expr_ref unit0(u.str.mk_unit(nth0), m);
        expr_ref unit1(u.str.mk_unit(nth1), m);
        expr* rhs_args[3] = { unit0, unit1, T };
        expr_ref rhs(u.str.mk_concat(3, rhs_args, s), m);

        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id nc_id = tree.register_facet<seq::ncontains_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        ac.set_ncontains_id(nc_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);

        auto& ef = root->facet_as<seq::eq_facet>(eq_id);
        auto& sf = root->facet_as<seq::solver_facet>(arith_id);
        auto& nf = root->facet_as<seq::ncontains_facet>(nc_id);
        auto& asf = root->facet_as<seq::assumption_facet>(assumption_id);
        ef.add_equation(X, rhs);
        sf.add_constraint(m.mk_eq(u.str.mk_length(X), a.mk_int(2)));
        sf.add_constraint(m.mk_eq(u.str.mk_length(T), a.mk_int(0)));
        expr_ref c0(u.str.mk_char('F'), m);
        expr_ref c1(u.str.mk_char(9), m);
        expr_ref e0(m.mk_eq(nth0, c0), m);
        expr_ref e1(m.mk_eq(nth1, c1), m);
        sf.add_constraint(e0);
        sf.add_constraint(e1);
        asf.add_assumption(e0, ac);
        asf.add_assumption(e1, ac);
        expr_ref comma(u.str.mk_string(zstring(",")), m);
        expr_ref equals(u.str.mk_string(zstring("=")), m);
        nf.add_ncontains(X, comma);
        nf.add_ncontains(K, equals);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::ncontains_propagation, m, u, a));
        tree.add_completion_plugin(alloc(seq::model_completion_split, m, u));

        ENSURE(tree.solve() == stx::search_result::sat);
        auto* snap = tree.sat_snapshot();
        ENSURE(snap != nullptr);
        auto const& assumptions = snap->facet_as<seq::assumption_facet>(assumption_id).assumptions();
        unsigned expected_codes[2] = { 'F', 9 };
        zstring expected(2, expected_codes);
        bool found = false;
        for (auto const& [assumption, dep] : assumptions) {
            expr* lhs = nullptr, *rhs_value = nullptr;
            zstring str;
            if (m.is_eq(assumption, lhs, rhs_value) && lhs == X && u.str.is_string(rhs_value, str) && str == expected) {
                found = true;
                break;
            }
        }
        ENSURE(found);
    }

    // Shared variable forced equal to two different constants.
    // Exercises Nielsen splitting and backtracking before reporting unsat.
    static void tst_branch_then_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        trail_stack tr;
        arith_util au(m);

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, au, tree.dep_mgr());
        stx::facet_id id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        auto& f = root->facet_as<seq::eq_facet>(id);
        f.add_equation(X, a);
        f.add_equation(X, b);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(12);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    static void tst_depth_cutoff() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref lhs(u.str.mk_concat(X, Y), m);
        expr_ref rhs(u.str.mk_string(zstring("abc")), m);
        ENSURE(solve_eq(m, u, lhs, rhs, 0) == stx::search_result::depth_cutoff);
    }

    // A disequation between two distinct constants is immediately
    // discharged (proved satisfiable-distinct) with no branching needed.
    static void tst_deq_trivial_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(mk_toks(u, m, a), mk_toks(u, m, b));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_deq_id(id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.set_max_search_depth(4);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    static void tst_deq_unit_nonempty_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a(u.str.mk_char('a'), m);
        expr_ref unit(u.str.mk_unit(a), m);
        expr_ref empty(u.str.mk_empty(u.str.mk_string_sort()), m);

        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(mk_toks(u, m, unit), mk_toks(u, m, empty));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_deq_id(id);
        tree.set_ambient_context(&ac);
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    static void check_deq_empty_length(bool reverse, unsigned form) {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref x(m.mk_fresh_const("x", u.str.mk_string_sort()), m);
        expr_ref y(m.mk_fresh_const("y", u.str.mk_string_sort()), m);
        expr_ref len_y(u.str.mk_length(y), m);
        expr_ref prefix(mk_unit_char(m, u, 'a'));
        expr_ref_vector lhs(m), rhs(m), empty(m);
        if (form == 1) {
            lhs.push_back(prefix);
            rhs.push_back(prefix);
        }
        if (form == 2)
            lhs.push_back(x);
        rhs.push_back(y);

        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        auto eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        auto deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        auto arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);
        auto& df = root->facet_as<seq::deq_facet>(deq_id);
        auto& sf = root->facet_as<seq::solver_facet>(arith_id);
        df.add_disequation(reverse ? rhs : lhs, reverse ? lhs : rhs, tree.dep_mgr().mk_leaf(7));
        seq::deq_propagation prop(m, u);
        for (unsigned length : { 0u, 2u }) {
            tr.push_scope();
            expr_ref length_value(a.mk_int(length), m);
            sf.add_constraint(m.mk_eq(len_y, length_value), tree.dep_mgr().mk_leaf(9));
            if (form == 2)
                seq::broadcast_subst(*root, x, empty, tree.dep_mgr().mk_leaf(11));
            prop.propagate(*root);
            ENSURE(df.is_satisfied());
            if (length == 0) {
                ENSURE(sf.has_conflict());
                vector<unsigned, false> deps;
                tree.dep_mgr().linearize(sf.conflict_dep(), deps);
                ENSURE(std::find(deps.begin(), deps.end(), 7u) != deps.end());
                ENSURE(std::find(deps.begin(), deps.end(), 9u) != deps.end());
                if (form == 2)
                    ENSURE(std::find(deps.begin(), deps.end(), 11u) != deps.end());
            }
            else
                ENSURE(sf.is_satisfied());
            tr.pop_scope(1);
            ENSURE(df.disequations()[0].active());
            ENSURE(sf.is_satisfied());
        }
    }

    static void tst_deq_empty_length() {
        for (bool reverse : { false, true })
            for (unsigned form : { 0u, 1u, 2u })
                check_deq_empty_length(reverse, form);
    }

    // A disequation between a constant and itself is an immediate
    // conflict (both sides prefix-strip to empty: forced equal).
    static void tst_deq_trivial_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        expr_ref a1(u.str.mk_string(zstring("a")), m);
        expr_ref a2(u.str.mk_string(zstring("a")), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        stx::facet_id id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(id).add_disequation(mk_toks(u, m, a1), mk_toks(u, m, a2));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_deq_id(id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.set_max_search_depth(4);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    // A substitution produced by eq_facet must propagate to deq_facet so
    // `X != "b"` is discharged after solving `X = "a"`.
    static void tst_deq_reacts_to_eq_branch_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);
        expr_ref b(u.str.mk_string(zstring("b")), m);

        trail_stack tr;
        arith_util au(m);

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, au, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        root->facet_as<seq::eq_facet>(eq_id).add_equation(X, a);
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(mk_toks(u, m, X), mk_toks(u, m, b));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.set_max_search_depth(12);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // Symbolic char equality must substitute `c := 'a'`, reducing the
    // equation to `X = X`.
    static void tst_word_eq_split_char_eq_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* char_s = u.mk_char_sort();
        sort* s = u.str.mk_string_sort();
        expr_ref c(m.mk_fresh_const("c", char_s), m);
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref ca(u.mk_char('a'), m);
        expr_ref lhs(u.str.mk_concat(u.str.mk_unit(c), X), m);
        expr_ref rhs(u.str.mk_concat(u.str.mk_unit(ca), X), m);
        ENSURE(solve_eq(m, u, lhs, rhs) == stx::search_result::sat);
    }

    // Check that find_eq_split_point chooses the balanced interior split
    // for `[a, X, Y] = [X, a, Y]`, with zero padding.
    static void tst_eq_split_find_point() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);

        expr_ref_vector lhs(m), rhs(m);
        lhs.push_back(mk_unit_char(m, u, 'a')); lhs.push_back(X); lhs.push_back(Y);
        rhs.push_back(X); rhs.push_back(mk_unit_char(m, u, 'a')); rhs.push_back(Y);

        unsigned split_lhs = 0, split_rhs = 0;
        int padding = 0;
        bool found = seq::eq_split::find_eq_split_point(u, lhs, rhs, split_lhs, split_rhs, padding);
        ENSURE(found);
        ENSURE(split_lhs == 2);
        ENSURE(split_rhs == 2);
        ENSURE(padding == 0);
    }

    // No interior split exists for `[X] = [a]`.
    static void tst_eq_split_find_point_none() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref a(u.str.mk_string(zstring("a")), m);

        expr_ref_vector lhs(m), rhs(m);
        lhs.push_back(X);
        rhs.push_back(mk_unit_char(m, u, 'a'));

        unsigned split_lhs = 0, split_rhs = 0;
        int padding = 0;
        ENSURE(!seq::eq_split::find_eq_split_point(u, lhs, rhs, split_lhs, split_rhs, padding));
    }

    // Balanced interior split on `X ++ a ++ Y = Y ++ a ++ X` should make
    // progress and preserve satisfiability.
    static void tst_eq_split_progress_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);
        expr_ref ch(u.str.mk_string(zstring("a")), m);
        expr_ref lhs(u.str.mk_concat(u.str.mk_concat(X, ch), Y), m);
        expr_ref rhs(u.str.mk_concat(u.str.mk_concat(Y, ch), X), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        root->facet_as<seq::eq_facet>(eq_id).add_equation(lhs, rhs);

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.add_split_plugin(alloc(seq::eq_split, m, u));
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // `X != Y` over two unconstrained variables should be discharged by
    // deq_split rather than getting stuck as unknown.
    static void tst_deq_split_free_vars_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m);
        expr_ref Y(m.mk_fresh_const("Y", s), m);

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(mk_toks(u, m, X), mk_toks(u, m, Y));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        ac.set_deq_id(deq_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.add_split_plugin(alloc(seq::eq_split, m, u));
        tree.add_split_plugin(alloc(seq::deq_split, m, u));
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::sat);
    }

    // `a != a` should remain an immediate conflict even when deq_split is
    // enabled.
    static void tst_deq_split_equal_consts_unsat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref ca(mk_unit_char(m, u, 'a'));

        trail_stack tr;

        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        stx::facet_id eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        stx::facet_id arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        stx::facet_id deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        root->facet_as<seq::deq_facet>(deq_id).add_disequation(mk_toks(u, m, ca), mk_toks(u, m, ca));

        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        ac.set_deq_id(deq_id);
        tree.set_ambient_context(&ac);

        tree.add_propagation_plugin(alloc(seq::eq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_split_plugin(alloc(seq::word_eq_split, m, u));
        tree.add_split_plugin(alloc(seq::eq_split, m, u));
        tree.add_split_plugin(alloc(seq::deq_split, m, u));
        tree.set_max_search_depth(20);
        ENSURE(tree.solve() == stx::search_result::unsat);
    }

    static void tst_deq_split_multiple_units_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        auto eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        auto deq_id = tree.register_facet<seq::deq_facet>(*root, m, u, tree.dep_mgr());
        auto arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        auto assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);

        expr_ref x(m.mk_const("x", a.mk_int()), m);
        expr_ref y(m.mk_const("y", a.mk_int()), m);
        expr_ref z(m.mk_const("z", a.mk_int()), m);
        expr_ref ux(u.str.mk_unit(x), m), uy(u.str.mk_unit(y), m), uz(u.str.mk_unit(z), m);
        auto& df = root->facet_as<seq::deq_facet>(deq_id);
        df.add_disequation(mk_toks(u, m, ux), mk_toks(u, m, uy));
        df.add_disequation(mk_toks(u, m, uy), mk_toks(u, m, uz));
        tree.add_propagation_plugin(alloc(seq::deq_propagation, m, u));
        tree.add_propagation_plugin(alloc(seq::arith_propagation, m, u));
        tree.add_split_plugin(alloc(seq::deq_split, m, u));
        tree.set_max_nodes(32);
        ENSURE(tree.solve() == stx::search_result::sat);
        ENSURE(df.disequations()[0].active() && df.disequations()[1].active());
        ENSURE(root->facet_as<seq::assumption_facet>(assumption_id).assumptions().empty());
    }

    static void check_length_model(ast_manager& m, expr* element, unsigned length, bool word_equation) {
        seq_util u(m);
        arith_util a(m);
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        p.set_bool("model", true);
        ref<solver> s = mk_smt_solver(m, p, symbol("ALL"));
        sort_ref seq_sort(u.str.mk_seq(element->get_sort()), m);
        expr_ref x(m.mk_const("x", seq_sort), m), y(m.mk_const("y", seq_sort), m);
        expr_ref_vector assertions(m);
        assertions.push_back(m.mk_eq(u.str.mk_length(x), a.mk_int(length)));
        if (word_equation) {
            expr_ref unit(u.str.mk_unit(element), m);
            assertions.push_back(m.mk_eq(u.str.mk_concat(x, unit), u.str.mk_concat(unit, y)));
        }
        for (expr* assertion : assertions)
            s->assert_expr(assertion);
        ENSURE(s->check_sat(0, nullptr) == l_true);
        model_ref md;
        s->get_model(md);
        ENSURE(md);
        for (expr* assertion : assertions)
            ENSURE(md->is_true(assertion));
    }

    static void tst_nseq_length_model() {
        ast_manager m;
        reg_decl_plugins(m);
        arith_util a(m);
        seq_util u(m);
        expr_ref_vector elements(m);
        elements.push_back(a.mk_int(1));
        elements.push_back(m.mk_true());
        elements.push_back(u.str.mk_char('a'));
        for (expr* element : elements)
            for (unsigned length : { 0u, 1u, 3u })
                for (bool word_equation : { false, true })
                    check_length_model(m, element, length, word_equation);
    }

    static void tst_nseq_empty_diseq() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref x(m.mk_fresh_const("x", u.str.mk_string_sort()), m);
        expr_ref z(m.mk_fresh_const("z", a.mk_int()), m);
        expr_ref text(u.str.mk_string("A"), m);
        expr_ref part(u.str.mk_substr(text, z, z), m);
        expr_ref empty(u.str.mk_empty(x->get_sort()), m);
        expr_ref eq_part(m.mk_eq(x, part), m);
        expr_ref eq_empty(m.mk_eq(x, empty), m);
        expr_ref assertion(m.mk_not(m.mk_eq(eq_part, eq_empty)), m);
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
        s->assert_expr(assertion);
        ENSURE(s->check_sat(0, nullptr) == l_false);
    }

    static void check_nseq_candidate_model(char const* input, bool require_sat = true, char const* scoped_integer = nullptr) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(input);
        ENSURE(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        p.set_bool("model", true);
        ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
        for (expr* assertion : cmd.assertions())
            s->assert_expr(assertion);
        auto check_model = [&]() {
            lbool result = s->check_sat(0, nullptr);
            ENSURE(result == l_true || (!require_sat && result == l_undef));
            if (result != l_true)
                return;
            model_ref md;
            s->get_model(md);
            ENSURE(md);
            for (expr* assertion : cmd.assertions())
                ENSURE(md->is_true(assertion));
        };
        check_model();
        if (scoped_integer) {
            arith_util a(m);
            expr_ref v(m.mk_const(cmd.find_func_decl(symbol(scoped_integer))), m);
            expr_ref rejected(m.mk_eq(v, a.mk_int(1)), m);
            s->push();
            s->assert_expr(rejected);
            ENSURE(s->check_sat(0, nullptr) == l_false);
            s->pop(1);
            check_model();
        }
    }

    static void tst_nseq_candidate_model() {
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const v Int)
            (assert (str.in_re x (re.++ (re.* (str.to_re "a")) (re.+ (str.to_re "b")))))
            (assert (str.in_re x (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
            (assert (str.in_re x (re.* (re.range "a" "u"))))
            (assert (str.in_re x (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
            (assert (not (str.in_re (str.++ "a" x "b") (re.++ (re.* (str.to_re "a")) (str.to_re "b")))))
            (assert (= (* v 2) (+ (str.len x) 2)))
        )", true, "v");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const z Int)
            (assert (not (= (str.contains (str.substr x z z) "A")
                            (str.prefixof "A" (str.substr x z z)))))
        )");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (define-fun i () Int (+ (str.indexof x " " 0) 1))
            (define-fun y () String (str.substr x i (- (str.len x) i)))
            (define-fun j () Int (+ (str.indexof y "." 0) 1))
            (define-fun z () String (str.substr y j (- (str.len y) j)))
            (assert (= (str.len z) 0))
            (assert (str.contains y "."))
            (assert (> (str.len y) 0))
            (assert (not (str.contains y " ")))
            (assert (str.contains x " "))
            (assert (> (str.len x) 0))
            (assert (>= i 0))
            (assert (>= (- (str.len x) i) 0))
            (assert (>= j 0))
            (assert (>= (- (str.len y) j) 0))
        )");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (declare-const t String)
            (declare-const n String)
            (assert (= (str.++ x y) (str.++ t n)))
            (assert (str.in_re n (re.* (str.to_re ""))))
            (assert (< (str.len x) (str.to_int t)))
        )", false);
    }

} // namespace

    // Block compression should solve `X.a.Y = aaaa.b` within depth 1.
    static void tst_block_compression_sat() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        sort* s = u.str.mk_string_sort();
        expr_ref X(m.mk_fresh_const("X", s), m), Y(m.mk_fresh_const("Y", s), m);
        expr_ref lhs(u.str.mk_concat(X, u.str.mk_concat(u.str.mk_string(zstring("a")), Y)), m);
        expr_ref rhs(u.str.mk_string(zstring("aaaab")), m);
        ENSURE(solve_eq(m, u, lhs, rhs, 1) == stx::search_result::sat);
    }

void tst_seq_eq_facet() {
    tst_eq_approx_memberships();
    tst_eq_approx_conjunctive_views();
    tst_eq_approx_scopes();
    tst_eq_approx_unsupported_views();
    tst_eq_approx_generic_sequences();
    tst_eq_approx_symbolic_predicate();
    tst_eq_approx_budget();
    tst_trivial_sat();
    tst_symbol_clash_unsat();
    tst_commute_sat();
    tst_model_completion_records_string_witness();
    tst_branch_then_unsat();
    tst_depth_cutoff();
    tst_deq_trivial_sat();
    tst_deq_unit_nonempty_sat();
    tst_deq_empty_length();
    tst_deq_trivial_unsat();
    tst_deq_reacts_to_eq_branch_sat();
    tst_eq_split_find_point();
    tst_eq_split_find_point_none();
    tst_eq_split_progress_sat();
    tst_deq_split_free_vars_sat();
    tst_deq_split_equal_consts_unsat();
    tst_deq_split_multiple_units_sat();
    tst_word_eq_split_char_eq_sat();
    tst_block_compression_sat();
    tst_nseq_length_model();
    tst_nseq_empty_diseq();
    tst_nseq_candidate_model();
    std::cout << "seq_eq_facet: all tests passed\n";
}

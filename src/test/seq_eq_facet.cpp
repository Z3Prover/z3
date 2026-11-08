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
#include "ast/seq/seq_skolem.h"
#include "smt/seq_solver_facet.h"
#include "smt/smt_context.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "util/rlimit.h"
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

    static void tst_word_eq_positional_bound(bool overlap, bool symbolic = false, bool deferred = false) {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        auto eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        auto arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        tree.set_ambient_context(&ac);
        auto& ef = root->facet_as<seq::eq_facet>(eq_id);
        auto& sf = root->facet_as<seq::solver_facet>(arith_id);
        sort* s = u.str.mk_string_sort();
        expr_ref x(m.mk_fresh_const("x", s), m), y(m.mk_fresh_const("y", s), m);
        expr_ref z(m.mk_fresh_const("z", s), m), p(m.mk_fresh_const("p", s), m);
        expr_ref q(m.mk_fresh_const("q", s), m), r(m.mk_fresh_const("r", s), m);
        expr_ref decoy_l(u.str.mk_concat(p, q), m), decoy_r(u.str.mk_concat(r, z), m);
        expr_ref block(u.str.mk_string("a"), m);
        expr_ref delim(u.str.mk_string(overlap ? "a" : "b"), m);
        if (symbolic) {
            expr_ref c(m.mk_fresh_const("c", u.mk_char_sort()), m);
            delim = u.str.mk_unit(c);
        }
        expr_ref left_inner(u.str.mk_concat(x, block), m), right_inner(u.str.mk_concat(y, delim), m);
        expr_ref lhs(u.str.mk_concat(left_inner, z), m), rhs(u.str.mk_concat(right_inner, r), m);
        if (deferred)
            ef.add_equation(decoy_l, decoy_r, tree.dep_mgr().mk_leaf(3));
        ef.add_equation(lhs, rhs, tree.dep_mgr().mk_leaf(7));
        if (!deferred)
            ef.add_equation(decoy_l, decoy_r, tree.dep_mgr().mk_leaf(3));
        expr_ref ly(u.str.mk_length(y), m), lx(u.str.mk_length(x), m);
        expr_ref different(m.mk_not(m.mk_eq(lx, ly)), m);
        for (auto const& eq : ef.equations())
            sf.add_length_constraint(eq.m_lhs, eq.m_rhs, eq.m_dep);
        seq::eq_propagation prop(m, u);
        tr.push_scope();
        prop.propagate(*root);
        seq::eq_tree::dep_tracker dep = nullptr;
        if (overlap || symbolic || deferred) {
            ENSURE(sf.implies(different, &dep) != l_true);
        }
        else {
            ENSURE(sf.implies(different, &dep) == l_true);
            ENSURE(tree.dep_mgr().contains(dep, 7));
            ENSURE(!tree.dep_mgr().contains(dep, 3));
        }
        tr.pop_scope(1);
        ENSURE(sf.implies(different, &dep) != l_true);
    }

    static void tst_word_eq_proved_length_alignment(bool suffix = false, bool symbolic = false, bool compound = false, bool interpreted_tail = false) {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        trail_stack tr;
        seq::eq_tree tree(tr, m.limit());
        auto* root = tree.mk_root();
        seq::sub_solver solver(m, a, tree.dep_mgr());
        auto eq_id = tree.register_facet<seq::eq_facet>(*root, m, u, tree.dep_mgr());
        auto arith_id = tree.register_facet<seq::solver_facet>(*root, m, u, solver);
        auto assumption_id = tree.register_facet<seq::assumption_facet>(*root, m);
        seq::null_ambient_context<seq::eq_tree::dep_tracker> ac(m, u, tr);
        ac.set_eq_id(eq_id);
        ac.set_arith_id(arith_id);
        ac.set_assumption_id(assumption_id);
        tree.set_ambient_context(&ac);
        auto& ef = root->facet_as<seq::eq_facet>(eq_id);
        auto& sf = root->facet_as<seq::solver_facet>(arith_id);
        sort* s = u.str.mk_string_sort();
        expr_ref x(m.mk_fresh_const("x", s), m), y = mk_unit_char(m, u, 'a');
        expr_ref p(m.mk_fresh_const("p", s), m), q(m.mk_fresh_const("q", s), m);
        if (interpreted_tail) {
            expr_ref source(m.mk_fresh_const("s", s), m);
            expr_ref one(a.mk_int(1), m), length(u.str.mk_length(source), m);
            expr_ref rest(a.mk_sub(length, one), m);
            p = u.str.mk_substr(source, one, rest);
        }
        if (compound) {
            expr* args[] = { p };
            x = u.mk_skolem(symbol("test.fragment"), 1, args, s);
        }
        if (symbolic) {
            expr* ch = nullptr;
            VERIFY(u.str.is_unit(y, ch));
            expr_ref value(m.mk_fresh_const("c", ch->get_sort()), m);
            y = u.str.mk_unit(value);
        }
        expr_ref lhs(u.str.mk_concat(x, p), m), rhs(u.str.mk_concat(y, q), m);
        if (suffix) {
            expr_ref k(m.mk_fresh_const("k", a.mk_int()), m);
            expr_ref ca(u.str.mk_string("a"), m), cb(u.str.mk_string("b"), m);
            expr_ref pa(u.str.mk_power(ca, k), m), pb(u.str.mk_power(cb, k), m);
            lhs = u.str.mk_concat(pa, x);
            rhs = u.str.mk_concat(pb, y);
        }
        ef.add_equation(lhs, rhs, tree.dep_mgr().mk_leaf(7));
        expr_ref lx(u.str.mk_length(x), m);
        expr_ref one(a.mk_int(1), m);
        sf.add_constraint(a.mk_ge(lx, one));
        seq::word_eq_split split(m, u);

        rational xv;
        ENSURE(sf.value(lx, xv) && xv.is_one());
        tr.push_scope();
        seq::eq_tree::edge model_edge;
        bool model_more = false, model_committed = false;
        auto model_it = split.split(*root, 0, model_edge, model_more, model_committed);
        ENSURE(model_it && model_committed);
        expr_ref_vector repl(m);
        ENSURE(ef.get_subst(x, repl) && repl.empty());
        tr.pop_scope(1);

        tr.push_scope();
        expr_ref c = mk_unit_char(m, u, 'a');
        expr_ref left_part(suffix ? ef.equations()[0].m_lhs[0] : p.get(), m);
        expr_ref right_part(suffix ? ef.equations()[0].m_rhs[0] : q.get(), m);
        expr_ref other_lhs(u.str.mk_concat(left_part, c), m), other_rhs(u.str.mk_concat(c, right_part), m);
        ef.add_equation(other_lhs, other_rhs, tree.dep_mgr().mk_leaf(9));
        auto const& first = ef.equations()[0];
        auto const& second = ef.equations()[1];
        sf.add_length_constraint(first.m_lhs, first.m_rhs, first.m_dep);
        sf.add_length_constraint(second.m_lhs, second.m_rhs, second.m_dep);
        seq::eq_tree::edge edge;
        bool more = false, committed = false;
        expr_ref length_one(m.mk_eq(lx, one), m);
        seq::eq_tree::dep_tracker dep = nullptr;
        ENSURE(sf.implies(length_one, &dep) == l_true);
        unsigned_vector deps;
        tree.dep_mgr().linearize(dep, deps);
        ENSURE(deps.contains(7) && deps.contains(9));
        tr.push_scope();
        auto it = split.split(*root, 0, edge, more, committed);
        if (compound || interpreted_tail) {
            ENSURE(it && committed);
            ENSURE(ef.get_subst(x, repl) && repl.empty());
            tr.pop_scope(2);
            return;
        }
        ENSURE(!it && more && committed);
        dep = nullptr;
        ENSURE(ef.get_subst(x, repl, &dep));
        ENSURE(repl.size() == 1 && repl[0] == y);
        deps.reset();
        tree.dep_mgr().linearize(dep, deps);
        ENSURE(deps.contains(7) && deps.contains(9));
        tr.pop_scope(1);
        repl.reset();
        ENSURE(!ef.get_subst(x, repl));
        ENSURE((suffix ? ef.equations()[0].m_lhs.back() : ef.equations()[0].m_lhs[0]) == x);

        tr.pop_scope(1);
        tr.push_scope();
        it = split.split(*root, 0, edge, more, committed);
        ENSURE(it && committed);
        repl.reset();
        ENSURE(ef.get_subst(x, repl) && repl.empty());
        ENSURE(sf.has_conflict());
        tr.pop_scope(1);
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
        scoped_rlimit limit(m.limit(), 1000000);
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
        seq_rewriter rw(m);
        stx::facet_id mem_id = tree.register_facet<seq::mem_facet>(*root, m, u, tree.dep_mgr(), rw, ac);
        ac.set_eq_id(eq_id);
        ac.set_deq_id(deq_id);
        ac.set_arith_id(arith_id);
        ac.set_ncontains_id(nc_id);
        ac.set_mem_id(mem_id);
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
        tree.add_propagation_plugin(alloc(seq::mem_propagation, m, u, rw));
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

    static void tst_deq_disjoint_stars() {
        for (bool disjoint : { false, true }) {
            eq_approx_fixture f;
            expr_ref x = f.var("x"), y = f.var("y");
            expr_ref left = f.word("a"), right = f.word(disjoint ? "b" : "a");
            left = f.u.re.mk_star(left);
            right = f.u.re.mk_star(right);
            f.add(x, left, 11);
            f.add(y, right, 13);
            auto deq_id = f.tree.register_facet<seq::deq_facet>(*f.root, f.m, f.u, f.tree.dep_mgr());
            seq::sub_solver solver(f.m, f.a, f.tree.dep_mgr());
            auto arith_id = f.tree.register_facet<seq::solver_facet>(*f.root, f.m, f.u, solver);
            f.ac.set_deq_id(deq_id);
            f.ac.set_arith_id(arith_id);
            auto& df = f.root->facet_as<seq::deq_facet>(deq_id);
            auto& sf = f.root->facet_as<seq::solver_facet>(arith_id);
            df.add_disequation(mk_toks(f.u, f.m, x), mk_toks(f.u, f.m, y),
                              f.tree.dep_mgr().mk_leaf(7));
            f.trail.push_scope();
            expr_ref len_x(f.u.str.mk_length(x), f.m), len_y(f.u.str.mk_length(y), f.m);
            expr_ref zero(f.a.mk_int(0), f.m);
            sf.add_constraint(f.m.mk_eq(len_x, zero), f.tree.dep_mgr().mk_leaf(17));
            sf.add_constraint(f.m.mk_eq(len_y, zero), f.tree.dep_mgr().mk_leaf(19));
            seq::mem_propagation prop(f.m, f.u, f.rw);
            auto result = prop.propagate(*f.root);
            if (disjoint) {
                ENSURE(result == stx::simplify_result::conflict);
                ENSURE(df.is_satisfied());
                vector<unsigned, false> deps;
                f.tree.dep_mgr().linearize(sf.conflict_dep(), deps);
                for (unsigned dep : { 7u, 11u, 13u, 17u, 19u })
                    ENSURE(std::find(deps.begin(), deps.end(), dep) != deps.end());
            }
            else
                ENSURE(df.disequations()[0].active());
            f.trail.pop_scope(1);
            f.root->clear_status();
            ENSURE(df.disequations()[0].active());
            ENSURE(sf.is_satisfied());
        }
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

    static void tst_nseq_index_suffix_axiom(bool compound = false, bool selector = false, unsigned ch = '=',
                                           bool indirect = false, bool length_only = false) {
        struct propagation_context : smt::context {
            using smt::context::context;
            using smt::context::propagate;
        };
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        th_rewriter rw(m);
        seq::skolem sk(m, rw);
        smt_params params;
        params.m_string_solver = symbol("nseq");
        propagation_context ctx(m, params);
        expr_ref s(m.mk_const("source", u.str.mk_string_sort()), m);
        if (compound) {
            expr_ref prefix(m.mk_const("prefix", s->get_sort()), m);
            s = u.str.mk_concat(prefix, s);
        }
        expr_ref needle(u.str.mk_string(zstring(1, &ch)), m);
        expr_ref zero(a.mk_int(0), m), one(a.mk_int(1), m);
        expr_ref index(u.str.mk_index(s, needle, zero), m);
        expr_ref start(a.mk_add(one, index), m);
        expr_ref len(u.str.mk_length(s), m);
        expr_ref remaining(a.mk_sub(len, start), m);
        expr_ref suffix(u.str.mk_substr(s, start, remaining), m);
        rw(suffix);
        expr_ref right = sk.mk_indexof_right(s, needle);
        expr_ref found(u.str.mk_contains(s, needle), m);
        for (bool present : {false, true, false}) {
            if (!present && (compound || selector || length_only))
                continue;
            ctx.push();
            ctx.internalize(found, false);
            ctx.mark_as_relevant(found.get());
            smt::literal lit = ctx.get_literal(found);
            ctx.assign(present ? lit : ~lit, smt::b_justification::mk_axiom());
            ctx.internalize(suffix, false);
            ctx.mark_as_relevant(suffix.get());
            expr_ref consumer(u.str.mk_length(suffix), m);
            if (!length_only)
                consumer = u.str.mk_contains(suffix, u.str.mk_string("x"));
            ctx.internalize(consumer, false);
            ctx.mark_as_relevant(consumer.get());
            if (selector) {
                expr_ref selected(suffix, m);
                if (indirect)
                    selected = u.str.mk_concat(needle, suffix);
                expr_ref at(u.str.mk_at(selected, zero), m);
                ctx.internalize(at, false);
                ctx.mark_as_relevant(at.get());
            }
            ENSURE(ctx.propagate());
            if (present) {
                ENSURE(ctx.e_internalized(right));
                bool same = ctx.get_enode(suffix)->get_root() == ctx.get_enode(right)->get_root();
                ENSURE(same == (!compound && !selector && !length_only));
            }
            else {
                ENSURE(ctx.get_enode(suffix)->get_root() == ctx.get_enode(s)->get_root());
            }
            ctx.pop(1);
        }
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

    static void tst_nseq_regex_bounds() {
        char const* cases[] = {
            R"(
                (declare-const x String)
                (assert (str.in_re x (re.* (str.to_re "a"))))
                (assert (= (str.len x) 3))
                (assert (not (= x "abb")))
                (assert (not (= "bab" x)))
                (assert (not (= x "aab")))
                (assert (not (= x "aaa")))
            )",
            R"(
                (declare-const x String)
                (assert (not (= "abb" x)))
                (assert (not (= x "bab")))
                (assert (not (= x "aab")))
                (assert (= (str.len x) 3))
                (assert (str.in_re x (re.* (str.to_re "a"))))
                (assert (not (= "aaa" x)))
            )",
            R"(
                (declare-const x String)
                (assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))
                (assert (not (= (str.++ x "b") "bb")))
                (assert (not (= x "a")))
            )",
            R"(
                (declare-const x String)
                (assert (str.in_re x (re.union (str.to_re "a")
                    (re.++ (str.to_re "b") (re.* re.allchar)))))
                (assert (not (str.in_re x (re.++ re.all (str.to_re "b") re.all))))
                (assert (>= (str.len x) 2))
            )",
            R"(
                (declare-const x String)
                (assert (str.in_re x (re.union (str.to_re "aaaa")
                    (re.++ (str.to_re "b") (re.* re.allchar)))))
                (assert (not (str.in_re x (re.++ re.all (str.to_re "b") re.all))))
                (assert (<= (str.len x) 3))
            )",
            R"(
                (declare-const x String)
                (declare-const y String)
                (assert (str.in_re (str.++ x "z" y) (re.* (str.to_re "z"))))
                (assert (str.in_re x (re.* (re.range "a" "u"))))
                (assert (str.in_re y (re.* (re.range "a" "u"))))
                (assert (>= (str.len x) 0))
                (assert (not (= x "")))
            )"
        };
        for (char const* input : cases) {
            ast_manager m;
            reg_decl_plugins(m);
            scoped_rlimit limit(m.limit(), 100000);
            cmd_context cmd(false, &m);
            std::istringstream is(input);
            ENSURE(parse_smt2_commands(cmd, is));
            params_ref p;
            p.set_sym("string_solver", symbol("nseq"));
            p.set_bool("model", true);
            p.set_bool("unsat_core", true);
            ref<solver> s = mk_smt2_solver(m, p, symbol("QF_SLIA"));
            unsigned last = cmd.assertions().size() - 1;
            for (unsigned i = 0; i < last; ++i)
                s->assert_expr(cmd.assertions().get(i));
            s->push();
            expr_ref guard(m.mk_fresh_const("guard", m.mk_bool_sort()), m);
            s->assert_expr(m.mk_implies(guard, cmd.assertions().get(last)));
            expr* assumptions[] = {guard};
            ENSURE(s->check_sat(1, assumptions) == l_false);
            expr_ref_vector core(m);
            s->get_unsat_core(core);
            ENSURE(core.size() == 1 && core.get(0) == guard);
            s->pop(1);
            ENSURE(s->check_sat(0, nullptr) == l_true);
            model_ref md;
            s->get_model(md);
            ENSURE(md);
            for (unsigned i = 0; i < last; ++i)
                ENSURE(md->is_true(cmd.assertions().get(i)));
        }
    }

    static void check_nseq_candidate_model(char const* input, bool require_sat = true, char const* scoped_integer = nullptr,
                                          unsigned budget = 1000000) {
        ast_manager m;
        reg_decl_plugins(m);
        scoped_rlimit limit(m.limit(), budget);
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
            if (require_sat && result != l_true)
                std::cerr << "nseq candidate failed: " << input << "\n";
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

    static void tst_nseq_disjoint_stars() {
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (assert (str.in_re x (re.* (str.to_re "d"))))
            (assert (str.in_re y (re.* (str.to_re "["))))
            (assert (= (str.len x) (str.len y)))
            (assert (not (= x y)))
            (assert (= 7 (str.len x)))
        )");
    }

    static void tst_nseq_regex_diseq_completion() {
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (declare-const v Int)
            (assert (= v 2))
            (assert (str.in_re x (re.* (re.++ (re.* (str.to_re "ww")) (str.to_re "++")))))
            (assert (str.in_re y (re.* (re.++ (re.* (str.to_re "ww")) (str.to_re "++")))))
            (assert (= (str.len x) (str.len y)))
            (assert (not (= x y)))
        )", true, "v");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (assert (str.in_re x (re.* (re.++ (str.to_re "ff") (re.* (str.to_re "||"))))))
            (assert (str.in_re y (re.* (re.++ (str.to_re "ff") (re.* (str.to_re "||"))))))
            (assert (= (str.len x) (str.len y)))
            (assert (not (= x y)))
        )");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (declare-const v Int)
            (assert (= v 2))
            (assert (str.in_re x (re.* (re.++ (str.to_re "I") (re.* (str.to_re "&"))))))
            (assert (str.in_re y (re.* (str.to_re "I"))))
            (assert (= (str.len x) (str.len y)))
            (assert (not (= x y)))
        )", true, "v");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (assert (str.in_re x (re.* (re.++ (re.* (str.to_re "aaaa")) (str.to_re "bbbb")))))
            (assert (str.in_re y (re.* (str.to_re "bbbb"))))
            (assert (= (str.len x) (str.len y)))
            (assert (not (= x y)))
        )");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (declare-const v Int)
            (assert (= v 2))
            (assert (str.in_re x (re.* (re.++ (str.to_re "b") (re.* (str.to_re "a"))))))
            (assert (str.in_re y (re.* (re.++ (str.to_re "b") (re.* (str.to_re "a"))))))
            (assert (= (str.len x) 7))
            (assert (= (str.len y) 7))
            (assert (not (= x y)))
        )", true, "v");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))
            (assert (str.in_re y (re.union (str.to_re "a") (str.to_re "b"))))
            (assert (= (str.len x) 1))
            (assert (= (str.len y) 1))
            (assert (not (= x y)))
        )");
        check_nseq_candidate_model(R"(
            (declare-const x String)
            (declare-const y String)
            (assert (str.in_re x (re.* (re.range "0" "9"))))
            (assert (str.in_re y (re.* (re.range "0" "9"))))
            (assert (= (str.len x) 7))
            (assert (= (str.len y) 7))
            (assert (not (= x y)))
            (assert (= (str.to_int x) 1234567))
        )", false);
    }

    static void tst_nseq_contains_index() {
        std::ostringstream input;
        input << R"(
            (declare-const key1 String)
            (declare-const key2 String)
            (define-fun i1 () Int (str.indexof key1 "A" 0))
            (define-fun i2 () Int (str.indexof key2 "O" 0))
            (define-fun tail1 () String (str.substr key1 (+ i1 1) (- (str.len key1) (+ i1 1))))
            (define-fun tail2 () String (str.substr key2 (+ i2 1) (- (str.len key2) (+ i2 1))))
            (define-fun folded () String
                (str.++ (str.replace (str.substr key2 0 (+ i2 1)) "O" "o") tail2))
            (assert (str.contains tail1 "A"))
            (assert (str.contains key1 "A"))
        )";
        for (char c = 'Z'; c > 'O'; --c)
            input << "(assert (not (str.contains folded \"" << c << "\")))\n";
        input << R"(
            (assert (not (str.contains tail2 "O")))
            (assert (str.contains key2 "O"))
        )";
        for (char c = 'N'; c >= 'A'; --c)
            input << "(assert (not (str.contains key2 \"" << c << "\")))\n";
        input << R"(
            (assert (>= i1 (- 1)))
            (assert (>= (- (str.len key1) i1) 1))
            (assert (>= i2 (- 1)))
            (assert (>= (- (str.len key2) i2) 1))
        )";
        check_nseq_candidate_model(input.str().c_str());
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (declare-const v Int)
            (assert (= v 2))
            (assert (str.contains s "aa"))
            (assert (= (str.indexof s "aa" 0) 1))
            (assert (= (str.len s) 5))
            (assert (str.contains (str.substr s 3 2) "aa"))
        )", true, "v");
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (assert (str.contains s "aa"))
            (assert (= (str.indexof s "aa" 0) 0))
            (assert (= (str.indexof s "aa" 1) 1))
            (assert (= (str.len s) 3))
        )");
    }

    static void tst_nseq_fixed_lengths() {
        char const* input = R"(
            (declare-const s String)
            (assert (not (str.contains s "A")))
            (assert (= (str.indexof s ":" 0) (- 1)))
            (assert (not (= (str.at s 0) "[")))
            (assert (not (= (str.len s) 0)))
            (assert (not (str.contains s ",")))
            (assert (not (str.contains s "://")))
        )";
        ast_manager m;
        reg_decl_plugins(m);
        scoped_rlimit limit(m.limit(), 1000000);
        cmd_context cmd(false, &m);
        std::istringstream is(input);
        ENSURE(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        p.set_bool("model", true);
        ref<solver> slv = mk_smt2_solver(m, p, symbol("QF_SLIA"));
        for (expr* assertion : cmd.assertions())
            slv->assert_expr(assertion);
        auto check = [&]() {
            ENSURE(slv->check_sat(0, nullptr) == l_true);
            model_ref md;
            slv->get_model(md);
            ENSURE(md);
            for (expr* assertion : cmd.assertions())
                ENSURE(md->is_true(assertion));
        };
        check();
        seq_util u(m);
        arith_util a(m);
        expr_ref s(m.mk_const(cmd.find_func_decl(symbol("s"))), m);
        expr_ref length_two(m.mk_eq(u.str.mk_length(s), a.mk_int(2)), m);
        slv->push();
        slv->assert_expr(length_two);
        check();
        model_ref md;
        slv->get_model(md);
        ENSURE(md->is_true(length_two));
        slv->pop(1);
        check();
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (define-fun t () String (str.substr s 1 (- (str.len s) 1)))
            (assert (= (str.at s 0) " "))
            (assert (= (str.at t (- (str.len t) 1)) " "))
            (assert (not (= (str.at t 0) " ")))
            (assert (not (= (str.len t) 0)))
            (assert (= (str.indexof s "=" 0) (- 1)))
            (assert (not (str.contains s ",")))
        )", true, nullptr, 10000000);
    }

    static void tst_nseq_short_stoi_bounds() {
        ast_manager m;
        reg_decl_plugins(m);
        seq_util u(m);
        arith_util a(m);
        expr_ref s(m.mk_fresh_const("s", u.str.mk_string_sort()), m);
        expr_ref i(m.mk_fresh_const("i", a.mk_int()), m);
        expr_ref zero(a.mk_int(0), m), one(a.mk_int(1), m);
        expr_ref_vector arguments(m);
        arguments.push_back(u.str.mk_at(s, i));
        arguments.push_back(u.str.mk_substr(s, i, one));
        arguments.push_back(u.str.mk_substr(s, i, zero));
        int upper_bounds[] = { 9, 9, -1 };
        params_ref p;
        p.set_sym("string_solver", symbol("nseq"));
        p.set_uint("max_conflicts", 0);
        for (unsigned j = 0; j < arguments.size(); ++j) {
            expr_ref conversion(u.str.mk_stoi(arguments.get(j)), m);
            expr_ref upper(a.mk_int(upper_bounds[j]), m);
            ref<solver> slv = mk_smt2_solver(m, p, symbol("QF_SLIA"));
            slv->assert_expr(a.mk_gt(conversion, upper));
            ENSURE(slv->check_sat(0, nullptr) == l_false);
        }
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (assert (= (str.len s) 1))
            (assert (= (str.to_int (str.at s 0)) (- 1)))
            (assert (= (str.to_int (str.at s (- 1))) (- 1)))
            (assert (= (str.to_int (str.at s 1)) (- 1)))
        )");
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (declare-const i Int)
            (assert (= (str.to_int (str.at s i)) 9))
        )");
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (assert (= (str.to_int (str.++ (str.at s 0) (str.at s 1))) 42))
        )");
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (assert (= (str.to_int (str.++ "0" (str.at s 0))) 7))
        )");
    }

    static void tst_nseq_candidate_model() {
        check_nseq_candidate_model(R"(
            (declare-const s String)
            (assert (>= (str.len s) 2))
            (assert (not (str.contains s ",")))
            (assert (not (str.contains s "=")))
        )");
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
    tst_word_eq_positional_bound(false);
    tst_word_eq_positional_bound(true);
    tst_word_eq_positional_bound(false, true);
    tst_word_eq_positional_bound(false, false, true);
    tst_word_eq_proved_length_alignment();
    tst_word_eq_proved_length_alignment(true);
    tst_word_eq_proved_length_alignment(false, true);
    tst_word_eq_proved_length_alignment(false, false, true);
    tst_word_eq_proved_length_alignment(false, false, false, true);
    tst_trivial_sat();
    tst_symbol_clash_unsat();
    tst_commute_sat();
    tst_model_completion_records_string_witness();
    tst_branch_then_unsat();
    tst_depth_cutoff();
    tst_deq_trivial_sat();
    tst_deq_unit_nonempty_sat();
    tst_deq_empty_length();
    tst_deq_disjoint_stars();
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
    tst_nseq_index_suffix_axiom();
    tst_nseq_index_suffix_axiom(true);
    tst_nseq_index_suffix_axiom(false, true);
    tst_nseq_index_suffix_axiom(false, false, 0x1f642);
    tst_nseq_index_suffix_axiom(false, true, '=', true);
    tst_nseq_index_suffix_axiom(false, false, '=', false, true);
    tst_nseq_length_model();
    tst_nseq_empty_diseq();
    tst_nseq_regex_bounds();
    tst_nseq_candidate_model();
    tst_nseq_disjoint_stars();
    tst_nseq_regex_diseq_completion();
    tst_nseq_contains_index();
    tst_nseq_fixed_lengths();
    tst_nseq_short_stoi_bounds();
    std::cout << "seq_eq_facet: all tests passed\n";
}

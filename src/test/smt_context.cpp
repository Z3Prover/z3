
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt/smt_context.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "ast/rewriter/distribute_forall.h"
#include "ast/simplifiers/distribute_forall.h"
#include "solver/solver.h"
#include "solver/assertions/asserted_formulas.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/fpa/fpa2bv_tactic.h"
#include "tactic/arith/elim_monotone_tactic.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "model/model_evaluator.h"
#include <cstring>
#include <sstream>

static void check_sat_smt_recfun(char const* input)
{
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context cmd(false, &m);
    std::istringstream is(input);
    VERIFY(parse_smt2_commands(cmd, is));
    params_ref p;
    p.set_bool("smt", true);
    ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
    for (expr* a : cmd.assertions())
        slv->assert_expr(a);
    VERIFY(l_true == slv->check_sat(0, nullptr));
}

static void check_sat_smt_model(char const* input)
{
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context cmd(false, &m);
    std::istringstream is(input);
    VERIFY(parse_smt2_commands(cmd, is));
    params_ref p;
    p.set_bool("smt", true);
    ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
    for (expr* a : cmd.assertions())
        slv->assert_expr(a);
    VERIFY(l_true == slv->check_sat(0, nullptr));
    model_ref model;
    slv->get_model(model);
    VERIFY(model);
}

static bool get_uint_stat(statistics const& st, char const* key, unsigned& value) {
    for (unsigned i = 0; i < st.size(); ++i)
        if (st.is_uint(i) && !strcmp(st.get_key(i), key)) {
            value = st.get_uint_value(i);
            return true;
        }
    return false;
}

static void check_array_domain(char const* input, lbool expected) {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context cmd(false, &m);
    std::istringstream is(input);
    VERIFY(parse_smt2_commands(cmd, is));
    ref<solver> slv = mk_smt2_solver(m, params_ref(), symbol::null);
    for (expr* a : cmd.assertions())
        slv->assert_expr(a);
    VERIFY(expected == slv->check_sat(0, nullptr));
}

static void check_symbolic_regex_substring() {
    for (unsigned relevancy : {0u, 2u}) {
        for (char const* word : {"x", "xy"}) {
            ast_manager m;
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream is(
                std::string("(set-logic QF_SLIA)\n")
                + "(declare-const t String)\n"
                + "(declare-const i Int)\n"
                + "(assert (distinct (str.substr t i 2) \"\"))\n"
                + "(assert (str.in_re \"" + word
                + "\" (re.++ (str.to_re (str.substr t i 2)) re.allchar)))\n");
            VERIFY(parse_smt2_commands(cmd, is));
            params_ref p;
            p.set_uint("relevancy", relevancy);
            ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
            for (expr* assertion : cmd.assertions())
                slv->assert_expr(assertion);
            lbool expected = !strcmp(word, "x") ? l_false : l_true;
            VERIFY(expected == slv->check_sat(0, nullptr));

            slv->push();
            slv->assert_expr(m.mk_not(cmd.assertions()[0]));
            VERIFY(l_false == slv->check_sat(0, nullptr));
            slv->pop(1);
            VERIFY(expected == slv->check_sat(0, nullptr));
        }
    }
}

static void check_real_power_bounds() {
    for (unsigned seed = 0; seed < 8; ++seed) {
        for (char const* input : {
                "(declare-const y Real)\n"
                "(assert (>= y 1))\n"
                "(assert (< (^ (/ 1 2) y) (/ 1 2)))\n",
                "(declare-const y Real)\n"
                "(assert (> y 0))\n"
                "(assert (<= y 1))\n"
                "(assert (> (^ (/ 1 2) y) (/ 1 2)))\n"}) {
            ast_manager m;
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream is(input);
            VERIFY(parse_smt2_commands(cmd, is));
            params_ref p;
            p.set_bool("smt", true);
            p.set_uint("random_seed", seed);
            ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
            slv->push();
            for (expr* assertion : cmd.assertions())
                slv->assert_expr(assertion);
            // General real powers may return unknown, but must not refute these witnesses.
            VERIFY(l_false != slv->check_sat(0, nullptr));
        }
    }
}

static void check_monotone_reals() {
    struct example { char const* input; bool eliminated; lbool expected; bool empty = false; };
    for (auto const& ex : {
            example{
                "(declare-const x Real)(declare-const y Real)"
                "(assert (or (> x 0) (< y 0)))"
                "(assert (> y 1))", true, l_true, true},
            example{
                "(declare-const x Real)(declare-const y Real)(declare-const z Real)"
                "(declare-const b Bool)"
                "(assert (or (> x y) (> x (+ y 1))))"
                "(assert (or (> z (+ x 10)) b))", true, l_true},
            example{
                "(declare-const x Real)(declare-const y Real)(declare-const z Real)"
                "(assert (= y (- 4)))(assert (= z 3))"
                "(assert (not (<= (/ (+ (* 3 x) y) 2) z)))"
                "(assert (< (- x x x) 20))", true, l_true},
            example{
                "(declare-const x Real)(declare-const y Real)"
                "(declare-const b Bool)"
                "(assert (= y 2))"
                "(assert (=> b (>= (+ (* (- 2) x) y) 4)))"
                "(assert (ite b (< x y) (< x (- y 1))))", true, l_true},
            example{
                "(declare-const x Real)"
                "(assert (ite (< x 0) (> x 1) (< x (- 1))))", false, l_false},
            example{
                "(declare-const x Real)(declare-const y Real)"
                "(declare-fun f (Real) Real)"
                "(assert (> x 0))(assert (= (f x) y))", false, l_true},
            example{
                "(declare-const x Int)(assert (< x 0))(assert (> x 1))", false, l_false}}) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(ex.input);
        VERIFY(parse_smt2_commands(cmd, is));
        goal_ref g = alloc(goal, m, true, true);
        unsigned i = 0;
        for (expr* f : cmd.assertions()) {
            app_ref label(m.mk_const(symbol(i++), m.mk_bool_sort()), m);
            g->assert_expr(f, label.get());
        }
        tactic_ref t = mk_elim_monotone_tactic(m);
        goal_ref_buffer result;
        (*t)(g, result);
        VERIFY(result.size() == 1);
        if (ex.empty)
            VERIFY(g->size() == 0);
        statistics st;
        t->collect_statistics(st);
        unsigned eliminated = 0;
        get_uint_stat(st, "elim-monotone", eliminated);
        VERIFY((eliminated != 0) == ex.eliminated);
        ref<solver> slv = mk_smt2_solver(m, params_ref(), symbol::null);
        for (unsigned j = 0; j < g->size(); ++j) {
            VERIFY(g->dep(j));
            slv->assert_expr(g->form(j));
        }
        VERIFY(slv->check_sat(0, nullptr) == ex.expected);
        if (ex.expected == l_true) {
            model_ref md;
            slv->get_model(md);
            if (g->mc())
                (*g->mc())(md);
            model_evaluator eval(*md);
            eval.set_model_completion(true);
            for (expr* f : cmd.assertions()) {
                expr_ref value(m);
                eval(f, value);
                VERIFY(m.is_true(value));
            }
        }
    }
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    arith_util a(m);
    app_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref f(a.mk_gt(x, a.mk_real(0)), m);
    goal_ref g = alloc(goal, m, true, true, true);
    g->assert_expr(f);
    tactic_ref t = mk_elim_monotone_tactic(m);
    goal_ref_buffer result;
    (*t)(g, result);
    VERIFY(g->size() == 1 && g->form(0) == f && g->pr(0));

    base_dependent_expr_state st(m);
    st.add(dependent_expr(m, f, g->pr(0), nullptr));
    elim_monotone simp(m, st);
    simp.reduce();
    VERIFY(st.qtail() == 1 && st[0].fml() == f && st[0].pr() == g->pr(0));
}

static void check_monotone_simplifier() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    app_ref x(m.mk_const("x", a.mk_real()), m);
    app_ref y(m.mk_const("y", a.mk_real()), m);
    expr_ref zero(a.mk_real(0), m);
    expr_ref x_gt_y(a.mk_gt(x, y), m);
    expr_ref y_gt_zero(a.mk_gt(y, zero), m);
    base_dependent_expr_state chain(m);
    chain.add(dependent_expr(m, x_gt_y, nullptr, nullptr));
    chain.add(dependent_expr(m, y_gt_zero, nullptr, nullptr));
    elim_monotone chain_simp(m, chain);
    chain_simp.reduce();
    VERIFY(m.is_true(chain[0].fml()) && m.is_true(chain[1].fml()));
    model_ref md = alloc(model, m);
    model_converter_ref mc = chain.model_trail().get_model_converter();
    (*mc)(md);
    model_evaluator eval(*md);
    expr_ref value(m);
    eval(x_gt_y, value);
    VERIFY(m.is_true(value));
    eval(y_gt_zero, value);
    VERIFY(m.is_true(value));

    expr_ref lower(a.mk_gt(x, zero), m);
    app_ref label(m.mk_const("lower", m.mk_bool_sort()), m);
    expr_dependency_ref dep(m.mk_leaf(label), m);
    for (bool use_assumptions : {false, true}) {
        for (int n : {-1, 10}) {
            base_dependent_expr_state st(m);
            st.add(dependent_expr(m, lower, nullptr, dep));
            elim_monotone simp(m, st);
            simp.reduce();
            VERIFY(m.is_true(st[0].fml()));
            st.advance_qhead();
            expr_ref numeral(a.mk_real(n), m);
            expr_ref eq(m.mk_eq(x, numeral), m);
            expr_ref_vector assumptions(m);
            if (use_assumptions)
                assumptions.push_back(eq);
            else
                st.add(dependent_expr(m, eq, nullptr, nullptr));
            st.replay(st.qhead(), assumptions);
            bool restored = false;
            for (unsigned i = st.qhead(); i < st.qtail(); ++i)
                if (st[i].fml() == lower) {
                    restored = true;
                    VERIFY(st[i].dep() == dep);
                }
            VERIFY(restored);
            if (use_assumptions)
                VERIFY(assumptions.size() == 1 && assumptions.get(0) == eq);
            // Assumptions must remain frozen while reprocessing the restored bounds.
            st.freeze(assumptions);
            simp.reduce();
            ref<solver> slv = mk_smt2_solver(m, params_ref(), symbol::null);
            for (unsigned i = 0; i < st.qtail(); ++i)
                slv->assert_expr(st[i].fml());
            VERIFY(slv->check_sat(assumptions.size(), assumptions.data()) == (n > 0 ? l_true : l_false));
        }
    }

    base_dependent_expr_state prefix(m);
    prefix.add(dependent_expr(m, lower, nullptr, nullptr));
    prefix.advance_qhead();
    expr_ref upper(a.mk_lt(x, zero), m);
    prefix.add(dependent_expr(m, upper, nullptr, nullptr));
    elim_monotone prefix_simp(m, prefix);
    prefix_simp.reduce();
    VERIFY(prefix[0].fml() == lower && prefix[1].fml() == upper);
}

static void check_bounded_clause_flattening() {
    for (unsigned budget : {0u, 8u, UINT_MAX})
      for (bool reverse : {false, true}) {
        ast_manager m;
        reg_decl_plugins(m);
        smt_params params;
        params.m_propagate_values = false;
        params.m_solve_eqs = false;
        params.m_nnf_cnf = false;
        params.m_max_bv_sharing = false;
        params.m_flat_clause_budget = budget;
        asserted_formulas formulas(m, params, params_ref());
        unsigned const size = 32;
        expr_ref_vector guards(m), components(m);
        for (unsigned i = 0; i < size; ++i) {
            guards.push_back(m.mk_fresh_const("guard", m.mk_bool_sort()));
            components.push_back(m.mk_fresh_const("component", m.mk_bool_sort()));
        }
        expr_ref conjunction(m.mk_not(m.mk_or(components.size(), components.data())), m);
        for (expr* guard : guards)
            formulas.assert_expr(reverse ? m.mk_or(conjunction, guard) : m.mk_or(guard, conjunction));
        formulas.reduce();
        VERIFY(formulas.get_num_formulas() <= 8 * size);
        if (budget < size) {
            VERIFY(formulas.get_num_formulas() == size);
        }
        else {
            VERIFY(formulas.get_num_formulas() > size);
        }

        ref<solver> slv = mk_smt2_solver(m, params_ref(), symbol::null);
        for (unsigned i = 0; i < formulas.get_num_formulas(); ++i)
            slv->assert_expr(formulas.get_formula(i));
        for (bool all_guards : {false, true})
            for (bool first_component : {false, true}) {
                slv->push();
                for (expr* guard : guards)
                    slv->assert_expr(all_guards ? guard : m.mk_not(guard));
                for (unsigned i = 0; i < size; ++i) {
                    expr* component = components.get(i);
                    slv->assert_expr(first_component && i == 0 ? component : m.mk_not(component));
                }
                bool expected = all_guards || !first_component;
                VERIFY((expected ? l_true : l_false) == slv->check_sat(0, nullptr));
                slv->pop(1);
            }
    }
}

static void check_extended_lra_features() {
    for (unsigned variant = 0; variant < 4; ++variant) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::string input =
            "(declare-const x Real)(declare-const y Real)"
            "(declare-const p Bool)(declare-const q Bool)"
            "(assert (or p q (= x 0)))"
            "(assert (or (not p) q (= x 2)))"
            "(assert (not (and (not p) q (not (= x 3)))))"
            "(assert (=> p (= y 12)))"
            "(assert (or p (= y 10)))";
        if (variant != 1)
            input += variant == 2 ? "(assert (or (not p) (not q) (= x 6)))" :
                                    "(assert (or (not p) (not q) (= x 5)))";
        if (variant == 3)
            input += "(assert (or p q (= x 1)))";
        std::istringstream is(input);
        VERIFY(parse_smt2_commands(cmd, is));
        static_features st(m, true);
        for (expr* f : cmd.assertions())
            st.collect(f);
        VERIFY(st.m_num_guarded_affine_defs == (variant == 0 ? 2u : 1u));
        VERIFY(st.m_num_shared_affine_selectors == (variant == 0 ? 1u : 0u));
        VERIFY(st.m_guarded_features_complete);
        VERIFY(st.m_max_arith_width == 1);
        VERIFY(st.m_num_linear_atoms == st.m_num_short_linear_atoms);
        st.reset();
        VERIFY(st.m_num_linear_atoms == 0 && st.m_num_guarded_affine_defs == 0);
        st.collect(cmd.assertions().size(), cmd.assertions().data());
        VERIFY(st.m_num_guarded_affine_defs == (variant == 0 ? 2u : 1u));
    }
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref sum(x, m);
    for (unsigned i = 0; i < 34; ++i)
        sum = a.mk_add(sum, sum);
    expr_ref atom(a.mk_le(sum, a.mk_real(1)), m);
    static_features st(m, true);
    st.collect(atom);
    VERIFY(st.m_num_linear_atoms == 1 && st.m_max_arith_width == UINT_MAX);
    expr_ref nonlinear(a.mk_mul(x, x), m);
    atom = a.mk_le(nonlinear, a.mk_real(1));
    st.reset();
    st.collect(atom);
    VERIFY(st.m_num_linear_atoms == 0);
}

static std::string lra_feature_fixture() {
    std::ostringstream out;
    out << "(set-logic QF_LRA)(declare-const x Real)(declare-const y Real)";
    for (unsigned i = 0; i < 80; ++i)
        out << "(declare-const b" << i << " Bool)"
            << "(assert (or b" << i << " (<= (+ x y) " << i << ")))";
    return out.str();
}

static void check_lra_feature_config() {
    for (bool proofs : {false, true})
     for (unsigned mode : {0u, 1u, 2u})
      for (unsigned control : {0u, 1u, 2u, 3u}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(lra_feature_fixture());
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_uint("arith.feature_config", mode);
        if (control == 1)
            p.set_bool("arith.bprop_on_pivoted_rows", true);
        if (control == 2)
            p.set_bool("auto_config", false);
        smt_params fp;
        fp.updt_params(p);
        smt::context ctx(m, fp, p);
        for (expr* f : cmd.assertions())
            ctx.assert_expr(f);
        VERIFY(l_true == (control == 3 ? ctx.check() : ctx.setup_and_check()));
        bool applied = mode == 2 && control == 0;
        VERIFY(ctx.get_params().contains("arith.bprop_on_pivoted_rows") == (applied || control == 1));
        if (applied || control == 1)
            VERIFY(ctx.get_params().get_bool("arith.bprop_on_pivoted_rows", true) == (control == 1));
        model_ref md;
        ctx.get_model(md);
        VERIFY(md);
        model_evaluator eval(*md);
        for (expr* f : cmd.assertions()) {
            expr_ref value(m);
            eval(f, value);
            VERIFY(m.is_true(value));
        }
        arith_util a(m);
        expr_ref x(m.mk_const("x", a.mk_real()), m);
        expr_ref zero(a.mk_real(0), m);
        expr_ref lower(a.mk_gt(x, zero), m), upper(a.mk_le(x, zero), m);
        ctx.push();
        ctx.assert_expr(lower);
        ctx.assert_expr(upper);
        VERIFY(l_false == ctx.check());
        if (proofs)
            VERIFY(ctx.get_proof());
        ctx.pop(1);
        VERIFY(l_true == ctx.check());
        expr* assumptions[] = {lower, upper};
        VERIFY(l_false == ctx.check(2, assumptions));
        VERIFY(ctx.get_unsat_core_size() == 2);
        VERIFY(l_true == ctx.check());
    }
    unsigned variant = 0;
    for (char const* extra : {
             "(declare-const z Real)(assert (<= (+ x y z) 1))",
             "(assert (<= (* x y) 1))",
             "(declare-fun f (Real) Real)(assert (<= (f x) 1))"}) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::string input = lra_feature_fixture();
        if (variant++ != 0)
            input.erase(0, std::strlen("(set-logic QF_LRA)"));
        std::istringstream is(input + extra);
        VERIFY(parse_smt2_commands(cmd, is));
        static_features st(m, true);
        st.collect(cmd.assertions().size(), cmd.assertions().data());
        params_ref selected;
        smt_params fp;
        fp.select_lra_feature_config(st, params_ref(), selected);
        VERIFY(!selected.contains("arith.bprop_on_pivoted_rows"));
    }
    params_ref invalid;
    invalid.set_uint("arith.feature_config", 3);
    smt_params fp;
    bool caught = false;
    try {
        fp.updt_params(invalid);
    }
    catch (default_exception const&) {
        caught = true;
    }
    VERIFY(caught);
}

static void check_sparse_lra_pivots() {
    for (unsigned strategy : {0u, 1u}) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-const x Real)(declare-const y Real)(declare-const z Real)"
            "(assert (>= x 0))(assert (>= y 0))(assert (>= z 0))"
            "(assert (< (+ (* 2 x) y) 9))"
            "(assert (> (+ x (* 3 y) z) 12))"
            "(assert (< (+ x y z) 6))");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_uint("arith.lp_pivot_strategy", strategy);
        p.set_bool("smt", true);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* f : cmd.assertions())
            slv->assert_expr(f);
        VERIFY(l_true == slv->check_sat(0, nullptr));
        model_ref md;
        slv->get_model(md);
        model_evaluator eval(*md);
        for (expr* f : cmd.assertions()) {
            expr_ref value(m);
            eval(f, value);
            VERIFY(m.is_true(value));
        }
        arith_util a(m);
        app_ref y(m.mk_const("y", a.mk_real()), m);
        expr_ref bound(a.mk_le(y, a.mk_real(1)), m);
        slv->push();
        slv->assert_expr(bound);
        VERIFY(l_false == slv->check_sat(0, nullptr));
        slv->pop(1);
        VERIFY(l_true == slv->check_sat(0, nullptr));
    }
}

void tst_smt_context()
{
    check_bounded_clause_flattening();
    check_extended_lra_features();
    check_lra_feature_config();
    check_sparse_lra_pivots();
    check_monotone_reals();
    check_monotone_simplifier();
    check_real_power_bounds();
    check_symbolic_regex_substring();

    smt_params params;

    ast_manager m;
    reg_decl_plugins(m);

    smt::context ctx(m, params);

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-const a (Array Int Int))\n"
            "(declare-const b (Array Int Int))\n"
            "(declare-const i Int)\n"
            "(assert (distinct a b))\n"
            "(assert (= (select a i) 0))\n"
            "(assert (= (select b i) 1))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        smt::context qctx(m, params);
        for (expr* assertion : cmd.assertions())
            qctx.assert_expr(assertion);
        VERIFY(l_true == qctx.check());
        statistics st;
        qctx.collect_statistics(st);
        char const* array_ext_axiom_stat = "array ext ax";
        unsigned num_array_ext_axioms = 0;
        VERIFY(get_uint_stat(st, array_ext_axiom_stat, num_array_ext_axioms));
        VERIFY(num_array_ext_axioms > 0);
    }

    app_ref a1(m.mk_const(symbol("a"), m.mk_bool_sort()), m);
    app_ref b1(m.mk_const(symbol("b"), m.mk_bool_sort()), m);
    app_ref c1(m.mk_const(symbol("c"), m.mk_bool_sort()), m);
    app_ref na1(m.mk_not(a1), m);
    ctx.assert_expr(na1);

    app_ref b_or_c(m.mk_or(c1.get(), b1.get()), m);
    ctx.assert_expr(b_or_c);

    {
        app_ref nc(m.mk_not(c1), m);
        ptr_vector<expr> assumptions;
        assumptions.push_back(nc.get());

        ctx.check(assumptions.size(), assumptions.data());
    }

    ctx.check();

    {
        arith_util a(m);
        expr_ref x(m.mk_var(2, a.mk_int()), m);
        expr_ref x4(m.mk_var(1, a.mk_int()), m);
        expr_ref y(m.mk_var(0, a.mk_int()), m);
        expr_ref zero(a.mk_int(0), m);
        expr_ref two(a.mk_int(2), m);
        expr_ref_vector conjs(m);
        conjs.push_back(a.mk_gt(x, y));
        conjs.push_back(a.mk_gt(zero, x4));
        conjs.push_back(a.mk_gt(zero, a.mk_uminus(y)));
        conjs.push_back(a.mk_lt(zero, a.mk_uminus(a.mk_mul(two, y))));
        expr_ref body(m.mk_and(conjs), m);

        sort* y_sort = a.mk_int();
        symbol y_name("y");
        body = m.mk_exists(1, &y_sort, &y_name, body);

        sort* sorts[2] = { a.mk_int(), a.mk_int() };
        symbol names[2] = { symbol("x"), symbol("x4") };
        expr_ref q(m.mk_forall(2, sorts, names, body), m);

        smt::context qctx(m, params);
        qctx.assert_expr(q);
        VERIFY(l_false == qctx.check());
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(set-logic ALL)\n"
            "(declare-datatypes ((Node 0)) (((base) (wrapped (payload Float32)))))\n"
            "(define-fun measure ((node Node) (fallback Int)) Int\n"
            "  (ite ((_ is wrapped) node) 1 fallback))\n"
            "(assert\n"
            "  (forall ((other Node))\n"
            "    (= (measure base 0)\n"
            "       (measure other 0))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        smt::context qctx(m, params);
        for (expr* a : cmd.assertions())
            qctx.assert_expr(a);
        VERIFY(l_false == qctx.check());
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-sort Element)\n"
            "(declare-sort Index)\n"
            "(declare-fun e6 () Element)\n"
            "(declare-fun i6 () Index)\n"
            "(declare-fun i2 () Index)\n"
            "(declare-fun i4 () Index)\n"
            "(declare-fun e9 () Element)\n"
            "(declare-fun i8 () Index)\n"
            "(declare-fun i10 () Index)\n"
            "(declare-fun a1 () (Array Index Element))\n"
            "(assert (exists ((i3 Index)) (and (= i3 i8) (= i6 i10) "
            "(not (= (store (store (store a1 i4 e9) i2 e6) i10 e6) "
            "(store (store (store a1 i6 e9) i8 e6) i10 e9))))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("rewriter.expand_nested_stores", true);
        tactic_ref t = mk_lira_tactic(m, p);
        goal_ref g = alloc(goal, m, false, true, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason_unknown;
        VERIFY(l_true == check_sat(*t, g, md, labels, pr, core, reason_unknown));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(set-logic ALL)\n"
            "(declare-const y (_ BitVec 1))\n"
            "(assert\n"
            "  (exists ((V (_ BitVec 8)))\n"
            "    (= (_ bv1 8)\n"
            "       ((_ extract 7 0)\n"
            "         (bvlshr\n"
            "           (concat V (_ bv0 8))\n"
            "           ((_ zero_extend 15) y))))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("smt", true);
        p.set_uint("bv.solver", 2);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* a : cmd.assertions())
            slv->assert_expr(a);
        VERIFY(l_false == slv->check_sat(0, nullptr));
    }

    {
        ast_manager m2;
        reg_decl_plugins(m2);
        cmd_context cmd(false, &m2);
        std::istringstream is(
            "(set-logic ALL)\n"
            "(assert\n"
            "  (exists ((V (_ BitVec 1)))\n"
            "    (= (_ bv0 1) (bvashr (_ bv1 1) V))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("smt", true);
        p.set_uint("bv.solver", 2);
        ref<solver> slv = mk_smt2_solver(m2, p, symbol::null);
        for (expr* a : cmd.assertions())
            slv->assert_expr(a);
        VERIFY(l_false == slv->check_sat(0, nullptr));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-const x (_ FloatingPoint 5 11))\n"
            "(declare-const y (_ FloatingPoint 5 11))\n"
            "(declare-const xb (_ BitVec 16))\n"
            "(declare-const yb (_ BitVec 16))\n"
            "(assert (= x ((_ to_fp 5 11) xb)))\n"
            "(assert (= y ((_ to_fp 5 11) yb)))\n"
            "(assert (= xb #b1000001111000111))\n"
            "(assert (= yb #b0011110111000000))\n"
            "(assert (not (= ((_ fp.to_ieee_bv 16) (fp.fma RNE x y x)) #x889b)))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        goal_ref g = alloc(goal, m, false, true, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        tactic_ref t = and_then(mk_fpa2bv_tactic(m), mk_simplify_tactic(m), mk_bit_blaster_tactic(m), mk_smt_tactic(m));
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason_unknown;
        VERIFY(l_false == check_sat(*t, g, md, labels, pr, core, reason_unknown));
    }

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-fun length ((Array Int Int)) Int)\n"
            "(declare-const lindx2 (Array Int Int))\n"
            "(declare-const indx1 (Array Int Int))\n"
            "(declare-const orig_findx1 (Array Int Int))\n"
            "(assert (and\n"
            "  (forall ((i Int) (j Int))\n"
            "    (let ((a!1 (and (<= 0 i)\n"
            "                    (<= i (- (length indx1) 1))\n"
            "                    (<= 0 j)\n"
            "                    (<= j (- (length orig_findx1) 1))\n"
            "                    (= i j))))\n"
            "      (=> a!1 (= (select indx1 i) (select orig_findx1 j)))))\n"
            "  (= (length lindx2) 11)\n"
            "  (forall ((i Int)) (=> (and (<= 3 i) (<= i 25)) (= (select indx1 i) (- 1))))))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        cmd.set_solver_factory(mk_smt_strategic_solver_factory());
        cmd.check_sat(0, nullptr);
        VERIFY(cmd.cs_state() == cmd_context::css_sat);
    }

    check_sat_smt_recfun(
        "(declare-sort I 0)\n"
        "(declare-fun isI (I) Bool)\n"
        "(declare-datatype L1 ((n1) (c1 (h1 I) (t1 L1))))\n"
        "(declare-datatype L2 ((n2) (c2 (h2 L1) (t2 L2))))\n"
        "(define-fun-rec isL1 ((x L1)) Bool (ite (is-c1 x) (and (isI (h1 x)) (isL1 (t1 x))) true))\n"
        "(declare-fun isL2 (L2) Bool)\n"
        "(define-fun-rec isL2_rec ((x L2)) Bool (ite (is-c2 x) (and (isL1 (h2 x)) (isL2_rec (t2 x))) true))\n"
        "(assert (forall ((x L2)) (! (= (isL2_rec x) (isL2 x)) :pattern ((isL2 x)))))\n");

    // Regression: a non-Boolean (Int) recursive function whose recursive step contains a
    // real quantifier nested inside an `ite` used to be misreified as a Boolean fresh
    // constant (mk_bool_sort() instead of rhs->get_sort()), producing an ill-typed
    // definitional axiom and a spurious `unsat`. t(1) = -1 is satisfiable: pick s == 0.
    check_sat_smt_recfun(
        "(declare-fun s (Int) Int)\n"
        "(define-fun-rec t ((p Int)) Int\n"
        "  (ite (<= p 0) 0 (+ (t (- p 1)) (ite (exists ((y Int)) (= (s y) (- p 1))) (- 1) 0))))\n"
        "(assert (= (t 1) (- 1)))\n");

    check_sat_smt_model(
        "(declare-sort H 0)\n"
        "(declare-const h H)\n"
        "(assert (partial-order h h))\n");

    {
        cmd_context cmd(false, &m);
        cmd.set_solver_factory(mk_smt_strategic_solver_factory());
        cmd.params().set_rlimit(1000000);
        std::istringstream is(
            "(set-option :smt.distribute_forall true)\n"
            "(declare-fun a () (Array (_ BitVec 11) (_ BitVec 8)))\n"
            "(declare-fun b () (Array (_ BitVec 11) (_ BitVec 8)))\n"
            "(declare-fun c () (Array (_ BitVec 11) (_ BitVec 16)))\n"
            "(declare-fun d () (Array (_ BitVec 11) (_ BitVec 8)))\n"
            "(declare-fun e () (Array (_ BitVec 11) (_ BitVec 8)))\n"
            "(declare-fun f () (Array (_ BitVec 11) (_ BitVec 8)))\n"
            "(declare-fun g () (Array (_ BitVec 11) (_ BitVec 8)))\n"
            "(declare-fun h () (Array (_ BitVec 11) (_ BitVec 16)))\n"
            "(declare-fun k () (Array (_ BitVec 11) (_ BitVec 16)))\n"
            "(assert (forall ((i (_ BitVec 11)))\n"
            "  (and (= (select e i) (select b #b00000000000))\n"
            "       (= (select f i) (select a i))\n"
            "       (= (select g i) (select d i))\n"
            "       (= (select h i) (select c #b00000000000))\n"
            "       (= (select k i) (select h i)))))\n"
            "(assert (= (select d #b00000000000) #x00))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        cmd.check_sat(0, nullptr);
        VERIFY(cmd.cs_state() == cmd_context::css_sat);
    }

    {
        arith_util a(m);
        sort* s = a.mk_int();
        symbol name("x");
        expr_ref x(m.mk_var(0, s), m);
        expr_ref first(m.mk_eq(x, a.mk_int(0)), m);
        expr_ref second(m.mk_eq(x, a.mk_int(1)), m);
        expr_ref lhs(m.mk_not(first), m);
        expr_ref rhs1(m.mk_not(second), m);
        expr_ref body(m.mk_not(m.mk_or(lhs, rhs1)), m);
        quantifier_ref q(m.mk_forall(1, &s, &name, body), m);
        distribute_forall distribute(m);
        expr_ref result(m);
        distribute(q, result);
        VERIFY(result != q && !is_quantifier(result));

        base_dependent_expr_state state(m);
        state.add(dependent_expr(m, q, nullptr, nullptr));
        distribute_forall_simplifier simplifier(m, params_ref(), state);
        simplifier.reduce();
        VERIFY(state[0].fml() != q);

        func_decl_ref f(m.mk_fresh_func_decl("f", 1, &s, s), m);
        app_ref term(m.mk_app(f.get(), x.get()), m);
        app_ref pattern(m.mk_pattern(term), m);
        expr* pat = pattern;
        quantifier_ref patterned(m.mk_forall(1, &s, &name, body, 0, symbol::null,
                                            symbol::null, 1, &pat), m);
        distribute(patterned, result);
        VERIFY(result == patterned);
        state.add(dependent_expr(m, patterned, nullptr, nullptr));
        simplifier.reduce();
        VERIFY(state[1].fml() == patterned);

        expr* no_pat = term;
        quantifier_ref no_pattern(m.mk_forall(1, &s, &name, body, 0, symbol::null,
                                             symbol::null, 0, nullptr, 1, &no_pat), m);
        distribute(no_pattern, result);
        VERIFY(result == no_pattern);
        state.add(dependent_expr(m, no_pattern, nullptr, nullptr));
        simplifier.reduce();
        VERIFY(state[2].fml() == no_pattern);
    }
    // Regression (issue #10981): two extensionally equal arrays over a Bit-Vector 1
    // (2-element) domain, built as stores over `const` arrays with different default
    // values, used to be reported unsat due to a reversed default/select pairing (and
    // a missing diagonal axiom) in the small-domain default-store axiom.
    check_sat_smt_model(
        "(assert (= (store ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b0) #b0 #b1)\n"
        "           (store ((as const (Array (_ BitVec 1) (_ BitVec 1))) #b1) #b1 #b0)))\n");

    // Regression (issue #11069): an uninterpreted array domain may be a singleton.
    char const* const_array =
        "(declare-sort S 0)\n"
        "(declare-const s S)\n"
        "(assert (= (store ((as const (Array S (_ BitVec 8))) #x00) s #x01)\n"
        "           ((as const (Array S (_ BitVec 8))) #x01)))\n";
    check_array_domain(const_array, l_true);
    std::string two_elements = std::string(const_array) +
        "(declare-const t S)\n(assert (distinct s t))\n";
    check_array_domain(two_elements.c_str(), l_false);

    char const* quantified_arrays =
        "(declare-sort S 0)\n"
        "(declare-const s S)\n"
        "(declare-const a (Array S (_ BitVec 2)))\n"
        "(declare-const b (Array S (_ BitVec 2)))\n"
        "(assert (forall ((x S)) (= (select a x) #b00)))\n"
        "(assert (forall ((x S)) (= (select b x) #b01)))\n"
        "(assert (= (store a s #b01) (store b s #b01)))\n";
    check_array_domain(quantified_arrays, l_true);
    two_elements = std::string(quantified_arrays) +
        "(declare-const t S)\n(assert (distinct s t))\n";
    check_array_domain(two_elements.c_str(), l_false);

    check_array_domain(
        "(declare-datatype S ((s)))\n"
        "(assert (= (store ((as const (Array S (_ BitVec 8))) #x00) s #x01)\n"
        "           ((as const (Array S (_ BitVec 8))) #x01)))\n", l_true);
    check_array_domain(
        "(declare-const s Int)\n"
        "(assert (= (store ((as const (Array Int (_ BitVec 8))) #x00) s #x01)\n"
        "           ((as const (Array Int (_ BitVec 8))) #x01)))\n", l_false);
    check_array_domain(
        "(declare-sort S 0)\n"
        "(declare-const s S)\n"
        "(assert (= (store (store ((as const (Array S Bool (_ BitVec 8))) #x00)\n"
        "                         s false #x01) s true #x01)\n"
        "           ((as const (Array S Bool (_ BitVec 8))) #x01)))\n", l_true);
    check_array_domain(
        "(declare-sort S 0)\n"
        "(declare-const s S)\n"
        "(assert (= (store ((as const (Array S Int (_ BitVec 8))) #x00) s 0 #x01)\n"
        "           ((as const (Array S Int (_ BitVec 8))) #x01)))\n", l_false);
    check_array_domain(
        "(declare-sort S 0)\n"
        "(assert (forall ((s S))\n"
        "  (= (store ((as const (Array S (_ BitVec 8))) #x00) s #x01)\n"
        "     ((as const (Array S (_ BitVec 8))) #x01))))\n", l_true);

    // Regression (issue #11156): MBQI must not give up on array model values over uninterpreted sorts.
    check_array_domain(
        "(declare-datatypes ((x5 0)) (((x3) (x4))))\n"
        "(declare-sort x31)\n"
        "(declare-datatypes ((x36 0)) (((x35))))\n"
        "(declare-sort x6)\n"
        "(declare-datatypes ((x29 0)) (((x28 (x23 x5)))))\n"
        "(declare-sort x30)\n"
        "(declare-datatypes ((x45 0)) (((x44 (x38 x5) (x39 x6) (x40 x6) (x41 x6) (x42 x36) (x43 x31)))))\n"
        "(declare-fun x63 () x30)\n"
        "(declare-fun x70 () (Array x30 x45))\n"
        "(declare-fun x68 () (Array x30 x45))\n"
        "(declare-fun z3name!0 (x30) x29)\n"
        "(declare-fun l51 () Bool)\n"
        "(assert (= l51 (forall ((x73 x30)) (or (= x3 (x23 (z3name!0 x73))) (= x3 (x38 (select x70 x73)))))))\n"
        "(assert (not (= x70 (store x70 x63 (x44 x4 (x39 (select x70 x63)) (x40 (select x70 x63)) (x41 (select x70 x63)) (x42 (select x70 x63)) (x43 (select x70 x63)))))))\n"
        "(assert (not (= x70 x68)))\n"
        "(assert l51)\n", l_true);

    // Regression (issue #10996, bug A): the equality atom (= x (ite p x y)) is first
    // internalized in a gate context by the ite-term axioms, and must still be merged
    // with true/false when it occurs as an argument of an uninterpreted function.
    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-sort U 0)\n"
            "(declare-const x U)\n"
            "(declare-const y U)\n"
            "(declare-const p Bool)\n"
            "(declare-fun g (Bool) Bool)\n"
            "(assert (distinct (g (= x (ite p x y))) (g true)))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        smt::context qctx(m, params);
        for (expr* a : cmd.assertions())
            qctx.assert_expr(a);
        expr_ref p(m.mk_const(symbol("p"), m.mk_bool_sort()), m);
        expr* assumption = p;
        VERIFY(l_false == qctx.check(1, &assumption));
    }

    // Regression (issue #10996, bug B): an n-ary distinct assigned while it is
    // internalized must propagate its value to the e-graph.
    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-sort U 0)\n"
            "(declare-const x U)\n"
            "(declare-const c U)\n"
            "(declare-fun h (U) U)\n"
            "(declare-fun g (Bool) Bool)\n"
            "(assert (= (h x) x))\n"
            "(assert (distinct (g (distinct (h (h x)) c x)) (g false)))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        smt::context qctx(m, params);
        for (expr* a : cmd.assertions())
            qctx.assert_expr(a);
        VERIFY(l_false == qctx.check());
    }
}

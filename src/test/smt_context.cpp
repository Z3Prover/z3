
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "smt/smt_context.h"
#include "math/lp/lar_solver.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "cmd_context/cmd_context.h"
#include "parsers/smt2/smt2parser.h"
#include "ast/rewriter/distribute_forall.h"
#include "ast/simplifiers/distribute_forall.h"
#include "solver/solver.h"
#include "model/model.h"
#include "tactic/goal.h"
#include "tactic/tactic.h"
#include "tactic/tactical.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/fpa/fpa2bv_tactic.h"
#include "tactic/smtlogics/quant_tactics.h"
#include "tactic/smtlogics/smt_tactic.h"
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

static void check_recfun_rlimit(char const* input, unsigned rlimit) {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context cmd(false, &m);
    cmd.set_solver_factory(mk_smt_strategic_solver_factory());
    cmd.params().set_rlimit(rlimit);
    std::ostringstream out;
    cmd.set_regular_stream(out);
    std::istringstream is(input);
    VERIFY(parse_smt2_commands(cmd, is));
    cmd.check_sat(0, nullptr);
    VERIFY(cmd.cs_state() == cmd_context::css_unknown);
    VERIFY(out.str() == "unknown\n");
}

static void check_recfun_rlimits() {
    for (char const* input : {
            "(define-fun-rec f ((x Int)) Int (f x))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f ((x Int)) Int (+ 1 (f (+ x 1))))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f () Int (+ 1 f))\n"
            "(assert (= f 1))\n",
            "(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int))"
            " ((g x) (f x)))\n"
            "(assert (= (f 0) 1))\n"}) {
        check_recfun_rlimit(input, 1);
    }
    check_recfun_rlimit(
        "(define-fun-rec f ((x Int)) Int (+ 1 (f (+ x 1))))\n"
        "(assert (= (f 0) 1))\n", 1000);
}

static bool get_uint_stat(statistics const& st, char const* key, unsigned& value) {
    for (unsigned i = 0; i < st.size(); ++i)
        if (st.is_uint(i) && !strcmp(st.get_key(i), key)) {
            value = st.get_uint_value(i);
            return true;
        }
    return false;
}

static void check_arithmetic_propagation_cancellation() {
    struct propagation_context : smt::context {
        using smt::context::context;
        using smt::context::propagate;
    };
    for (bool cancel : {false, true}) {
        ast_manager m;
        reg_decl_plugins(m);
        smt_params params;
        propagation_context ctx(m, params);
        ctx.push();
        VERIFY(ctx.at_base_level());
        arith_util a(m);
        expr_ref x(m.mk_const("x", a.mk_int()), m);
        expr_ref y(m.mk_const("y", a.mk_int()), m);
        expr_ref sum(a.mk_add(x, y), m);
        expr_ref one(a.mk_int(1), m);
        expr_ref bound(a.mk_ge(sum, one), m);
        ctx.internalize(bound, false);
        ctx.mark_as_relevant(bound.get());
        ctx.assign(ctx.get_literal(bound), smt::b_justification::mk_axiom());
        {
            scoped_rlimit limit(m.limit(), cancel ? 0 : 1);
            if (cancel)
                m.limit().cancel();
            VERIFY(ctx.propagate());
            statistics st;
            ctx.collect_statistics(st);
            unsigned pivots = 0;
            get_uint_stat(st, "arith-pivots", pivots);
            VERIFY(pivots == 0);
        }
        VERIFY(ctx.check() == l_true);
        statistics st;
        ctx.collect_statistics(st);
        unsigned pivots = 0;
        VERIFY(get_uint_stat(st, "arith-pivots", pivots) && pivots > 0);
        ctx.push();
        ctx.assert_expr(m.mk_not(bound));
        VERIFY(ctx.check() == l_false);
        ctx.pop(1);
        VERIFY(ctx.check() == l_true);
        ctx.pop(1);
        VERIFY(ctx.check() == l_true);
    }
}

static void check_lp_cancellation_recovery() {
    struct resource_limit : lp::lp_resource_limit {
        reslimit limit;
        lp::statistics const* stats = nullptr;
        bool enabled = true;
        bool cancel_after_pivot = false;
        bool pivot_checked = false;
        bool get_cancel_flag() override {
            if (enabled && cancel_after_pivot && stats->m_pivots > 0)
                limit.cancel();
            return !limit.inc();
        }
        bool get_cancel_flag(unsigned cost) override {
            pivot_checked = true;
            if (enabled && !cancel_after_pivot)
                limit.cancel();
            return !limit.inc(cost);
        }
    };
    for (bool after_pivot : {false, true}) {
        resource_limit resource;
        lp::lar_solver solver;
        resource.stats = &solver.settings().stats();
        resource.cancel_after_pivot = after_pivot;
        solver.settings().set_resource_limit(resource);
        auto x = solver.add_var(0, true);
        auto y = solver.add_var(1, true);
        vector<std::pair<lp::mpq, lp::lpvar>> coeffs;
        coeffs.push_back({lp::mpq(1), x});
        coeffs.push_back({lp::mpq(1), y});
        auto term = solver.add_term(coeffs, 2);
        solver.add_var_bound(term, lp::GE, lp::mpq(1));
        {
            scoped_rlimit limit(resource.limit, 0);
            VERIFY(solver.find_feasible_solution() == lp::lp_status::CANCELLED);
            VERIFY(resource.pivot_checked);
            VERIFY(solver.settings().stats().m_pivots == (after_pivot ? 1u : 0u));
            VERIFY(solver.ax_is_correct());
        }
        resource.enabled = false;
        VERIFY(solver.find_feasible_solution() == lp::lp_status::OPTIMAL);
        VERIFY(solver.ax_is_correct());
        VERIFY(solver.column_is_feasible(term));
    }
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

static void check_stored_lambdas() {
    auto check = [](char const* input, lbool expected) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        cmd.set_solver_factory(mk_smt_strategic_solver_factory());
        std::ostringstream out;
        cmd.set_regular_stream(out);
        std::istringstream is(input);
        VERIFY(parse_smt2_commands(cmd, is));
        cmd.check_sat(0, nullptr);
        VERIFY(out.str() == (expected == l_false ? "unsat\n" : "sat\n"));
    };
    // Regression for issue #11267: stores must preserve lambda semantics.
    for (char const* input : {
        "(assert (= (store (lambda ((x Int)) x) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(assert (= (store ((as const (Array Int Int)) 3) 7 0)\n"
        "           (store (lambda ((x Int)) x) 7 0)))\n",
        "(assert (= (store (lambda ((x Int)) (+ x 1)) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(assert (= (store (lambda ((x Int)) x) 7 0)\n"
        "           (store (lambda ((x Int)) 3) 7 0)))\n",
        "(declare-const a (Array Int Int))\n"
        "(assert (= a (store (lambda ((x Int)) x) 7 0)))\n"
        "(assert (= a (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(declare-const a (Array Int Int))\n"
        "(assert (= (store a 7 0) (store ((as const (Array Int Int)) 3) 7 0)))\n"
        "(assert (= a (lambda ((x Int)) x)))\n",
        "(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))\n"
        "(declare-const w W)\n"
        "(assert (= w (mk (store (lambda ((x Int)) x) 7 0))))\n"
        "(assert (= w (mk (store ((as const (Array Int Int)) 3) 7 0))))\n",
        "(assert (= (store (store (lambda ((x Int)) x) 7 0) 8 0)\n"
        "           (store (store ((as const (Array Int Int)) 3) 7 0) 8 0)))\n",
        "(assert (= (store (lambda ((x Int) (y Int)) (+ x y)) 7 8 0)\n"
        "           (store ((as const (Array Int Int Int)) 3) 7 8 0)))\n",
        "(assert (= (store ((_ map (+ (Int Int) Int)) (lambda ((x Int)) x)\n"
        "                   ((as const (Array Int Int)) 1)) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n"}) {
        check(input, l_false);
    }
    check(
        "(assert (= (store (lambda ((x Int)) (ite (= x 7) 1 3)) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n", l_true);
    check(
        "(assert (= (store (lambda ((x Bool)) (ite x 1 3)) true 0)\n"
        "           (store ((as const (Array Bool Int)) 3) true 0)))\n", l_true);
}

static void check_sat_array_lambdas() {
    for (char const* input : {
        "(assert (= (store (lambda ((x Int)) x) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(assert (= (store (lambda ((x Int)) x) 7 0)\n"
        "           (store (lambda ((x Int)) (+ x 1)) 7 0)))\n",
        "(declare-const a (Array Int Int))\n"
        "(assert (= (store a 7 0) (store ((as const (Array Int Int)) 3) 7 0)))\n"
        "(assert (= a (lambda ((x Int)) x)))\n",
        "(declare-datatypes ((W 0)) (((mk (arr (Array Int Int))))))\n"
        "(declare-const w W)\n"
        "(assert (= w (mk (store (lambda ((x Int)) x) 7 0))))\n"
        "(assert (= w (mk (store ((as const (Array Int Int)) 3) 7 0))))\n",
        "(assert (= (store (store (lambda ((x Int)) x) 7 0) 8 0)\n"
        "           (store (store ((as const (Array Int Int)) 3) 7 0) 8 0)))\n",
        "(assert (= (store ((_ map (+ (Int Int) Int)) (lambda ((x Int)) x)\n"
        "                   ((as const (Array Int Int)) 1)) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(declare-const a (Array Int Int))\n"
        "(assert (= a (store (lambda ((x Int)) x) 7 0)))\n"
        "(assert (= a (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(declare-fun f (Int) Int)\n"
        "(assert (= (f 0) 0))\n"
        "(assert (= (store (_ as-array f) 7 0)\n"
        "           (store ((as const (Array Int Int)) 3) 7 0)))\n",
        "(declare-fun f (Int) Int)\n"
        "(declare-const a (Array Int Int))\n"
        "(assert (= (f 0) 0))\n"
        "(assert (= a (store (_ as-array f) 7 0)))\n"
        "(assert (= a (store ((as const (Array Int Int)) 3) 7 0)))\n"}) {
        for (bool smt : {false, true}) {
            ast_manager m;
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream is(input);
            VERIFY(parse_smt2_commands(cmd, is));
            params_ref p;
            p.set_bool("smt", smt);
            p.set_bool("euf", !smt);
            ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
            for (unsigned i = 0; i < 2; ++i) {
                slv->push();
                for (expr* a : cmd.assertions())
                    slv->assert_expr(a);
                // These backends may give up on lambdas, but must not report sat.
                VERIFY(l_true != slv->check_sat(0, nullptr));
                slv->pop(1);
                VERIFY(l_true == slv->check_sat(0, nullptr));
            }
        }
    }
}

static void check_expand_store_eq() {
    struct {
        char const* input;
        lbool expected;
    } cases[] = {
        {"(assert (= (store ((as const (Array Bool Int)) 0) false 1)\n"
         "           (store ((as const (Array Bool Int)) 1) true 0)))\n",
         l_true},
        {"(assert (= (store (store ((as const (Array Bool Bool Int)) 0)\n"
         "                         false false 1) false true 1)\n"
         "           (store (store ((as const (Array Bool Bool Int)) 1)\n"
         "                         true false 0) true true 0)))\n",
         l_true},
        {"(assert (= (store ((as const (Array (_ BitVec 2) Int)) 0) #b00 1)\n"
         "           (store ((as const (Array (_ BitVec 2) Int)) 1) #b01 0)))\n",
         l_false},
        {"(assert (= (store ((as const (Array Int Int)) 0) 0 1)\n"
         "           (store ((as const (Array Int Int)) 1) 1 0)))\n",
         l_false},
        {"(declare-const a (Array Bool Int))\n"
         "(assert (= (store a false 0) (store a false 1)))\n",
         l_false}
    };
    for (auto const& test : cases) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(test.input);
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("expand_store_eq", true);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* assertion : cmd.assertions())
            slv->assert_expr(assertion);
        VERIFY(test.expected == slv->check_sat(0, nullptr));
    }
}

static void check_array_index_dependencies() {
    for (char const* input : {
        "(declare-datatypes () ((D a b c)))\n"
        "(declare-const x D)\n"
        "(assert (= ((as const (Array D Bool)) false)\n"
        "  (store (store (store ((as const (Array D Bool)) true)\n"
        "                      a false) b false) x false)))\n",
        "(declare-datatypes () ((D a b c)))\n"
        "(declare-const x D)\n"
        "(declare-const y Bool)\n"
        "(assert (= ((as const (Array D Bool Bool)) false)\n"
        "  (store (store (store (store (store (store\n"
        "    ((as const (Array D Bool Bool)) true)\n"
        "    a false false) a true false) b false false) b true false) c false false) x y false)))\n"}) {
        for (unsigned backend = 0; backend < 3; ++backend) {
            bool sat_smt = backend == 2;
            auto mode = backend == 1 ? PGM_ENABLED : PGM_DISABLED;
            ast_manager m(mode);
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream is(input);
            VERIFY(parse_smt2_commands(cmd, is));
            params_ref p;
            p.set_bool("smt", sat_smt);
            p.set_bool("unsat_core", true);
            auto make_solver = [&]() {
                ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
                for (expr* assertion : cmd.assertions())
                    slv->assert_expr(assertion);
                return slv;
            };
            ref<solver> slv = make_solver();
            VERIFY(l_true == slv->check_sat(0, nullptr));

            expr_ref_vector assumptions(m);
            assumptions.push_back(m.mk_eq(m.mk_const(cmd.find_func_decl(symbol("x"))),
                                          m.mk_const(cmd.find_func_decl(symbol("a")))));
            if (cmd.is_func_decl(symbol("y")))
                assumptions.push_back(m.mk_not(m.mk_const(cmd.find_func_decl(symbol("y")))));

            for (expr* assumption : assumptions) {
                slv = make_solver();
                VERIFY(l_false == slv->check_sat(1, &assumption));
                expr_ref_vector core(m);
                slv->get_unsat_core(core);
                // The array equality is satisfiable, so the conflict must
                // depend on the assumption about the index component.
                VERIFY(core.size() == 1);
                VERIFY(core[0] == assumption);
                VERIFY(l_true == slv->check_sat(0, nullptr));
            }
        }
    }
}

static void check_singleton_array_defaults() {
    struct {
        char const* input;
        lbool expected;
    } cases[] = {
        {"(declare-datatypes () ((D d)))\n"
         "(assert (= (default (store ((as const (Array D Int)) 0) d 1)) 1))\n",
         l_true},
        {"(declare-datatypes () ((D d)))\n"
         "(assert (= (default (store ((as const (Array D Int)) 0) d 1)) 0))\n",
         l_false},
        {"(declare-datatypes () ((D d) (E e)))\n"
         "(declare-const v Int)\n"
         "(assert (distinct v 0))\n"
         "(assert (= (default (store ((as const (Array D E Int)) 0) d e v)) v))\n",
         l_true},
        {"(declare-datatypes () ((D d) (E e)))\n"
         "(declare-const v Int)\n"
         "(assert (distinct v 0))\n"
         "(assert (= (default (store ((as const (Array D E Int)) 0) d e v)) 0))\n",
         l_false}
    };
    for (auto const& test : cases) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(test.input);
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("smt", true);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* assertion : cmd.assertions())
            slv->assert_expr(assertion);
        VERIFY(test.expected == slv->check_sat(0, nullptr));
    }
}

static void check_singleton_array_range_cardinality() {
    char const* declarations =
        "(declare-datatypes () ((One one)))\n"
        "(declare-datatypes ((Box 1))\n"
        "  ((par (T) ((box (value (Array T One)))))))\n"
        "(declare-const b (Box Int))\n";
    std::string equality =
        "(= (store ((as const (Array (Box Int) Bool)) false) b true)\n"
        "   ((as const (Array (Box Int) Bool)) true))";
    struct {
        bool sat_smt;
        bool negate;
    } cases[] = {{false, false}, {false, true}, {true, false}, {true, true}};
    for (auto const& test : cases) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::string input = std::string(declarations) + "(assert " +
            (test.negate ? "(not " + equality + ")" : equality) + ")\n";
        std::istringstream is(input);
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_bool("smt", test.sat_smt);
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* assertion : cmd.assertions())
            slv->assert_expr(assertion);
        VERIFY((test.negate ? l_false : l_true) == slv->check_sat(0, nullptr));
    }
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

static void check_nonlinear_to_int() {
    for (char const* input : {
            "(declare-fun N () Int)\n"
            "(assert (<= 1 N))\n"
            "(assert (<= N 3))\n"
            "(assert (> (- (* (to_real N) (to_real N))"
            " (* 2.0 (to_real (to_int (/ (* (to_real N) (to_real N)) 2.0))))) 1.0))\n",
            "(declare-fun N () Int)\n"
            "(assert (<= 4.0 (to_real N)))\n"
            "(assert (<= (to_real N) 16.0))\n"
            "(assert (> (- (* -4.0 (* (to_real N) (to_real N)))"
            " (* 128.0 (to_real (to_int (/ (* -4.0 (* (to_real N) (to_real N))) 128.0))))) 124.0))\n"}) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(input);
        VERIFY(parse_smt2_commands(cmd, is));
        ref<solver> slv = mk_smt2_solver(m, params_ref(), symbol::null);
        for (expr* assertion : cmd.assertions())
            slv->assert_expr(assertion);
        VERIFY(l_false == slv->check_sat(0, nullptr));

        slv = mk_smt2_solver(m, params_ref(), symbol::null);
        slv->assert_expr(cmd.assertions()[0]);
        slv->assert_expr(cmd.assertions()[1]);
        expr_ref complement(m.mk_not(cmd.assertions()[2]), m);
        slv->assert_expr(complement);
        VERIFY(l_true == slv->check_sat(0, nullptr));
        model_ref model;
        slv->get_model(model);
        expr_ref value(m);
        VERIFY(model->eval_expr(complement, value));
        VERIFY(m.is_true(value));
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

static void check_special_relation_logic() {
    for (char const* logic : {"UFDTLIA", "ALL", ""}) {
        for (bool external : {false, true}) {
            for (bool initialized : {false, true}) {
                ast_manager m;
                reg_decl_plugins(m);
                cmd_context cmd(false, external ? &m : nullptr);
                if (initialized)
                    cmd.m();
                bool restricted = !strcmp(logic, "UFDTLIA");
                std::ostringstream input;
                if (*logic)
                    input << "(set-logic " << logic << ")\n";
                input << "(declare-sort U 0)\n"
                      << "(declare-const h U)\n";
                if (restricted)
                    input << "(declare-fun partial-order (U U) Bool)\n";
                input << "(assert (partial-order h h))\n";
                std::istringstream is(input.str());
                ENSURE(parse_smt2_commands(cmd, is));
                ENSURE(cmd.assertions().size() == 1);
                auto* assertion = to_app(cmd.assertions().get(0));
                ENSURE(assertion->get_family_id() ==
                       (restricted ? null_family_id : cmd.m().get_family_id("specrels")));
            }
        }
    }
}

void tst_smt_context()
{
    check_arithmetic_propagation_cancellation();
    check_lp_cancellation_recovery();
    check_recfun_rlimits();
    check_special_relation_logic();
    check_nonlinear_to_int();
    check_real_power_bounds();
    check_symbolic_regex_substring();
    check_array_index_dependencies();
    check_stored_lambdas();
    check_sat_array_lambdas();
    check_singleton_array_defaults();
    check_singleton_array_range_cardinality();
    check_expand_store_eq();

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

    {
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(define-fun-rec g ((x Int)) Int (ite (<= x 0) 0 (+ 1 (g (- x 1)))))\n"
            "(define-fun-rec h ((x Int)) Int (g x))\n"
            "(define-fun-rec f ((x Int)) Int (h x))\n"
            "(assert (= (f 3) 3))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        model mdl(m);
        expr_ref value(m);
        VERIFY(mdl.eval_expr(cmd.assertions()[0], value));
        VERIFY(m.is_true(value));
    }

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

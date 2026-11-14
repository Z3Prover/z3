
/*++
Copyright (c) 2015 Microsoft Corporation
--*/

#include "smt/smt_context.h"
#include "smt/smt_case_split_queue.h"
#include "math/lp/lar_solver.h"
#include "ast/reg_decl_plugins.h"
#include "ast/arith_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/proofs/proof_checker.h"
#include "ast/converters/generic_model_converter.h"
#include "cmd_context/cmd_context.h"
#include "util/gparams.h"
#include "parsers/smt2/smt2parser.h"
#include "ast/rewriter/distribute_forall.h"
#include "ast/rewriter/array_rewriter.h"
#include "ast/simplifiers/distribute_forall.h"
#include "solver/solver.h"
#include "model/model.h"
#include "qe/qsat.h"
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

static void check_case_split_relevant_first() {
    for (unsigned strategy : {0u, 1u, 2u}) {
        for (unsigned relevancy : {0u, 2u}) {
            for (unsigned setting : {0u, 1u, 2u}) {
                ast_manager m;
                reg_decl_plugins(m);
                params_ref p;
                p.set_bool("auto_config", false);
                p.set_uint("case_split", strategy);
                p.set_uint("relevancy", relevancy);
                if (setting != 0)
                    p.set_bool("case_split_relevant_first", setting == 2);
                smt_params params;
                params.updt_params(p);
                params.m_random_var_freq = 0;
                smt::context ctx(m, params, p);
                ctx.push();
                app_ref irrelevant(m.mk_const("irrelevant", m.mk_bool_sort()), m);
                app_ref relevant(m.mk_const("relevant", m.mk_bool_sort()), m);
                ctx.internalize(irrelevant, false);
                ctx.internalize(relevant, false);
                ctx.mark_as_relevant(relevant.get());
                smt::bool_var vi = ctx.get_bool_var(irrelevant);
                smt::bool_var vr = ctx.get_bool_var(relevant);
                ctx.set_activity(vi, 2);
                ctx.set_activity(vr, 1);
                scoped_ptr<smt::case_split_queue> queue(smt::mk_case_split_queue(ctx, params));
                queue->mk_var_eh(vi);
                queue->mk_var_eh(vr);
                bool relevant_first = setting == 2 && relevancy != 0;
                smt::bool_var next;
                lbool phase;
                queue->next_case_split(next, phase);
                VERIFY(next == (relevant_first ? vr : vi));
                queue->next_case_split(next, phase);
                VERIFY(next == (relevant_first ? vi : vr));
                queue->next_case_split(next, phase);
                VERIFY(next == smt::null_bool_var);
            }
        }
    }
}

static void check_late_equality_justification() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-sort U 0)\n"
            "(declare-const i U)\n"
            "(declare-const d U)\n"
            "(declare-const c U)\n"
            "(declare-const t Bool)\n"
            "(declare-const p Bool)\n"
            "(declare-const z Bool)\n"
            "(declare-const e Bool)\n"
            "(declare-const a (Array U Bool))\n"
            "(declare-const b (Array U Bool))\n"
            "(assert (= a (lambda ((x U)) (= x c))))\n"
            "(assert (not (select b i)))\n"
            "(assert (or t (= b a)))\n"
            "(assert (or t (not p)))\n"
            "(assert (or (not t) (not p)))\n"
            "(assert (or (= b a) p))\n"
            "(assert (or (= i d) z))\n"
            "(assert (or (= d c) z))\n"
            "(assert (or (not z) e))\n");
        VERIFY(parse_smt2_commands(cmd, is));
        params_ref p;
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* a : cmd.assertions())
            slv->assert_expr(a);
        VERIFY(l_true == slv->check_sat(0, nullptr));
    }
}

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

// Running into the unfolding budget is slow in debug builds. Use a small budget.
struct scoped_recfun_unfold_limit {
    std::string m_old;
    scoped_recfun_unfold_limit(char const* limit): m_old(gparams::get_value("rewriter.max_recfun_unfoldings")) {
        gparams::set("rewriter.max_recfun_unfoldings", limit);
    }
    ~scoped_recfun_unfold_limit() {
        gparams::set("rewriter.max_recfun_unfoldings", m_old.c_str());
    }
};

static void check_recfun_rlimits() {
    scoped_recfun_unfold_limit _limit("1000");
    for (char const* input : {
            "(define-fun-rec f ((x Int)) Int (f x))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f ((x Int)) Int (+ 1 (f (+ x 1))))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f () Int (+ 1 f))\n"
            "(assert (= f 1))\n",
            "(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int))"
            " ((g x) (f x)))\n"
            "(assert (= (f 0) 1))\n",
            // unfolding on values that does not terminate
            "(define-fun-rec f ((x Int)) Int (ite (> x 0) 0 (f x)))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f ((x Int)) Int (ite (> x 0) 0 (f (+ x 0))))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f ((x Int)) Int (ite (> x 0) 0 (f (- x 1))))\n"
            "(assert (= (f 0) 1))\n",
            "(define-fun-rec f ((x Int) (y Int)) Int (ite (> (+ x y) 5) 0 (f y x)))\n"
            "(assert (= (f 0 1) 1))\n",
            "(define-funs-rec ((f ((x Int)) Int) (g ((x Int)) Int))"
            " ((g x) (ite (> x 0) 0 (f x))))\n"
            "(assert (= (f 0) 1))\n"}) {
        check_recfun_rlimit(input, 1);
    }
    check_recfun_rlimit(
        "(define-fun-rec f ((x Int)) Int (+ 1 (f (+ x 1))))\n"
        "(assert (= (f 0) 1))\n", 1000);
}

static void check_recfun_output(char const* input, char const* expected) {
    ast_manager m;
    reg_decl_plugins(m);
    cmd_context cmd(false, &m);
    cmd.set_solver_factory(mk_smt_strategic_solver_factory());
    std::ostringstream out;
    cmd.set_regular_stream(out);
    std::istringstream is(input);
    VERIFY(parse_smt2_commands(cmd, is));
    if (out.str() != expected)
        std::cout << "expected:\n" << expected << "got:\n" << out.str();
    VERIFY(out.str() == expected);
}

static void check_mbqi_division_by_zero() {
    // The model checker interprets division, modulus and remainder by a zero
    // divisor as the current model does. A free choice refutes satisfied quantifiers.
    check_recfun_output(
        "(assert (forall ((x Int)) (= 0 (mod 0 x))))\n"
        "(check-sat)\n", "sat\n");
    check_recfun_output(
        "(declare-fun a () Real)\n"
        "(declare-fun b () Real)\n"
        "(declare-fun c () Real)\n"
        "(declare-fun d () Real)\n"
        "(assert (not (exists ((e Real)) (=> (and (= 0 (/ a (- b e)) c)) (< c d)))))\n"
        "(check-sat)\n", "sat\n");
    check_recfun_output(
        "(assert (forall ((x Int) (y Int) (z Int)) (= x (/ 1 y z (- 128 z 1)))))\n"
        "(check-sat)\n", "unsat\n");
}

static void check_recfun_unfold_limit() {
    // the simplifier unfolds recursive functions on values within a budget.
    check_recfun_output(
        "(define-fun-rec sum ((n Int)) Int (ite (<= n 0) 0 (+ n (sum (- n 1)))))\n"
        "(simplify (sum 50))\n"
        "(simplify (sum 50) :max_recfun_unfoldings 10)\n",
        "1275\n"
        "(+ 455 (sum 40))\n");
    // a call in a branch that is not taken does not block unfolding.
    check_recfun_output(
        "(define-fun-rec g ((x Int)) Int (ite (> x 0) (g x) 7))\n"
        "(define-fun-rec max2 ((x Int) (y Int)) Int (ite (>= x y) x (max2 y x)))\n"
        "(simplify (g 0))\n"
        "(simplify (max2 3 3))\n",
        "7\n"
        "3\n");
    // model evaluation terminates on applications that cannot be evaluated.
    scoped_recfun_unfold_limit _limit("1000");
    check_recfun_output(
        "(define-fun-rec f ((x Int)) Int (ite (> x 0) 0 (f x)))\n"
        "(assert (= (f 0) 1))\n"
        "(check-sat)\n"
        "(get-value ((f 0) (f 5)))\n"
        "(eval (f 0))\n",
        "sat\n"
        "(((f 0) (f 0))\n"
        " ((f 5) 0))\n"
        "(f 0)\n");
    check_recfun_output(
        "(define-fun-rec f ((x Int)) Int (f x))\n"
        "(assert (= (f 0) 1))\n"
        "(check-sat)\n"
        "(eval (f 0))\n",
        "sat\n"
        "(f 0)\n");
}

static void check_qe2_false_answer() {
    // qe2 reports a false answer as false, not as false under re-bound variables.
    check_recfun_output(
        "(declare-fun v () (Array Bool Bool))\n"
        "(assert (forall ((r (Array Bool Bool)) (a (Array (Array Bool Bool) Bool)))\n"
        "  (distinct true (select (store (store a v true) r true) (store v false false)))))\n"
        "(check-sat-using qe2)\n", "unsat\n");
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

static void check_generated_quantifiers() {
    struct {
        char const* input;
        bool positive_sat;
        bool negative_sat;
    } cases[] = {
        {"(assert (forall ((x Int) (b Bool))"
         " (! (or b (not b) (= x 0)) :skolemid generated)))", true, false},
        {"(assert (forall ((x Int) (b Bool))"
         " (! (and b (> x 0)) :skolemid generated)))", false, true},
        {"(declare-const p Bool)"
         "(assert (forall ((x Int) (b Bool))"
         " (! (or p (and b (> x 0))) :skolemid generated)))", true, true}
    };
    for (auto const& test : cases) {
        for (bool positive : {false, true}) {
            ast_manager m;
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream is(test.input);
            VERIFY(parse_smt2_commands(cmd, is));
            smt_params params;
            smt::context ctx(m, params);
            expr* q = cmd.assertions().get(0);
            for (unsigned i = 0; i < 2; ++i) {
                ctx.push();
                ctx.internalize(q, true);
                ctx.mark_as_relevant(q);
                smt::literal lit = ctx.get_literal(q);
                ctx.assign(positive ? lit : ~lit, smt::b_justification::mk_axiom());
                bool sat = positive ? test.positive_sat : test.negative_sat;
                VERIFY(ctx.check() == (sat ? l_true : l_false));
                ctx.pop(1);
            }
        }
    }

    for (char const* input : {
        "(assert (= ((as const (Array Int Int)) 0)"
        "           (lambda ((x Int)) (+ x 0))))",
        "(assert (= (lambda ((x Int) (b Bool)) (ite b x 0))"
        "           (lambda ((x Int) (b Bool)) (ite b (+ x 0) 0))))"}) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(input);
        VERIFY(parse_smt2_commands(cmd, is));
        app* eq = to_app(cmd.assertions().get(0));
        array_rewriter rw(m);
        expr_ref result(m);
        VERIFY(rw.mk_eq_core(eq->get_arg(0), eq->get_arg(1), result) == BR_REWRITE2);
        VERIFY(is_forall(result));
        VERIFY(to_quantifier(result)->get_skid() == symbol("generated"));
    }
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

static void check_sequence_last_index() {
    char const* const cases[] = {
        "(assert (= (seq.last_indexof (seq.++ (seq.unit 10) (seq.unit 20))"
        "                           (seq.unit 20)) 1))",
        "(assert (= (seq.last_indexof (seq.++ (seq.unit 10) (seq.unit 20))"
        "                           (seq.unit 10)) 0))",
        "(assert (= (seq.last_indexof"
        "  (seq.++ (seq.unit 10) (seq.unit 20) (seq.unit 10) (seq.unit 20) (seq.unit 10))"
        "  (seq.++ (seq.unit 10) (seq.unit 20) (seq.unit 10))) 2))",
        "(declare-const p (Seq Int))"
        "(assert (= (seq.last_indexof (seq.++ p (seq.unit 10) p (seq.unit 20))"
        "                           (seq.++ p (seq.unit 20))) (+ (seq.len p) 1)))",
        "(declare-const p (Seq Int))"
        "(assert (= (seq.last_indexof (seq.++ p (seq.unit 10) p (seq.unit 20) (seq.unit 30))"
        "                           (seq.++ p (seq.unit 20))) (+ (seq.len p) 1)))",
        "(declare-const t String)"
        "(assert (= (seq.last_indexof (str.++ t \"a\" t \"b\") (str.++ t \"b\")) (+ (str.len t) 1)))"
    };
    for (bool sat_smt : {false, true}) {
        for (auto const& test : cases) {
            ast_manager m;
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream input(test);
            VERIFY(parse_smt2_commands(cmd, input));
            params_ref p;
            p.set_bool("smt", sat_smt);
            ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
            expr* assertion = cmd.assertions()[0];
            // Each equation is valid, including for arbitrary symbolic prefixes.
            // Check both accepting its value and rejecting every other value.
            for (bool negate : {false, true}) {
                slv->push();
                slv->assert_expr(negate ? m.mk_not(assertion) : assertion);
                lbool expected = negate ? l_false : l_true;
                lbool actual = slv->check_sat(0, nullptr);
                bool correct = actual == expected;
                if (!correct)
                    std::cerr << "last_indexof: expected " << expected << ", got " << actual
                              << ", sat.smt=" << sat_smt << ", negate=" << negate
                              << '\n' << test << '\n';
                VERIFY(correct);
                slv->pop(1);
            }
        }
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

static void check_integer_power(bool euf) {
    struct example { char const* input; lbool expected; };
    example examples[] = {
        {"(declare-const x Real)(assert (< x 0.0))"
         "(assert (distinct (^ x (/ 1.0 2.0)) 0.0))", l_false},
        {"(declare-const x Real)(assert (= x (- 8.0)))"
         "(assert (= (^ x (/ 1.0 3.0)) (- 2.0)))", l_true},
        {"(declare-const x Real)(declare-const y Real)"
         "(assert (<= x (- 1.0)))(assert (>= x (- 1.0)))"
         "(assert (<= y (/ 1.0 2.0)))(assert (>= y (/ 1.0 2.0)))"
         "(assert (distinct (^ x y) 0.0))", l_false},
        {"(declare-const x Real)(declare-const y Real)"
         "(assert (<= x (- 1.0)))(assert (>= x (- 1.0)))"
         "(assert (<= y (/ 1.0 2.0)))(assert (>= y (/ 1.0 2.0)))"
         "(assert (= (^ x y) 0.0))", l_true},
        {"(declare-const x Real)(declare-const y Real)"
         "(assert (<= x (- 8.0)))(assert (>= x (- 8.0)))"
         "(assert (<= y (/ (- 1.0) 3.0)))(assert (>= y (/ (- 1.0) 3.0)))"
         "(assert (distinct (^ x y) (/ (- 1.0) 2.0)))", l_false},
        {"(declare-const x Real)(declare-const y Real)"
         "(assert (< x 0.0))(assert (= (* y y) 2.0))"
         "(assert (distinct (^ x y) 0.0))", l_false},
        {"(assert (= (^ 0.0 0.0) 1.0))", l_true},
        {"(assert (distinct (^ 0.0 0.0) 1.0))", l_false},
        {"(declare-const x Real)(assert (distinct (^ x 0.0) 1.0))", l_false},
        {"(declare-const x Real)(declare-const y Real)"
         "(assert (<= x 0.0))(assert (>= x 0.0))"
         "(assert (<= y 0.0))(assert (>= y 0.0))"
         "(assert (distinct (^ x y) 1.0))", l_false},
        {"(declare-const x Real)(declare-const y Real)"
         "(assert (<= x 0.0))(assert (>= x 0.0))"
         "(assert (<= y 0.0))(assert (>= y 0.0))"
         "(assert (= (^ x y) 1.0))", l_true},
        {"(set-logic QF_NIA)(assert (= (mod (** 2 (- 3)) 3) 0))", l_true},
        {"(set-logic QF_NIA)(assert (= (** 0 0) 1))(assert (= (** 0 (- 3)) 0))"
         "(assert (= (** (- 1) (- 3)) (- 1)))(assert (= (** (- 1) (- 4)) 1))"
         "(assert (= (** 2 (- 1000000000000000000000000000000)) 0))"
         "(assert (= (** (- 1) (- 1000000000000000000000000000000)) 1))", l_true},
        {"(declare-const n Int)(assert (>= n 0))(assert (= (** 2 n) 3))", l_false},
        {"(set-logic QF_NIA)(declare-const n Int)(assert (> n 10))(assert (= (** 2 n) 2048))", l_true},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (> x y))(assert (>= y 1))(assert (<= (** 2 x) (** 2 y)))", l_false},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (< x (- 1)))(assert (< y (- 2)))(assert (> y (- 4)))"
         "(assert (= (** x y) (- 8)))", l_false},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (< x (- 1)))(assert (< y (- 2)))(assert (> y (- 4)))"
         "(assert (= (** x y) 0))", l_true},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (> y 0))(assert (= (** 2 x) (** 3 y)))", l_false},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (< x 0))(assert (< y 0))(assert (= (** 2 x) (** 3 y)))", l_true},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (< y 0))(assert (= (** x y) 0))(assert (= (* x x) 1))", l_false},
        {"(declare-const n Int)(declare-const f Int)(assert (>= n 1))"
         "(assert (distinct (* (+ f n) (** 2 n))"
         " (+ (* 2 (+ f n (- 1)) (** 2 (- n 1))) (** 2 n))))", l_false},
        {"(declare-const x Int)(declare-const y Int)"
         "(assert (> (* x x) 4))(assert (> (* y y) 4))"
         "(assert (= (** (** x y) y) (** x (** y y))))", l_false},
        {"(declare-const x Int)(assert (= (** x 0) 1))(assert (= x 0))", l_true},
        {"(declare-const n Int)(declare-const r Real)"
         "(assert (= (* r r) 2.0))(assert (> r 0.0))"
         "(assert (>= n 1))(assert (<= n 4))(assert (= (** 2 n) 8))", l_true},
        {"(declare-const n Int)(declare-const r Real)"
         "(assert (= (* r r) 2.0))(assert (> r 0.0))"
         "(assert (>= n 1))(assert (<= n 4))(assert (= (** 2 n) 3))", l_false},
    };
    for (auto const& example : examples) {
        ast_manager m;
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(example.input);
        ENSURE(parse_smt2_commands(cmd, is));
        params_ref p;
        p.set_uint("timeout", 10000);
        if (euf) {
            p.set_bool("smt", true);
            p.set_bool("euf", true);
        }
        ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
        for (expr* assertion : cmd.assertions())
            slv->assert_expr(assertion);
        lbool result = slv->check_sat(0, nullptr);
        if (result != example.expected) {
            std::cerr << "integer power: " << example.input << "\nresult: " << result
                      << "\nreason: " << slv->reason_unknown() << "\n";
            statistics st;
            slv->collect_statistics(st);
            std::cerr << st << "\n";
        }
        ENSURE(result == example.expected);
        if (result == l_true) {
            model_ref mdl;
            slv->get_model(mdl);
            for (expr* assertion : cmd.assertions()) {
                expr_ref value(m);
                ENSURE(mdl->eval_expr(assertion, value, true) && m.is_true(value));
            }
        }
        slv->push();
        slv->assert_expr(m.mk_false());
        ENSURE(slv->check_sat(0, nullptr) == l_false);
        slv->pop(1);
        ENSURE(slv->check_sat(0, nullptr) == example.expected);
    }
    {
        ast_manager m;
        reg_decl_plugins(m);
        arith_util a(m);
        expr_ref n(m.mk_const(symbol("n"), a.mk_int()), m);
        expr_ref p(m.mk_const(symbol("p"), m.mk_bool_sort()), m);
        expr_ref q(m.mk_const(symbol("q"), m.mk_bool_sort()), m);
        expr_ref ten(a.mk_int(10), m), two(a.mk_int(2), m), target(a.mk_int(2048), m);
        expr_ref positive(a.mk_gt(n, ten), m), power(a.mk_power(two, n), m);
        expr_ref equality(m.mk_eq(power, target), m), witness(m.mk_and(positive, equality), m);
        expr_ref zero(a.mk_int(0), m), negative(a.mk_lt(n, zero), m);
        expr_ref first(m.mk_implies(p, witness), m), second(m.mk_implies(q, negative), m);
        params_ref params;
        params.set_bool("unsat_core", true);
        if (euf) {
            params.set_bool("smt", true);
            params.set_bool("euf", true);
        }
        ref<solver> slv = mk_smt2_solver(m, params, symbol::null);
        slv->assert_expr(first);
        slv->assert_expr(second);
        expr* assumptions[] = {p, q};
        ENSURE(slv->check_sat(1, assumptions) == l_true);
        ENSURE(slv->check_sat(2, assumptions) == l_false);
        expr_ref_vector core(m);
        slv->get_unsat_core(core);
        ENSURE(core.size() == 2 && core.contains(p) && core.contains(q));
        params.set_uint("rlimit", 20);
        slv->updt_params(params);
        ENSURE(slv->check_sat(1, assumptions) != l_false);
        params.set_uint("rlimit", 0);
        slv->updt_params(params);
        ENSURE(slv->check_sat(1, assumptions) == l_true);

        params.set_bool("core.minimize", true);
        slv = mk_smt2_solver(m, params, symbol::null);
        expr_ref one(a.mk_int(1), m);
        positive = a.mk_ge(n, one);
        expr_ref is_one(m.mk_eq(n, one), m);
        expr_ref not_one(m.mk_not(is_one), m);
        first = m.mk_implies(p, positive);
        second = m.mk_implies(q, not_one);
        slv->assert_expr(first);
        slv->assert_expr(second);
        slv->assert_expr(a.mk_gt(power, zero));
        ENSURE(slv->check_sat(2, assumptions) == l_true);
        model_ref mdl;
        slv->get_model(mdl);
        expr_ref result(m);
        ENSURE(mdl->eval_expr(p, result, true) && m.is_true(result));
        ENSURE(mdl->eval_expr(q, result, true) && m.is_true(result));
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

static void check_qsat_proofs() {
    struct {
        char const* input;
        lbool expected;
        bool quantified = false;
    } cases[] = {
        {"(declare-fun a () (Array Int (Array Int Int)))\n"
         "(assert (= a (store a 0 (store (select a 0) 0 0))))\n", l_true},
        {"(declare-const x Int)\n"
         "(assert (> x 0))\n"
         "(assert (< x 0))\n", l_false},
        {"(assert (forall ((a Real)) (exists ((b Real))\n"
         " (and (>= (+ a b) 0.0) (<= b 0.0)))))\n", l_false, true}
    };
    for (bool proofs : {false, true}) {
        for (auto const& test : cases) {
            ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream is(test.input);
            VERIFY(parse_smt2_commands(cmd, is));
            tactic_ref t = mk_qsat_tactic(m, params_ref());
            goal_ref g = alloc(goal, m, proofs, true, false);
            for (expr* a : cmd.assertions())
                g->assert_expr(a);
            model_ref md;
            labels_vec labels;
            proof_ref pr(m);
            expr_dependency_ref core(m);
            std::string reason_unknown;
            lbool expected = proofs && test.quantified ? l_undef : test.expected;
            VERIFY(expected == check_sat(*t, g, md, labels, pr, core, reason_unknown));
            if (expected == l_undef) {
                VERIFY(reason_unknown == "qsat does not support proof production");
                VERIFY(!pr);
            }
            else if (expected == l_true) {
                VERIFY(md);
                for (expr* a : cmd.assertions()) {
                    expr_ref value(m);
                    VERIFY(md->eval_expr(a, value) && m.is_true(value));
                }
            }
            else if (proofs) {
                VERIFY(pr && m.is_false(m.get_fact(pr)));
                proof_checker checker(m);
                expr_ref_vector side_conditions(m);
                VERIFY(checker.check(pr, side_conditions));
            }
        }
    }
}

static void check_qe_rec_proofs() {
    for (bool proofs : {false, true}) {
        ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
        reg_decl_plugins(m);
        cmd_context cmd(false, &m);
        std::istringstream is(
            "(declare-const p Bool)\n"
            "(assert (not (exists ((x Int)) p)))\n"
            "(assert p)\n");
        VERIFY(parse_smt2_commands(cmd, is));
        tactic_ref t = mk_qe_rec_tactic(m, params_ref());
        goal_ref g = alloc(goal, m, proofs, false, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason_unknown;
        tactic_ref solve = proofs ? t.get() : and_then(t.get(), mk_smt_tactic(m));
        VERIFY(l_false == check_sat(*solve, g, md, labels, pr, core, reason_unknown));
        if (proofs) {
            VERIFY(pr && m.is_false(m.get_fact(pr)));
            proof_checker checker(m);
            expr_ref_vector side_conditions(m);
            VERIFY(checker.check(pr, side_conditions));
        }

        std::istringstream quantified(
            "(assert (forall ((a Real)) (exists ((b Real))\n"
            " (and (>= (+ a b) 0.0) (<= b 0.0)))))\n");
        cmd.reset_assertions();
        VERIFY(parse_smt2_commands(cmd, quantified));
        g = alloc(goal, m, proofs, false, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        if (proofs) {
            VERIFY(l_undef == check_sat(*t, g, md, labels, pr, core, reason_unknown));
            VERIFY(reason_unknown == "qsat does not support proof production");
            VERIFY(!pr);
        }
        else {
            goal_ref_buffer result;
            (*t)(g, result);
            VERIFY(result.size() == 1);
            for (unsigned i = 0; i < result[0]->size(); ++i)
                VERIFY(!has_quantifiers(result[0]->form(i)));
        }
    }
}

static void check_proof_mode_guards() {
    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    tactic_manager tactics;
    install_tactics(tactics);
    cmd_context cmd(false, &m);
    std::istringstream input(
        "(declare-datatype Color ((red) (green) (blue)))\n"
        "(declare-const c Color)\n"
        "(declare-const b (_ BitVec 8))\n"
        "(declare-const f (_ FloatingPoint 8 24))\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(declare-fun h (Int Int) Int)\n"
        "(assert (or (= c red) (= c green)))\n"
        "(assert (= (bvadd b #x01) #x02))\n"
        "(assert (fp.isZero f))\n"
        "(assert (> x 0))\n"
        "(assert (< x 3))\n"
        "(assert (= (div x y) 3))\n"
        "(assert (forall ((k Int)) (= (h k 0) k)))\n");
    ENSURE(parse_smt2_commands(cmd, input));
    for (char const* name : {
        "ackermannize_bv", "add-bounds", "aig", "bit-blast", "bv_bound_chk", "diff-neq",
        "dt2bv", "elim-small-bv", "eq2bv", "ff-sat", "ff-solve", "ff2bv", "fix-dl-var",
        "fm", "fpa2bv", "horn", "horn-simplify", "lia2card", "lia2pb",
        "nla2bv", "nlqsat", "nlsat", "normalize-bounds", "occf", "pb2bv", "pb-preprocess",
        "pqffd", "psat", "psmt", "qe2", "qe_rec",
        "qffd", "qfnra-nlsat", "qsat",
        "recover-01", "reduce-args", "reduce-bv-size", "sat", "sat-preprocess",
        "smtfd", "solver-subsumption", "symmetry-reduce", "tseitin-cnf",
        "tseitin-cnf-core", "unit-subsume-simplify", "ctx-solver-simplify", "propagate-values",
        "blast-term-ite", "bv-slice", "bv1-blast", "bvarray2uf", "card2bv",
        "cofactor-term-ite", "dom-simplify", "elim-predicates", "elim-uncnstr2",
        "euf-completion", "factor", "fold-unfold",
        "injectivity", "max-bv-sharing", "propagate-bv-bounds2", "propagate-ineqs",
        "qe-light", "reduce-args2", "special-relations"
    }) {
        bool rejects = false;
        for (char const* rejecting : {
            "ackermannize_bv", "aig", "bv_bound_chk", "diff-neq", "elim-small-bv",
            "ff-sat", "ff-solve", "ff2bv", "fm", "horn",
            "lia2pb", "nla2bv", "nlsat", "occf", "pb2bv", "pqffd", "psat", "psmt",
            "qe2", "qe_rec", "qffd", "qfnra-nlsat", "qsat", "recover-01", "reduce-bv-size",
            "sat", "sat-preprocess", "smtfd", "symmetry-reduce", "tseitin-cnf", "tseitin-cnf-core",
            "unit-subsume-simplify"
        })
            rejects |= !strcmp(name, rejecting);
        tactic_cmd* factory = tactics.find_tactic_cmd(symbol(name));
        if (!factory)
            std::cerr << "Missing proof-mode test tactic: " << name << "\n";
        ENSURE(factory);
        tactic_ref t = factory->mk(m);
        if (!strcmp(name, "bit-blast")) {
            params_ref p;
            p.set_bool("blast_quant", true);
            t->updt_params(p);
        }
        for (bool cores : {false, true}) {
            goal_ref g = alloc(goal, m, true, true, cores);
            for (expr* a : cmd.assertions())
                g->assert_expr(a, cores ? a : nullptr);
            g->set_depth(7);
            g->add(alloc(generic_model_converter, m, "proof-noop"));
            goal_ref before = alloc(goal, *g);
            goal_ref_buffer result;
            bool rejected = false;
            try {
                (*t)(g, result);
            }
            catch (z3_exception const& ex) {
                ENSURE(rejects);
                ENSURE(strstr(ex.what(), "does not support proof production") ||
                       strstr(ex.what(), "generation of proof objects is not supported") ||
                       !strcmp(ex.what(), "QF_FF certificates are not supported in v1") ||
                       (cores && strstr(ex.what(), "does not support unsat core production")));
                rejected = true;
            }
            ENSURE(rejected == rejects);
            if (rejected) {
                t->cleanup();
                continue;
            }
            ENSURE(result.size() == 1 && result[0] == g.get());
            ENSURE(g->size() == before->size() && g->depth() == before->depth());
            ENSURE(g->prec() == before->prec());
            ENSURE(g->pc() == before->pc() && g->mc() == before->mc() && g->dc() == before->dc());
            for (unsigned i = 0; i < g->size(); ++i) {
                ENSURE(g->form(i) == before->form(i));
                ENSURE(g->pr(i) == before->pr(i));
                ENSURE(g->dep(i) == before->dep(i));
            }
            t->cleanup();
        }
    }

#ifndef SINGLE_THREAD
    {
        goal_ref g = alloc(goal, m, true, false, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        tactic_ref t = par_and_then(mk_skip_tactic(), mk_skip_tactic());
        goal_ref_buffer result;
        bool rejected = false;
        try {
            (*t)(g, result);
        }
        catch (tactic_exception const& ex) {
            ENSURE(!strcmp(ex.what(), "par_and_then does not support proof production"));
            rejected = true;
        }
        ENSURE(rejected);
    }
#endif

    struct {
        char const* name;
        char const* input;
    } cases[] = {
        {"dt2bv", "(declare-datatype C ((r) (g) (b))) (declare-const c C)"
                  "(assert (or (= c r) (= c g)))"},
        {"bit-blast", "(declare-const b (_ BitVec 8)) (assert (= (bvadd b #x01) #x02))"},
        {"fpa2bv", "(declare-const f (_ FloatingPoint 8 24)) (assert (fp.isZero f))"},
        {"fix-dl-var", "(declare-const x Int) (declare-const y Int) (assert (<= (- x y) 3))"},
        {"purify-arith", "(declare-const x Int) (declare-const y Int) (assert (= (div x y) 3))"},
        {"sat", "(declare-const a Bool) (declare-const b Bool) (assert (or a b))"}
    };
    for (auto const& test : cases) {
        ast_manager n;
        reg_decl_plugins(n);
        cmd_context ctx(false, &n);
        std::istringstream source(test.input);
        ENSURE(parse_smt2_commands(ctx, source));
        goal_ref g = alloc(goal, n, false, true, false);
        for (expr* a : ctx.assertions())
            g->assert_expr(a);
        tactic_ref normalize = mk_simplify_tactic(n);
        goal_ref_buffer normalized;
        (*normalize)(g, normalized);
        ENSURE(normalized.size() == 1);
        g = normalized[0];
        goal_ref before = alloc(goal, *g);
        tactic_ref t = tactics.find_tactic_cmd(symbol(test.name))->mk(n);
        goal_ref_buffer result;
        (*t)(g, result);
        ENSURE(result.size() == 1);
        bool changed = result[0]->size() != before->size();
        for (unsigned i = 0; !changed && i < before->size(); ++i)
            changed = result[0]->form(i) != before->form(i);
        ENSURE(changed);
        t->cleanup();
    }
}

static void check_proof_mode_compositions() {
    struct {
        char const* name;
        bool cores;
    } cases[] = {
        {"purify-arith", false}, {"nra", false}, {"qfnra", false},
        {"qfufbv_ackr", false},
        {"quasi-macros", false}, {"quasi-macros", true}
    };
    for (auto const& test : cases) {
        ast_manager m(PGM_ENABLED);
        reg_decl_plugins(m);
        tactic_manager tactics;
        install_tactics(tactics);
        cmd_context cmd(false, &m);
        std::istringstream input(
            !strcmp(test.name, "quasi-macros") ?
            "(declare-fun h (Int Int) Int)"
            "(assert (forall ((k Int)) (= (h k 0) k)))"
            "(assert (not (= (h 1 0) 1)))" :
            "(declare-const x Real)"
            "(assert (> (+ x 0.0) 0.0)) (assert (< x 0.0))");
        ENSURE(parse_smt2_commands(cmd, input));
        goal_ref g = alloc(goal, m, true, false, test.cores);
        for (expr* a : cmd.assertions())
            g->assert_expr(a, test.cores ? a : nullptr);
        goal_ref before = alloc(goal, *g);
        tactic_ref t = tactics.find_tactic_cmd(symbol(test.name))->mk(m);
        goal_ref_buffer result;
        (*t)(g, result);
        ENSURE(result.size() == 1);
        bool changed = result[0]->size() != before->size();
        for (unsigned i = 0; !changed && i < before->size(); ++i)
            changed = result[0]->form(i) != before->form(i);
        ENSURE(changed);
        for (unsigned i = 0; i < result[0]->size(); ++i) {
            proof* pr = result[0]->pr(i);
            ENSURE(pr && m.get_fact(pr) == result[0]->form(i));
            if (test.cores)
                ENSURE(result[0]->dep(i));
            for (expr* e : subterms::all(expr_ref(pr, m))) {
                if (!m.is_asserted(e))
                    continue;
                bool original = false;
                for (expr* a : cmd.assertions())
                    original |= a == m.get_fact(to_app(e));
                ENSURE(original);
            }
        }
    }

    ast_manager m(PGM_ENABLED);
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref zero(a.mk_real(0), m), sum(a.mk_add(x, zero), m);
    expr_ref lower(a.mk_gt(sum, zero), m), upper(a.mk_lt(x, zero), m);
    goal_ref g = alloc(goal, m, true, false, false);
    g->assert_expr(lower);
    g->assert_expr(upper);
    tactic_ref t = and_then(mk_simplify_tactic(m), mk_bit_blaster_tactic(m), mk_smt_tactic(m));
    model_ref md;
    labels_vec labels;
    proof_ref pr(m);
    expr_dependency_ref core(m);
    std::string reason;
    ENSURE(check_sat(*t, g, md, labels, pr, core, reason) == l_false);
    ENSURE(pr && m.is_false(m.get_fact(pr)));
    proof_checker checker(m);
    expr_ref_vector side_conditions(m);
    ENSURE(checker.check(pr, side_conditions));
}

static void check_proof_mode_sls() {
    for (char const* name : {"qfbv-sls", "sls-smt"}) {
        for (bool proofs : {false, true}) {
            for (bool satisfiable : {false, true}) {
                ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
                reg_decl_plugins(m);
                tactic_manager tactics;
                install_tactics(tactics);
                cmd_context cmd(false, &m);
                std::istringstream input(
                    satisfiable ?
                    "(declare-const x (_ BitVec 4)) (assert (= (bvmul x x) #x1))" :
                    "(declare-const x (_ BitVec 4)) (assert (= (bvmul x x) #x2))");
                ENSURE(parse_smt2_commands(cmd, input));
                goal_ref g = alloc(goal, m, proofs, true, false);
                for (expr* a : cmd.assertions())
                    g->assert_expr(a);
                tactic_ref t = tactics.find_tactic_cmd(symbol(name))->mk(m);
                model_ref md;
                labels_vec labels;
                proof_ref pr(m);
                expr_dependency_ref core(m);
                std::string reason;
                lbool status;
                {
                    scoped_rlimit limit(m.limit(), 50000);
                    status = check_sat(*t, g, md, labels, pr, core, reason);
                }
                if (proofs) {
                    ENSURE(status == l_undef);
                    ENSURE(reason == "bv-size-reduction does not support proof production");
                    ENSURE(!g->is_decided_unsat());
                }
                else {
                    ENSURE(status == (satisfiable ? l_true : l_undef));
                    if (satisfiable) {
                        ENSURE(md);
                        for (expr* assertion : cmd.assertions()) {
                            expr_ref value(m);
                            ENSURE(md->eval_expr(assertion, value, true));
                            ENSURE(m.is_true(value));
                        }
                    }
                    else
                        ENSURE(!g->is_decided_unsat());
                }
                t->cleanup();
            }
        }
    }
}

static void check_proof_mode_fallbacks() {
    struct {
        char const* name;
        char const* input;
    } cases[] = {
        {"qfbv", "(declare-const x (_ BitVec 8))"
                  "(assert (= (bvand x #x01) #x01))"
                  "(assert (= (bvand x #x01) #x00))"},
        {"qffp", "(declare-datatype C ((r) (g) (b))) (declare-const c C)"
                 "(declare-const f (_ FloatingPoint 8 24)) (assert (fp.isZero f))"
                 "(assert (or (= c r) (= c g))) (assert (not (= c r))) (assert (not (= c g)))"},
        {"qfnia", "(declare-const x Int) (assert (> x 0)) (assert (< x 0))"},
        {"qfnra", "(declare-const x Real) (assert (> x 0.0)) (assert (< x 0.0))"},
        {"nra", "(declare-const x Real) (assert (> x 0.0)) (assert (< x 0.0))"},
        {"lra", "(assert (forall ((a Real)) (exists ((b Real))"
                " (and (>= (+ a b) 0.0) (<= b 0.0)))))"}
    };
    for (auto const& test : cases) {
        ast_manager m(PGM_ENABLED);
        reg_decl_plugins(m);
        tactic_manager tactics;
        install_tactics(tactics);
        cmd_context cmd(false, &m);
        std::istringstream input(test.input);
        ENSURE(parse_smt2_commands(cmd, input));
        goal_ref g = alloc(goal, m, true, false, false);
        for (expr* a : cmd.assertions())
            g->assert_expr(a);
        tactic_ref t = tactics.find_tactic_cmd(symbol(test.name))->mk(m);
        model_ref md;
        labels_vec labels;
        proof_ref pr(m);
        expr_dependency_ref core(m);
        std::string reason;
        ENSURE(check_sat(*t, g, md, labels, pr, core, reason) == l_false);
        ENSURE(pr && m.is_false(m.get_fact(pr)));
        for (expr* e : subterms::all(expr_ref(pr, m))) {
            if (!m.is_asserted(e))
                continue;
            bool original = false;
            for (expr* assertion : cmd.assertions())
                original |= assertion == m.get_fact(to_app(e));
            ENSURE(original);
        }
        // The legacy checker rejects OEQ definition premises in BV congruence.
        if (strcmp(test.name, "qfbv")) {
            proof_checker checker(m);
            expr_ref_vector side_conditions(m);
            ENSURE(checker.check(pr, side_conditions));
        }
    }
}

static void check_horn_proof_diagnostic() {
    char const* inputs[] = {
        "(declare-fun inv (Int) Bool)"
        "(assert (forall ((x Int)) (=> (= x 0) (inv x))))"
        "(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))"
        "(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))",
        "(assert (forall ((q17 Int) (q18 Int) (q19 Bool)) false))",
        "(declare-fun p (Int) Bool)"
        "(assert (p 0))"
        "(assert (not (p 0)))"
        "(assert (not (p 1)))",
        "(declare-fun p (Int) Bool)"
        "(assert (p 0))"
        "(assert (not (p 1)))"
    };
    for (bool proofs : {false, true}) {
        for (unsigned i = 0; i < 4; ++i) {
            ast_manager m(proofs ? PGM_ENABLED : PGM_DISABLED);
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream input(inputs[i]);
            ENSURE(parse_smt2_commands(cmd, input));
            params_ref p;
            scoped_ptr<solver_factory> factory = mk_smt_strategic_solver_factory();
            ref<solver> slv = (*factory)(m, p, proofs, true, false, symbol("HORN"));
            for (expr* a : cmd.assertions())
                slv->assert_expr(a);
            lbool result = slv->check_sat(0, nullptr);
            if (proofs) {
                ENSURE(result == l_undef);
                ENSURE(slv->reason_unknown() == "horn does not support proof production");
            }
            else {
                ENSURE(result == (i == 3 ? l_true : l_false));
            }
        }
    }
}

static void check_intblast_signed_mod() {
    for (int x = 0; x < 8; ++x) {
        for (int y = 0; y < 8; ++y) {
            int sx = x < 4 ? x : x - 8;
            int sy = y < 4 ? y : y - 8;
            int expected = sx;
            if (sy != 0) {
                expected = sx % sy;
                if (expected != 0 && (expected < 0) != (sy < 0))
                    expected += sy;
            }
            expected = (expected + 8) % 8;
            std::ostringstream spec;
            spec << "(declare-const x (_ BitVec 3))\n"
                 << "(declare-const y (_ BitVec 3))\n"
                 << "(assert (bvule (_ bv" << x << " 3) x))\n"
                 << "(assert (bvule x (_ bv" << x << " 3)))\n"
                 << "(assert (bvule (_ bv" << y << " 3) y))\n"
                 << "(assert (bvule y (_ bv" << y << " 3)))\n"
                 << "(assert (= (ubv_to_int (bvsmod x y)) " << expected << "))\n";
            ast_manager m;
            reg_decl_plugins(m);
            cmd_context cmd(false, &m);
            std::istringstream input(spec.str());
            ENSURE(parse_smt2_commands(cmd, input));
            params_ref p;
            p.set_uint("bv.solver", 2);
            ref<solver> slv = mk_smt2_solver(m, p, symbol::null);
            for (unsigned i = 0; i + 1 < cmd.assertions().size(); ++i)
                slv->assert_expr(cmd.assertions()[i]);
            slv->push();
            slv->assert_expr(m.mk_not(cmd.assertions().back()));
            ENSURE(l_false == slv->check_sat(0, nullptr));
            slv->pop(1);
            slv->assert_expr(cmd.assertions().back());
            ENSURE(l_true == slv->check_sat(0, nullptr));
        }
    }
}

void tst_smt_context()
{
    check_late_equality_justification();
    check_proof_mode_guards();
    check_proof_mode_compositions();
    check_proof_mode_sls();
    check_proof_mode_fallbacks();
    check_horn_proof_diagnostic();
    check_integer_power(false);
    check_integer_power(true);
    check_case_split_relevant_first();
    check_intblast_signed_mod();
    check_qsat_proofs();
    check_qe_rec_proofs();
    check_arithmetic_propagation_cancellation();
    check_lp_cancellation_recovery();
    check_recfun_rlimits();
    check_recfun_unfold_limit();
    check_mbqi_division_by_zero();
    check_special_relation_logic();
    check_nonlinear_to_int();
    check_qe2_false_answer();
    check_real_power_bounds();
    check_symbolic_regex_substring();
    check_sequence_last_index();
    check_array_index_dependencies();
    check_generated_quantifiers();
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

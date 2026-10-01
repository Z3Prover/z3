/*++
Copyright (c) 2026

Module Name:

    bv_mul_bounds.cpp

Abstract:

    Regression tests for unsigned multiplication order bounds.

--*/
#include "api/c++/z3++.h"
#include "util/util.h"
#include "ast/reg_decl_plugins.h"
#include "ast/for_each_expr.h"
#include "ast/proofs/proof_checker.h"
#include "ast/simplifiers/bv_mul_bounds.h"
#include "smt/smt_solver.h"
#include "solver/solver.h"

static void test_mul_order_budget(unsigned width, bool strict, bool reverse, bool small_guard) {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", width);
    z3::expr b = ctx.bv_const("b", width);
    z3::expr c = ctx.bv_const("c", width);
    z3::solver s(ctx, "QF_BV");
    s.set("rlimit", 10000u);
    s.add(strict ? z3::ult(a, b) : z3::ule(a, b));
    s.add(z3::ugt(reverse ? c * a : a * c, reverse ? c * b : b * c));
    s.add(z3::bvmul_no_overflow(reverse ? c : b, reverse ? b : c, false));
    if (small_guard)
        s.add(z3::bvmul_no_overflow(a, c, false));
    // A resource budget, rather than a wall-clock threshold, detects the
    // missing word-level implication without depending on machine speed.
    ENSURE(s.check() == z3::unsat);
}

static void test_mul_wraparound_guards() {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", 4);
    z3::expr b = ctx.bv_const("b", 4);
    z3::expr c = ctx.bv_const("c", 4);
    z3::expr p = ctx.bool_const("p");
    z3::expr ac = a * c, bc = b * c;
    z3::expr nb = z3::bvmul_no_overflow(b, c, false);
    z3::solver s(ctx, "QF_BV");
    // 2*6=12 fits, while 3*6=18 wraps to 2. The smaller guard is
    // insufficient, and a guard inside a disjunction is not an asserted fact.
    s.add(a == 2 && b == 3 && c == 6);
    s.add(z3::ult(a, b) && z3::ugt(ac, bc));
    s.add(z3::bvmul_no_overflow(a, c, false));
    s.push();
    s.add(nb || p);
    s.add(p);
    ENSURE(s.check() == z3::sat);
    ENSURE(s.get_model().eval(!nb).is_true());
    s.pop();
    s.push();
    s.add(!nb);
    ENSURE(s.check() == z3::sat);
    s.pop();
    s.add(nb);
    ENSURE(s.check() == z3::unsat);
}

static void test_mul_signed_and_zero() {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", 4);
    z3::expr b = ctx.bv_const("b", 4);
    z3::expr c = ctx.bv_const("c", 4);
    z3::solver s(ctx, "QF_BV");
    // Signed no-overflow does not prevent unsigned wraparound.
    s.add(a == 1 && b == 2 && c == 15);
    s.add(z3::ult(a, b) && z3::ugt(a * c, b * c));
    s.add(z3::bvmul_no_overflow(a, c, true));
    s.add(z3::bvmul_no_overflow(b, c, true));
    ENSURE(s.check() == z3::sat);
    s.reset();
    // Signed input order cannot be used as unsigned input order.
    s.add(a == 8 && b == 1 && c == 1);
    s.add(a < b && z3::ugt(a * c, b * c));
    s.add(z3::bvmul_no_overflow(b, c, false));
    ENSURE(s.check() == z3::sat);
    s.reset();
    // A zero common factor permits equal products even for reversed inputs.
    s.add(a == 3 && b == 2 && c == 0);
    s.add(z3::ule(a * c, b * c));
    s.add(z3::bvmul_no_overflow(b, c, false));
    ENSURE(s.check() == z3::sat);
}

static void test_mul_order_incremental() {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", 16);
    z3::expr b = ctx.bv_const("b", 16);
    z3::expr c = ctx.bv_const("c", 16);
    // Use the full-goal tactic after each check, rather than the separate
    // incremental SAT backend selected by the default solver after push().
    z3::solver s = z3::tactic(ctx, "qfbv").mk_solver();
    s.set("rlimit", 10000u);
    s.add(z3::ult(a, b));
    s.add(z3::ugt(a * c, b * c));
    s.push();
    s.add(z3::bvmul_no_overflow(b, c, false));
    ENSURE(s.check() == z3::unsat);
    s.pop();
    s.add(a == 2 && b == 3 && c == 32767);
    ENSURE(s.check() == z3::sat);
}

static void test_mul_bounds_guard_context() {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", 4);
    z3::expr b = ctx.bv_const("b", 4);
    z3::expr c = ctx.bv_const("c", 4);
    z3::expr p = ctx.bool_const("p");
    z3::expr nb = z3::bvmul_no_overflow(b, c, false);
    z3::tactic t(ctx, "bv-mul-bounds");
    for (unsigned mode = 0; mode < 3; ++mode) {
        z3::goal g(ctx, false, false, false);
        g.add(z3::ult(a, b));
        g.add(z3::ugt(a * c, b * c));
        if (mode == 0)
            g.add(nb || p);
        else if (mode == 1)
            g.add(!nb);
        else
            g.add(z3::bvmul_no_overflow(a, c, false));
        z3::apply_result r = t(g);
        ENSURE(r.size() == 1);
        z3::solver s(ctx, "QF_BV");
        s.add(r[0].as_expr());
        // Bind only after applying the tactic, so value propagation cannot
        // erase the guarded symbolic pattern before the test exercises it.
        s.add(a == 2 && b == 3 && c == 6 && p);
        ENSURE(s.check() == z3::sat);
    }
}

static void test_mul_bounds_valid_lemmas() {
    for (unsigned width : {1u, 2u, 3u, 4u}) {
        z3::context ctx;
        z3::expr a = ctx.bv_const("a", width);
        z3::expr b = ctx.bv_const("b", width);
        z3::expr c = ctx.bv_const("c", width);
        z3::expr p = ctx.bool_const("p");
        z3::expr_vector from(ctx), to(ctx);
        from.push_back(a);
        from.push_back(b);
        from.push_back(c);
        z3::tactic t(ctx, "bv-mul-bounds");
        for (bool reverse : {false, true}) {
            z3::goal g(ctx, false, false, false);
            g.add(reverse ? !z3::uge(a, b) : z3::ult(a, b));
            g.add(reverse ? z3::ult(c * b, c * a) : z3::ugt(a * c, b * c));
            // Keep the guard below an OR so the goal retains the new clause
            // instead of closing immediately by top-level unit resolution.
            g.add(z3::bvmul_no_overflow(reverse ? c : b, reverse ? b : c, false) || p);
            unsigned original_size = g.size();
            z3::apply_result r = t(g);
            ENSURE(r.size() == 1 && r[0].size() > original_size);
            z3::apply_result repeated = t(r[0]);
            ENSURE(repeated.size() == 1 && repeated[0].size() == r[0].size());
            for (unsigned i = original_size; i < r[0].size(); ++i) {
                z3::expr lemma = r[0][i];
                for (unsigned x = 0; x < (1u << width); ++x)
                    for (unsigned y = 0; y < (1u << width); ++y)
                        for (unsigned z = 0; z < (1u << width); ++z) {
                            to.resize(0);
                            to.push_back(ctx.bv_val(x, width));
                            to.push_back(ctx.bv_val(y, width));
                            to.push_back(ctx.bv_val(z, width));
                            ENSURE(lemma.substitute(from, to).simplify().is_true());
                        }
            }
        }
    }
}

static void test_mul_bounds_other_inputs() {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", 4);
    z3::expr b = ctx.bv_const("b", 4);
    z3::expr c = ctx.bv_const("c", 4);
    z3::expr d = ctx.bv_const("d", 4);
    z3::tactic t(ctx, "bv-mul-bounds");
    for (unsigned mode = 0; mode < 4; ++mode) {
        z3::goal g(ctx, false, false, false);
        if (mode == 0) {
            g.add(a < b);
            g.add(z3::ugt(a * c, b * c));
            g.add(z3::bvmul_no_overflow(b, c, false));
        }
        else if (mode == 1) {
            g.add(z3::ult(a, b));
            g.add(z3::ugt(a * c, b * c));
            g.add(z3::bvmul_no_overflow(b, c, true));
        }
        else if (mode == 2) {
            g.add(z3::ugt(a, b));
            g.add(z3::ule(a * c, b * c));
            g.add(z3::bvmul_no_overflow(b, c, false));
        }
        else {
            g.add(z3::ult(a, b));
            g.add(z3::ugt(a * c, b * d));
            g.add(z3::bvmul_no_overflow(b, d, false));
        }
        z3::apply_result r = t(g);
        ENSURE(r.size() == 1);
        z3::solver s(ctx, "QF_BV");
        s.add(r[0].as_expr());
        if (mode == 0)
            s.add(a == 8 && b == 1 && c == 1);
        else if (mode == 1)
            s.add(a == 1 && b == 2 && c == 15);
        else if (mode == 2)
            s.add(a == 3 && b == 2 && c == 0);
        else
            s.add(a == 2 && b == 3 && c == 5 && d == 3);
        ENSURE(s.check() == z3::sat);
    }
}

static void test_mul_bounds_satisfied_lemmas() {
    z3::context ctx;
    z3::expr a = ctx.bv_const("a", 16);
    z3::expr b = ctx.bv_const("b", 16);
    z3::expr c = ctx.bv_const("c", 16);
    z3::expr guard = z3::bvmul_no_overflow(b, c, false);
    z3::tactic t(ctx, "bv-mul-bounds");
    for (unsigned mode = 0; mode < 3; ++mode) {
        z3::goal g(ctx, false, false, false);
        if (mode == 0) {
            // The available opposite order makes the lemma's antecedent
            // false. Adding the satisfied clause can perturb SAT search.
            g.add(z3::ult(a, b));
            g.add(z3::ult(a * c, b * c));
            g.add(z3::bvmul_no_overflow(a, c, false));
        }
        else {
            g.add(z3::ule(a, b));
            g.add(mode == 1 ? z3::ule(a * c, b * c) : z3::ugt(a * c, b * c));
            g.add(mode == 1 ? guard : !guard);
        }
        z3::apply_result r = t(g);
        ENSURE(r.size() == 1 && r[0].size() == g.size());
    }
}

static void test_mul_bounds_complement_ownership() {
    ast_manager m;
    reg_decl_plugins(m);
    bv_util bv(m);
    expr_ref a(m.mk_const("a", bv.mk_sort(4)), m);
    expr_ref b(m.mk_const("b", bv.mk_sort(4)), m);
    expr_ref c(m.mk_const("c", bv.mk_sort(4)), m);
    expr_ref p(m.mk_const("p", m.mk_bool_sort()), m);
    expr_ref order(bv.mk_ule(b, a), m);
    base_dependent_expr_state st(m);
    st.add(dependent_expr(m, m.mk_or(order, p), nullptr, nullptr));
    st.add(dependent_expr(m, m.mk_not(bv.mk_ule(bv.mk_bv_mul(a, c), bv.mk_bv_mul(b, c))), nullptr, nullptr));
    st.add(dependent_expr(m, m.mk_or(bv.mk_bvumul_no_ovfl(b, c), p), nullptr, nullptr));
    unsigned refs = order->get_ref_count();
    bv::mul_bounds bounds(m, st);
    bounds.reduce();
    ENSURE(st.qtail() == 4 && !st.inconsistent());
    // The added clause owns one reference to order. A missing complementary
    // assertion must not leave another reference through a temporary NOT.
    ENSURE(order->get_ref_count() == refs + 1);
}

static void test_mul_bounds_proof_rules() {
    for (unsigned width : {4u, 16u}) {
        ast_manager m(PGM_ENABLED);
        reg_decl_plugins(m);
        bv_util bv(m);
        expr_ref a(m.mk_const("a", bv.mk_sort(width)), m);
        expr_ref b(m.mk_const("b", bv.mk_sort(width)), m);
        expr_ref c(m.mk_const("c", bv.mk_sort(width)), m);
        for (bool strict : {false, true}) {
            expr_ref_vector assertions(m);
            assertions.push_back(strict ? m.mk_not(bv.mk_ule(b, a)) : bv.mk_ule(a, b));
            assertions.push_back(m.mk_not(bv.mk_ule(bv.mk_bv_mul(a, c), bv.mk_bv_mul(b, c))));
            assertions.push_back(bv.mk_bvumul_no_ovfl(b, c));
            base_dependent_expr_state st(m);
            for (expr* f : assertions)
                st.add(dependent_expr(m, f, m.mk_asserted(f), nullptr));
            bv::mul_bounds bounds(m, st);
            bounds.reduce();
            ENSURE(st.inconsistent());
            dependent_expr result = st[st.qtail() - 1];
            ENSURE(m.is_false(result.fml()));
            ENSURE(result.pr() && m.get_fact(result.pr()) == result.fml());
            ENSURE(result.pr()->get_decl_kind() == PR_UNIT_RESOLUTION);
            proof_checker checker(m);
            expr_ref_vector side_conditions(m);
            ENSURE(checker.check(result.pr(), side_conditions));
            ENSURE(side_conditions.empty());
            bool has_lemma = false;
            for (expr* e : subterms::all(expr_ref(result.pr(), m))) {
                if (m.is_asserted(e)) {
                    bool found = false;
                    for (expr* f : assertions)
                        found |= f == m.get_fact(to_app(e));
                    ENSURE(found);
                }
                if (!m.is_proof(e) || to_app(e)->get_decl_kind() != PR_TH_LEMMA)
                    continue;
                has_lemma = true;
                // The proof checker treats BV theory lemmas as trusted.
                // Independently validate the small-width lemma with the SMT
                // backend, which does not run this QF_BV preprocessing pass.
                if (width == 4) {
                    params_ref p;
                    p.set_uint("rlimit", 1000000);
                    solver_ref check(mk_smt_solver(m, p, symbol()));
                    check->assert_expr(m.mk_not(m.get_fact(to_app(e))));
                    ENSURE(check->check_sat(0, nullptr) == l_false);
                }
            }
            ENSURE(has_lemma);
        }
    }
}

static void test_mul_order_proof_and_core() {
    z3::config cfg;
    cfg.set("proof", true);
    z3::context ctx(cfg);
    z3::expr a = ctx.bv_const("a", 16);
    z3::expr b = ctx.bv_const("b", 16);
    z3::expr c = ctx.bv_const("c", 16);
    z3::solver s(ctx, "QF_BV");
    s.set("rlimit", 10000u);
    s.add(z3::ult(a, b));
    s.add(z3::ugt(a * c, b * c));
    s.add(z3::bvmul_no_overflow(b, c, false));
    ENSURE(s.check() == z3::unsat);
    ENSURE(s.proof().is_app());

    z3::context core_ctx;
    z3::expr x = core_ctx.bv_const("x", 16);
    z3::expr y = core_ctx.bv_const("y", 16);
    z3::expr z = core_ctx.bv_const("z", 16);
    z3::expr order = core_ctx.bool_const("order");
    z3::expr product = core_ctx.bool_const("product");
    z3::expr guard = core_ctx.bool_const("guard");
    // assert-and-track on the default solver selects a different backend.
    // Explicitly use QF_BV preprocessing to exercise the lemma dependencies.
    z3::solver core_solver = z3::tactic(core_ctx, "qfbv").mk_solver();
    core_solver.set("unsat_core", true);
    core_solver.set("rlimit", 10000u);
    core_solver.add(z3::ult(x, y), order);
    core_solver.add(z3::ugt(x * z, y * z), product);
    core_solver.add(z3::bvmul_no_overflow(y, z, false), guard);
    ENSURE(core_solver.check() == z3::unsat);
    z3::expr_vector core = core_solver.unsat_core();
    bool has_order = false, has_product = false, has_guard = false;
    for (unsigned i = 0; i < core.size(); ++i) {
        has_order |= z3::eq(core[i], order);
        has_product |= z3::eq(core[i], product);
        has_guard |= z3::eq(core[i], guard);
    }
    ENSURE(has_order && has_product && has_guard);
}

static void test_mul_bounds_qfbv_depth() {
    z3::context ctx;
    z3::goal g(ctx);
    g.add(ctx.parse_string(
        "(assert (forall ((x (_ BitVec 32)))"
        " (exists ((y (_ BitVec 32))) (= x (bvmul y y)))))"));
    z3::apply_result result = z3::tactic(ctx, "qfbv")(g);
    ENSURE(result.size() == 1);
    ENSURE(result[0].inconsistent());
    // Preserve the existing QF_BV preprocessing depth for unrelated goals,
    // including the official qfbv-quant SMT-LIB regression.
    ENSURE(result[0].depth() == 8);
}

void tst_bv_mul_bounds() {
    test_mul_bounds_qfbv_depth();
    test_mul_order_budget(16, true, false, true);
    for (unsigned width : {1u, 4u, 8u, 16u, 32u, 64u})
        for (bool strict : {false, true})
            for (bool reverse : {false, true})
                test_mul_order_budget(width, strict, reverse, false);
    test_mul_wraparound_guards();
    test_mul_signed_and_zero();
    test_mul_order_incremental();
    test_mul_bounds_guard_context();
    test_mul_bounds_valid_lemmas();
    test_mul_bounds_other_inputs();
    test_mul_bounds_satisfied_lemmas();
    test_mul_bounds_complement_ownership();
    test_mul_bounds_proof_rules();
    test_mul_order_proof_and_core();
}

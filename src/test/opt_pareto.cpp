/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_pareto.cpp

Abstract:

    Tests for Pareto enumeration in opt::context over the nlsat-backed
    solver (opt.pareto_nlsat). Covers what the SMT-LIB regressions cannot
    assert directly: the model values of the front points are irrational
    algebraic numerals, front points closer than the 12-digit display
    bracket are still told apart, and problems outside the NRA fragment
    fall back to the smt solver and enumerate their front there.

Author:

    Lev Nachmanson 2026-09-04

--*/
#include "opt/opt_context.h"
#include "opt/opt_pareto_solver.h"
#include "ast/reg_decl_plugins.h"

static void set_pareto_priority(opt::context& ctx, bool reuse_nlsat_solver = true) {
    // Use Pareto enumeration rather than lexicographic optimization.
    params_ref p;
    p.set_sym("priority", symbol("pareto"));
    // On eligible problems, retain the nlsat instance and its learned clauses
    // between checks; false selects a fresh exact nlsat solver for each check.
    p.set_bool("pareto_nlsat_reuse", reuse_nlsat_solver);
    ctx.updt_params(p);
}

static void tst_irrational_front(bool reuse_nlsat_solver) {
    // Check that both incomparable irrational Pareto points are returned once,
    // and that their model coordinates are exact algebraic numerals.
    std::cout << "opt_pareto: irrational front\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx, reuse_nlsat_solver);
    expr_ref x(m.mk_const(symbol("x"), a.mk_real()), m);
    expr_ref y(m.mk_const(symbol("y"), a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    // x^2 = 2 and y = -x leave (sqrt(2), -sqrt(2)) and (-sqrt(2), sqrt(2)).
    // Maximizing both coordinates makes neither point dominate the other.
    ctx.add_hard_constraint(m.mk_eq(a.mk_mul(x, x), two));
    ctx.add_hard_constraint(m.mk_eq(y, a.mk_uminus(x)));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(y.get()), true);
    expr_ref_vector asms(m);
    model_ref mdl;
    // Either point may be returned first; retain its exact x coordinate.
    ENSURE(ctx.optimize(asms) == l_true);
    ctx.get_model(mdl);
    expr_ref x1 = (*mdl)(x);
    ENSURE(a.is_irrational_algebraic_numeral(x1));
    // Blocking the first point must leave the other root, not a duplicate.
    ENSURE(ctx.optimize(asms) == l_true);
    ctx.get_model(mdl);
    expr_ref x2 = (*mdl)(x);
    ENSURE(a.is_irrational_algebraic_numeral(x2));
    ENSURE(x1 != x2);
    // Both feasible points have now been blocked, so enumeration is UNSAT.
    ENSURE(ctx.optimize(asms) == l_false);
}

static void tst_nearly_tied_front(bool reuse_nlsat_solver) {
    // Check that exact dominance comparisons keep two distinct Pareto points
    // even when their coordinates differ by only 10^-14, below the 12-digit
    // bracket used by rounded comparisons.
    std::cout << "opt_pareto: nearly tied front\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx, reuse_nlsat_solver);
    sort* real = a.mk_real();
    expr_ref x(m.mk_const(symbol("x"), real), m);
    expr_ref w(m.mk_const(symbol("w"), real), m);
    expr_ref r2(m.mk_const(symbol("r2"), real), m);
    expr_ref r3(m.mk_const(symbol("r3"), real), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref three(a.mk_numeral(rational(3), false), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    // Exact 10^-14, below the 10^-12 rounding bracket. Rational exponentiation
    // avoids narrowing a large integer literal or introducing floating-point rounding.
    expr_ref eps(a.mk_numeral(rational(1) / power(rational(10), 14), false), m);
    // Fix r2 = sqrt(2) and r3 = sqrt(3) by selecting their positive roots.
    ctx.add_hard_constraint(m.mk_eq(a.mk_mul(r2, r2), two));
    ctx.add_hard_constraint(a.mk_gt(r2, zero));
    ctx.add_hard_constraint(m.mk_eq(a.mk_mul(r3, r3), three));
    ctx.add_hard_constraint(a.mk_gt(r3, zero));
    // The choices are (sqrt(2), sqrt(3) - eps) and (sqrt(2) - eps, sqrt(3)).
    // Each is better in one coordinate and worse in the other.
    expr_ref pt1(m.mk_and(m.mk_eq(x, r2), m.mk_eq(w, a.mk_sub(r3, eps))), m);
    expr_ref pt2(m.mk_and(m.mk_eq(x, a.mk_sub(r2, eps)), m.mk_eq(w, r3)), m);
    ctx.add_hard_constraint(m.mk_or(pt1, pt2));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(w.get()), true);
    expr_ref_vector asms(m);
    // After returning one point, the nearly tied other point must remain SAT.
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(ctx.optimize(asms) == l_true);
    // Only these two points are feasible, so blocking both makes the next call UNSAT.
    ENSURE(ctx.optimize(asms) == l_false);
}

static void tst_uf_fallback(bool reuse_nlsat_solver) {
    // Check that an uninterpreted function forces the general SMT fallback
    // without losing either point of a rational Pareto front.
    std::cout << "opt_pareto: uf fallback\n";
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx, reuse_nlsat_solver);
    sort* real = a.mk_real();
    expr_ref x(m.mk_const(symbol("x"), real), m);
    expr_ref w(m.mk_const(symbol("w"), real), m);
    func_decl_ref f(m.mk_func_decl(symbol("f"), real, real), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref one(a.mk_numeral(rational(1), false), m);
    // Maximizing both coordinates makes (1, 0) and (0, 1) incomparable.
    expr_ref pt1(m.mk_and(m.mk_eq(x, one), m.mk_eq(w, zero)), m);
    expr_ref pt2(m.mk_and(m.mk_eq(x, zero), m.mk_eq(w, one)), m);
    ctx.add_hard_constraint(m.mk_or(pt1, pt2));
    // f(x) >= 0 is satisfiable at either point, but is outside pure NRA.
    ctx.add_hard_constraint(a.mk_ge(m.mk_app(f, x.get()), zero));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(w.get()), true);
    expr_ref_vector asms(m);
    // The SMT fallback must return both points, despite the extra UF constraint.
    ENSURE(ctx.optimize(asms) == l_true);
    ENSURE(ctx.optimize(asms) == l_true);
    // No third point remains after the two Pareto points have been blocked.
    ENSURE(ctx.optimize(asms) == l_false);
}

static unsigned counter(statistics const& st, char const* key) {
    // Treat a missing reuse-specific counter as zero on fresh/fallback paths.
    for (unsigned i = 0; i < st.size(); ++i)
        if (std::string(st.get_key(i)) == key)
            return st.get_uint_value(i);
    return 0;
}

static void tst_finite_front(bool reuse_nlsat_solver) {
    // Enumerate a known finite front without duplicates and check the reusable
    // solver's check and scope-retraction counts.
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx, reuse_nlsat_solver);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref y(m.mk_const("y", a.mk_real()), m);
    unsigned const bound = 12;
    expr_ref_vector choices(m), asms(m);
    // Restrict x to 0, ..., 12 and set y = 12 - x. Increasing x decreases y,
    // so all 13 feasible points belong to the max/max Pareto front.
    for (unsigned i = 0; i <= bound; ++i)
        choices.push_back(m.mk_eq(x, a.mk_numeral(rational(i), false)));
    ctx.add_hard_constraint(m.mk_or(choices.size(), choices.data()));
    ctx.add_hard_constraint(m.mk_eq(a.mk_add(x, y), a.mk_numeral(rational(bound), false)));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(y.get()), true);
    // Require 13 SAT models, each feasible and previously unseen; order is irrelevant.
    bool_vector seen(bound + 1, false);
    for (unsigned i = 0; i <= bound; ++i) {
        ENSURE(ctx.optimize(asms) == l_true);
        model_ref model;
        ctx.get_model(model);
        rational xv, yv;
        ENSURE(a.is_numeral((*model)(x), xv) && xv.is_unsigned());
        ENSURE(a.is_numeral((*model)(y), yv));
        ENSURE(xv + yv == rational(bound));
        ENSURE(xv <= rational(bound));
        unsigned k = xv.get_unsigned();
        ENSURE(!seen[k]);
        seen[k] = true;
    }
    // All feasible points have been returned and blocked, so the next call is UNSAT.
    ENSURE(ctx.optimize(asms) == l_false);
    // Each point needs a SAT candidate check and an UNSAT dominance check;
    // popping its dominance scope causes one retraction. Add one final UNSAT
    // check for exhaustion. Fresh solvers do not publish these reuse counters.
    statistics st;
    ctx.collect_statistics(st);
    ENSURE(counter(st, "pareto nlsat checks") == (reuse_nlsat_solver ? 2 * (bound + 1) + 1 : 0));
    ENSURE(counter(st, "pareto nlsat retractions") == (reuse_nlsat_solver ? bound + 1 : 0));
}

static void tst_mixed_directions(bool reuse_nlsat_solver) {
    // Check that Pareto dominance respects a mix of maximization and minimization.
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx, reuse_nlsat_solver);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref y(m.mk_const("y", a.mk_real()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    // The feasible points are (2, -2) and (-2, 2).
    ctx.add_hard_constraint(m.mk_or(m.mk_eq(x, two), m.mk_eq(x, a.mk_uminus(two))));
    ctx.add_hard_constraint(m.mk_eq(y, a.mk_uminus(x)));
    // Maximizing x and minimizing y both favor (2, -2), which dominates (-2, 2).
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(y.get()), false);
    expr_ref_vector asms(m);
    ENSURE(ctx.optimize(asms) == l_true);
    model_ref model;
    ctx.get_model(model);
    rational xv, yv;
    ENSURE(a.is_numeral((*model)(x), xv) && xv == rational(2));
    ENSURE(a.is_numeral((*model)(y), yv) && yv == rational(-2));
    // The blocker excludes the returned point and its dominated alternative: UNSAT.
    ENSURE(ctx.optimize(asms) == l_false);
}

static void tst_solver_scopes() {
    // Check that nested scopes and per-call assumptions retract cleanly in the
    // reusable nlsat solver, including after UNSAT and resource-limit unknown
    // results, and that saved algebraic models remain usable.
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    params_ref p;
    solver_ref s = opt::mk_pareto_nlsat_solver(m, p);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref positive(a.mk_gt(x, zero), m);
    expr_ref negative(a.mk_lt(x, zero), m);
    // Keep x^2 = 2 at the base level throughout: without sign restrictions,
    // either sqrt(2) or -sqrt(2) is feasible.
    s->assert_expr(m.mk_eq(a.mk_mul(x, x), two));
    // The outer scope selects x > 0; adding x < 0 in a nested scope is UNSAT.
    s->push();
    s->assert_expr(positive);
    s->push();
    s->assert_expr(negative);
    ENSURE(s->check_sat() == l_false);
    // Pop only x < 0. The remaining x^2 = 2 and x > 0 are SAT at sqrt(2).
    s->pop(1);
    ENSURE(s->check_sat() == l_true);
    model_ref model;
    s->get_model(model);
    ENSURE(model->is_true(positive));
    // Expose only x in the model, not the solver's internal scope constants.
    ENSURE(model->get_num_constants() == 1);
    // Pop x > 0 as well, leaving x^2 = 2, then select x < 0 in a new scope.
    // This must be SAT at -sqrt(2), with no positive-root restriction left over.
    s->pop(1);
    s->push();
    s->assert_expr(negative);
    ENSURE(s->check_sat() == l_true);
    s->get_model(model);
    ENSURE(model->is_true(negative));
    expr_ref value = (*model)(x);
    // Reuse the exact model value -sqrt(2) in a new assertion. With x^2 = 2
    // and x < 0 still active, x > -sqrt(2) excludes the only root: UNSAT.
    s->push();
    s->assert_expr(a.mk_gt(x, value));
    ENSURE(s->check_sat() == l_false);
    // The saved SAT model must still satisfy x^2 = 2 after the UNSAT check.
    ENSURE(model->is_true(m.mk_eq(a.mk_mul(x, x), two)));
    // Pop both the bound and x < 0. On the base formula, a per-call x > 0
    // assumption is SAT and selects the positive root.
    s->pop(2);
    expr_ref_vector assumptions(m);
    assumptions.push_back(positive);
    ENSURE(s->check_sat(assumptions) == l_true);
    s->get_model(model);
    ENSURE(model->is_true(positive));
    // The assumptions now contain both x > 0 and x < 0, so this call is UNSAT.
    assumptions.push_back(negative);
    ENSURE(s->check_sat(assumptions) == l_false);
    // With no assumptions, x^2 = 2 is SAT again: neither assumption may leak.
    ENSURE(s->check_sat() == l_true);
    // Force an unknown result with a tiny resource limit, not a contradiction,
    // and require the solver to explain why it could not finish.
    s->push();
    {
        scoped_rlimit limit(m.limit(), 1);
        ENSURE(s->check_sat() == l_undef);
        ENSURE(!s->reason_unknown().empty());
    }
    // With the temporary limit gone, pop the scope and recover a SAT result.
    s->pop(1);
    ENSURE(s->check_sat() == l_true);
}

static void tst_cancelled_solver() {
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    params_ref p;
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref y(m.mk_const("y", a.mk_real()), m);
    expr_ref z(m.mk_const("z", a.mk_real()), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref five(a.mk_numeral(rational(5), false), m);
    expr_ref square(a.mk_mul(x, x), m);
    expr_ref_vector constraints(m);
    constraints.push_back(m.mk_eq(y, zero));
    constraints.push_back(m.mk_eq(z, five));
    constraints.push_back(a.mk_gt(a.mk_add(a.mk_mul(y, square), x), z));
    constraints.push_back(m.mk_eq(square, a.mk_mul(z, x)));
    auto make_solver = [&]() {
        solver_ref s = opt::mk_pareto_nlsat_solver(m, p);
        s->assert_expr(constraints);
        s->push();
        return s;
    };
    // With y = 0 and z = 5, x > 5 excludes both roots of x^2 = 5*x.
    auto full = make_solver();
    auto start = m.limit().count();
    ENSURE(full->check_sat() == l_false);
    ENSURE(m.limit().count() - start <= UINT_MAX);
    unsigned max_budget = static_cast<unsigned>(m.limit().count() - start);
    bool interrupted = false;
    for (unsigned budget = 1; budget <= max_budget; ++budget) {
        auto s = make_solver();
        {
            scoped_rlimit limit(m.limit(), budget);
            lbool result = s->check_sat();
            ENSURE(result == l_false || result == l_undef);
            if (result == l_undef) {
                ENSURE(m.limit().is_canceled());
                ENSURE(!s->reason_unknown().empty());
                interrupted = true;
            }
        }
        // Sweep cancellation through preprocessing and search. The permanent
        // conflict survives this empty scope, so recovery must still prove UNSAT.
        s->pop(1);
        ENSURE(s->check_sat() == l_false);
    }
    ENSURE(interrupted);
}

static void tst_reuse_fragment() {
    // Check which arithmetic terms are eligible for the reusable nlsat path.
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref i(m.mk_const("i", a.mk_int()), m);
    expr_ref two(a.mk_numeral(rational(2), false), m);
    expr_ref_vector terms(m);
    // Division by a nonzero numeral is polynomial arithmetic up to scaling.
    terms.push_back(a.mk_div(x, two));
    ENSURE(opt::can_reuse_nlsat_solver(terms));
    // Adding 2/x introduces a variable denominator, so the whole vector is rejected.
    terms.push_back(a.mk_div(two, x));
    ENSURE(!opt::can_reuse_nlsat_solver(terms));
    // Start an independent case: to_real(i) still contains an integer variable
    // and must not enter the real-only reuse fragment.
    terms.reset();
    terms.push_back(a.mk_to_real(i));
    ENSURE(!opt::can_reuse_nlsat_solver(terms));
}

static void tst_sampled_fronts() {
    // For each seed s in {0, ..., 15}, generate the finite feasible set
    //
    //   u(s, i) = (3*s + 5*i) mod 11 - 5,
    //   v(s, i) = (s + i*i + 3*i) mod 9 - 4,       i in {0, ..., 7},
    //   c(s)    = sqrt(2) if bit 2 of s is set, and 1 otherwise,
    //   F(s)    = { c(s) * (u(s, i), v(s, i)) : i in {0, ..., 7} }.
    //
    // The problem is to Pareto-optimize x and y subject to (x, y) in F(s).
    // Bit 0 selects max x when set and min x otherwise; bit 1 does the same
    // for y. If sign_x is 1 for max and -1 for min (and likewise for sign_y),
    // then q dominates p exactly when
    //
    //   sign_x*q.x >= sign_x*p.x  and  sign_y*q.y >= sign_y*p.y,
    //
    // with at least one strict inequality. The expected front consists of all
    // p in F(s) for which no such q exists. The full seed varies the points;
    // its low bits additionally select the four direction pairs and the scale.
    // Every problem is run with fresh and reused nlsat, for 32 solver runs.
    //
    // Compute the expected front with plain integer comparisons, independently
    // of Z3, and store its point indices in front. Ask Z3 to return exactly
    // those points in any order, without duplicates, with fresh and reused
    // nlsat solvers. Positive scaling preserves the expected front while
    // exercising both rational and algebraic coordinates.
    struct point { int x, y; };
    for (unsigned seed = 0; seed < 16; ++seed) {
        // Vary the point set reproducibly; the seed's low two bits choose the
        // four combinations of objective directions.
        svector<point> points;
        for (unsigned i = 0; i < 8; ++i)
            points.push_back({static_cast<int>((3 * seed + 5 * i) % 11) - 5,
                              static_cast<int>((seed + i * i + 3 * i) % 9) - 4});
        bool max_x = (seed & 1) != 0, max_y = (seed & 2) != 0;
        unsigned_vector front;
        // A point j dominates i only if j is no worse in either objective and
        // strictly better in at least one. Keep exactly the undominated points.
        for (unsigned i = 0; i < points.size(); ++i) {
            bool dominated = false;
            for (unsigned j = 0; j < points.size(); ++j) {
                if (i == j)
                    continue;
                bool better_x = max_x ? points[j].x >= points[i].x : points[j].x <= points[i].x;
                bool better_y = max_y ? points[j].y >= points[i].y : points[j].y <= points[i].y;
                dominated |= better_x && better_y &&
                    (points[j].x != points[i].x || points[j].y != points[i].y);
            }
            if (!dominated)
                front.push_back(i);
        }
        // Run the same instance with a fresh-per-check and a reusable nlsat solver.
        for (bool reuse_nlsat_solver : {false, true}) {
            ast_manager m;
            reg_decl_plugins(m);
            arith_util a(m);
            opt::context ctx(m);
            set_pareto_priority(ctx, reuse_nlsat_solver);
            expr_ref x(m.mk_const("x", a.mk_real()), m);
            expr_ref y(m.mk_const("y", a.mk_real()), m);
            // Use scale 1 or positive sqrt(2). A common positive scale preserves
            // the oracle's ordering while adding cases with algebraic coordinates.
            expr_ref scale(a.mk_numeral(rational(1), false), m);
            if (seed & 4) {
                scale = m.mk_const("scale", a.mk_real());
                ctx.add_hard_constraint(m.mk_eq(a.mk_mul(scale, scale), a.mk_numeral(rational(2), false)));
                ctx.add_hard_constraint(a.mk_gt(scale, a.mk_numeral(rational(0), false)));
            }
            auto coordinate = [&](int k) {
                return expr_ref(a.mk_mul(a.mk_numeral(rational(k), false), scale), m);
            };
            // Admit exactly the scaled sample points, with the chosen min/max directions.
            expr_ref_vector choices(m), asms(m);
            for (point const& p : points)
                choices.push_back(m.mk_and(m.mk_eq(x, coordinate(p.x)), m.mk_eq(y, coordinate(p.y))));
            ctx.add_hard_constraint(m.mk_or(choices.size(), choices.data()));
            ctx.add_objective(to_app(x.get()), max_x);
            ctx.add_objective(to_app(y.get()), max_y);
            // Match each result to a previously unseen oracle point using exact
            // model equalities; do not assume any enumeration order.
            bool_vector seen(front.size(), false);
            for (unsigned i = 0; i < front.size(); ++i) {
                ENSURE(ctx.optimize(asms) == l_true);
                model_ref model;
                ctx.get_model(model);
                bool found = false;
                for (unsigned j = 0; j < front.size(); ++j) {
                    point const& p = points[front[j]];
                    if (model->is_true(m.mk_eq(x, coordinate(p.x))) && model->is_true(m.mk_eq(y, coordinate(p.y)))) {
                        ENSURE(!seen[j]);
                        seen[j] = true;
                        found = true;
                    }
                }
                ENSURE(found);
            }
            // Pareto enumeration retains blockers for each returned point and
            // every point it dominates. Once the entire front has been returned,
            // all feasible samples are blocked, so the next call must be UNSAT.
            // This means enumeration is exhausted, not that the original problem
            // was infeasible: even with empty asms, the context keeps its blockers.
            ENSURE(ctx.optimize(asms) == l_false);
        }
    }
}

static void tst_assumption_fallback() {
    // Check that Optimize calls with assumptions use the SMT fallback and
    // enumerate only the Pareto front permitted by those assumptions.
    ast_manager m;
    reg_decl_plugins(m);
    arith_util a(m);
    opt::context ctx(m);
    set_pareto_priority(ctx);
    expr_ref x(m.mk_const("x", a.mk_real()), m);
    expr_ref y(m.mk_const("y", a.mk_real()), m);
    expr_ref zero(a.mk_numeral(rational(0), false), m);
    expr_ref one(a.mk_numeral(rational(1), false), m);
    // Without assumptions, the max/max front consists of (0, 1) and (1, 0).
    ctx.add_hard_constraint(m.mk_or(m.mk_and(m.mk_eq(x, zero), m.mk_eq(y, one)),
                                    m.mk_and(m.mk_eq(x, one), m.mk_eq(y, zero))));
    ctx.add_objective(to_app(x.get()), true);
    ctx.add_objective(to_app(y.get()), true);
    expr_ref_vector asms(m);
    // Assuming x = 1 excludes (0, 1), leaving only (1, 0) as a SAT front point.
    asms.push_back(m.mk_eq(x, one));
    ENSURE(ctx.optimize(asms) == l_true);
    model_ref model;
    ctx.get_model(model);
    ENSURE(model->is_true(asms.get(0)));
    // Under the same assumption, blocking (1, 0) leaves no feasible point: UNSAT.
    ENSURE(ctx.optimize(asms) == l_false);
    // Assumption handling must not invoke the reusable nlsat solver.
    statistics st;
    ctx.collect_statistics(st);
    ENSURE(counter(st, "pareto nlsat checks") == 0);
}

void tst_opt_pareto() {
    // Cover solver state, fragment selection, and Pareto enumeration/fallback.
    tst_solver_scopes();
    tst_cancelled_solver();
    tst_reuse_fragment();
    // Sampled fronts already exercise both nlsat modes; assumptions force SMT.
    tst_sampled_fronts();
    tst_assumption_fallback();
    // Run the remaining front tests with and without nlsat reuse. The UF case
    // must stay on the general SMT solver regardless of this setting.
    for (bool reuse_nlsat_solver : {false, true}) {
        tst_irrational_front(reuse_nlsat_solver);
        tst_nearly_tied_front(reuse_nlsat_solver);
        tst_uf_fallback(reuse_nlsat_solver);
        tst_finite_front(reuse_nlsat_solver);
        tst_mixed_directions(reuse_nlsat_solver);
    }
}

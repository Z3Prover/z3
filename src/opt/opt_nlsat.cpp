/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_nlsat.cpp

Abstract:

    Exact optimization of a real-valued objective over quantifier-free
    nonlinear real arithmetic using nlsat cells. See opt_nlsat.h.

Author:

    Lev Nachmanson 2026-08-25

--*/
#include "opt/opt_nlsat.h"
#include "util/common_msgs.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/expr2var.h"
#include "ast/occurs.h"
#include "ast/for_each_expr.h"
#include "ast/converters/model_converter.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/tactic/goal2nlsat.h"
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "tactic/core/tseitin_cnf_tactic.h"
#include "tactic/arith/purify_arith_tactic.h"

namespace opt {

    nlsat_opt::nlsat_opt(ast_manager& m, params_ref const& p):
        m(m), m_params(p), m_arith(m) {}

    void nlsat_opt::result::reset() {
        m_value = nullptr;
        m_model = nullptr;
        m_attained = false;
        m_unbounded = false;
        m_has_sup = false;
        m_open = false;
        m_sup = nullptr;
        m_rounds = 0;
    }

    // Find rational bounds that isolate value from neighboring polynomial roots.
    // Coarse bounds avoid large dyadic coefficients in downstream queries.
    static void coarse_isolating_interval(ast_manager& m, algebraic_numbers::manager& am, anum const& value,
                                          svector<mpz>& coeffs, rational& lower, rational& upper) {
        polynomial::manager pm(m.limit(), am.qm());
        polynomial::var x = pm.mk_var();
        polynomial_ref p(pm);
        p = pm.mk_univariate(x, coeffs.size() - 1, coeffs.data());
        scoped_anum_vector roots(am);
        am.isolate_roots(p, roots);
        unsigned j = 0;
        while (j < roots.size() && !am.eq(roots[j], value))
            ++j;
        // coeffs should define value, so this is only a defensive fallback.
        // If no matching root is found, reuse value's own isolating interval.
        if (j == roots.size()) {
            am.get_interval(value, lower, upper);
            return;
        }
        // Here value is roots[j]. Put each bound between value and its
        // neighboring root, or beyond value when no neighbor exists.
        scoped_anum lo(am), hi(am);
        if (j == 0)
            am.int_lt(value, lo);
        else
            am.select(roots[j-1], value, lo);
        if (j + 1 == roots.size())
            am.int_gt(value, hi);
        else
            am.select(value, roots[j+1], hi);
        am.to_rational(lo, lower);
        am.to_rational(hi, upper);
    }

    expr_ref mk_algebraic_eq(ast_manager& m, expr* term, expr* value) {
        arith_util a(m);
        SASSERT(a.is_real(term));
        rational q;
        if (a.is_numeral(value, q))
            return expr_ref(m.mk_eq(term, a.mk_numeral(q, false)), m);
        SASSERT(a.is_irrational_algebraic_numeral(value));
        auto& am = a.am();
        anum const& number = a.to_irrational_algebraic_numeral(value);
        svector<mpz> coeffs;
        am.get_polynomial(number, coeffs);
        expr_ref poly(m);
        for (unsigned k = coeffs.size(); k-- > 0; ) {
            expr_ref c(a.mk_numeral(rational(coeffs[k]), false), m);
            poly = poly ? a.mk_add(a.mk_mul(poly, term), c) : c;
        }
        rational lower, upper;
        coarse_isolating_interval(m, am, number, coeffs, lower, upper);
        expr_ref_vector constraints(m);
        constraints.push_back(m.mk_eq(poly, a.mk_numeral(rational(0), false)));
        constraints.push_back(a.mk_ge(term, a.mk_numeral(lower, false)));
        constraints.push_back(a.mk_le(term, a.mk_numeral(upper, false)));
        return mk_and(constraints);
    }

    template<typename Query>
    static lbool bounded_limit_query(ast_manager& m, unsigned ticks, Query const& query) {
        if (ticks == 0) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat finite-limit check disabled)\n");
            return l_undef;
        }
        // Pushing a resource scope clears the cancellation flag, so do not
        // enter one when the enclosing operation has already been canceled.
        if (!m.inc())
            return l_undef;
        lbool result = l_undef;
        bool external_cancel = false;
        uint64_t start = m.limit().count(), consumed = 0;
        {
            scoped_rlimit budget(m.limit(), ticks);
            try {
                result = query();
            }
            catch (tactic_exception& ex) {
                IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat finite-limit check failed: " << ex.what() << ")\n");
            }
            catch (z3_exception& ex) {
                if (!m.limit().is_canceled())
                    throw;
                IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat finite-limit check interrupted: " << ex.what() << ")\n");
            }
            external_cancel = m.limit().get_cancel_msg() == Z3_CANCELED_MSG;
            consumed = m.limit().count() - start;
        }
        // Popping the private budget must not swallow a timeout or Ctrl-C.
        if (external_cancel)
            m.limit().cancel();
        IF_VERBOSE(3, verbose_stream() << "(optsmt nlsat finite-limit check :result " << result
                   << " :rlimit-consumed " << consumed << " :budget " << ticks << ")\n");
        return result;
    }

    /**
       \brief The fragment nlsat decides: Boolean structure over polynomial
       arithmetic atoms, with uninterpreted constants as the only free symbols.
       Uninterpreted functions of positive arity are rejected because nlsat
       would treat their applications as unrelated variables (no congruence).
    */
    struct nra_fragment_check {
        ast_manager& m;
        arith_util&  a;
        bool         ok = true;
        nra_fragment_check(ast_manager& m, arith_util& a): m(m), a(a) {}
        void operator()(var*) { ok = false; }
        void operator()(quantifier*) { ok = false; }
        void operator()(app* n) {
            if (!ok)
                return;
            family_id fid = n->get_family_id();
            if (fid == m.get_basic_family_id() || fid == a.get_family_id())
                ;
            else if (fid == null_family_id && n->get_num_args() == 0)
                ;
            else
                ok = false;
            sort* s = n->get_sort();
            if (!m.is_bool(s) && !a.is_real(s) && !a.is_int(s))
                ok = false;
        }
    };

    bool in_nra_fragment(ast_manager& m, arith_util& a, expr_ref_vector const& hard, expr* obj) {
        nra_fragment_check chk(m, a);
        expr_fast_mark1 visited;
        for (expr* f : hard) {
            for_each_expr_core<nra_fragment_check, expr_fast_mark1, false, false>(chk, visited, f);
            if (!chk.ok)
                return false;
        }
        for_each_expr_core<nra_fragment_check, expr_fast_mark1, false, false>(chk, visited, obj);
        return chk.ok;
    }

    lbool nlsat_opt::can_approach_from_below(expr_ref_vector const& hard, expr* obj, rational const& lo,
                                            expr* bound, unsigned rlimit_budget) {
        return bounded_limit_query(m, rlimit_budget, [&]() {
            if (!m_arith.is_real(obj) || !in_nra_fragment(m, m_arith, hard, obj)) {
                IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat finite-limit check: outside NRA)\n");
                return l_undef;
            }
            app_ref T(m);
            goal_ref pg;
            lbool st = preprocess(hard, obj, lo, std::nullopt, T, pg);
            if (st != l_true)
                return st;
            return can_approach_from_below(*pg, T, bound);
        });
    }

    lbool nlsat_opt::can_approach_from_below(goal const& pg, app* T, expr* bound) {
        rational q;
        if (!bound || (!m_arith.is_numeral(bound, q) && !m_arith.is_irrational_algebraic_numeral(bound))) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat finite-limit check: bound is not a numeral)\n");
            return l_undef;
        }
        return check_limit(pg, T, bound);
    }

    lbool nlsat_opt::prove_unbounded(expr_ref_vector const& hard, expr* obj, rational const& lo) {
        if (!in_nra_fragment(m, m_arith, hard, obj))
            return l_undef;
        // Normalize through the same pipeline as maximize: the assertions may
        // contain division and other non-polynomial arithmetic that
        // purification removes.
        app_ref T(m);
        goal_ref pg;
        lbool st = preprocess(hard, obj, lo, std::nullopt, T, pg);
        if (st == l_false)
            return l_false;   // no model with obj >= lo: lo bounds obj from above
        if (st != l_true)
            return l_undef;
        return prove_unbounded(*pg, T);
    }

    lbool nlsat_opt::prove_unbounded(goal const& pg, app* T) {
        return check_limit(pg, T, nullptr);
    }

    lbool nlsat_opt::check_limit(goal const& pg, app* T, expr* bound) {
        nlsat::solver s(m.limit(), m_params, true);
        nlsat::var t;
        expr_ref_vector x2t(m), b2a(m);
        if (!load(pg, T, s, t, x2t, b2a))
            return l_undef;
        scoped_anum limit(s.am());
        if (bound) {
            rational q;
            if (m_arith.is_numeral(bound, q))
                s.am().set(limit, q.to_mpq());
            else
                s.am().set(limit, m_arith.to_irrational_algebraic_numeral(bound));
        }
        return s.check_limit(t, bound ? &limit.get() : nullptr);
    }

    /**
       \brief Build hard /\ T = obj /\ lo <= T <= hi and normalize it for
       goal2nlsat (purified arithmetic, no term-ite, CNF). T is a fresh
       constant that only occurs in these three assertions, so no
       preprocessing step can substitute it away except by eliminating the
       objective. Returns l_true with the preprocessed goal in pg, l_false if
       preprocessing refutes the goal, and l_undef if preprocessing fails or
       loses T.
    */
    lbool nlsat_opt::preprocess(expr_ref_vector const& hard, expr* obj, rational const& lo, std::optional<rational> const& hi,
                                app_ref& T, goal_ref& pg) {
        T = m.mk_fresh_const("opt.nlsat.obj", m_arith.mk_real());
        goal_ref g = alloc(goal, m, false, true, false);
        for (expr* f : hard)
            g->assert_expr(f);
        g->assert_expr(m.mk_eq(T, obj));
        g->assert_expr(m_arith.mk_ge(T, m_arith.mk_numeral(lo, false)));
        if (hi)
            g->assert_expr(m_arith.mk_le(T, m_arith.mk_numeral(*hi, false)));

        params_ref simp_p;
        simp_p.set_bool("elim_and", true);
        simp_p.set_bool("blast_distinct", true);
        params_ref purify_p;
        purify_p.set_bool("complete", false);
        tactic_ref pre = and_then(using_params(mk_simplify_tactic(m), simp_p),
                                  using_params(mk_purify_arith_tactic(m), purify_p),
                                  mk_propagate_values_tactic(m),
                                  mk_elim_term_ite_tactic(m),
                                  using_params(mk_purify_arith_tactic(m), purify_p),
                                  using_params(mk_simplify_tactic(m), simp_p),
                                  mk_tseitin_cnf_core_tactic(m),
                                  using_params(mk_simplify_tactic(m), simp_p));
        goal_ref_buffer pre_result;
        try {
            (*pre)(g, pre_result);
        }
        catch (tactic_exception& ex) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: preprocessing failed: " << ex.what() << ")\n");
            return l_undef;
        }
        if (pre_result.size() != 1)
            return l_undef;
        pg = pre_result[0];
        if (pg->inconsistent())
            return l_false;
        for (unsigned i = 0; i < pg->size(); ++i)
            if (occurs(T, pg->form(i)))
                return l_true;
        return l_undef;
    }

    /**
       \brief Load the preprocessed goal into s with T as the first variable
       and the maximization target. On return t is T's nlsat variable and
       x2t, b2a map nlsat arithmetic and Boolean variables back to terms and
       atoms. Returns false if goal2nlsat rejects the goal.
    */
    bool nlsat_opt::load(goal const& pg, app* T, nlsat::solver& s, nlsat::var& t, expr_ref_vector& x2t, expr_ref_vector& b2a) {
        expr2var a2b(m), t2x(m);
        t = s.mk_var(false);
        t2x.insert(T, t);
        goal2nlsat g2n;
        try {
            g2n(pg, m_params, s, a2b, t2x);
        }
        catch (tactic_exception& ex) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: unsupported: " << ex.what() << ")\n");
            return false;
        }
        s.set_max_var(t);
        t2x.mk_inv(x2t);
        a2b.mk_inv(b2a);
        return true;
    }

    /**
       \brief The literal t > v (strict) or t >= v (!strict): a linear
       inequality when v is rational, otherwise a root atom on the defining
       polynomial of v. Returns null_literal if the root index of v cannot
       be recovered from the polynomial.
    */
    static nlsat::literal mk_lower_bound(nlsat::solver& s, nlsat::var t, anum const& v, bool strict) {
        algebraic_numbers::manager& am = s.am();
        polynomial::manager& pm = s.pm();
        polynomial_ref p(pm);
        if (am.is_rational(v)) {
            rational q;
            am.to_rational(v, q);
            rational d = denominator(q), n = -numerator(q);   // d*t - n > 0  <=>  t > q
            p = pm.mk_linear(1, &d, &t, n);
            polynomial::polynomial* pp = p.get();
            bool is_even = false;
            if (strict)
                return s.mk_ineq_literal(nlsat::atom::GT, 1, &pp, &is_even);
            return ~s.mk_ineq_literal(nlsat::atom::LT, 1, &pp, &is_even);   // !(t < q)
        }
        svector<mpz> coeffs;
        am.get_polynomial(v, coeffs);
        p = pm.mk_univariate(t, coeffs.size() - 1, coeffs.data());   // consumes coeffs
        scoped_anum_vector roots(am);
        am.isolate_roots(p, roots);
        for (unsigned k = 0; k < roots.size(); ++k)
            if (am.eq(roots[k], v))
                return nlsat::literal(s.mk_root_atom(strict ? nlsat::atom::ROOT_GT : nlsat::atom::ROOT_GE, t, k + 1, p.get()), false);
        return nlsat::null_literal;
    }

    /**
       \brief The model of the preprocessed goal from the current nlsat
       assignment, mapped back through the model converter.
    */
    model_ref nlsat_opt::extract_model(nlsat::solver& s, expr_ref_vector const& x2t, expr_ref_vector const& b2a, app* T,
                                       model_converter* mc) {
        algebraic_numbers::manager& am = s.am();
        model_ref md = alloc(model, m);
        for (unsigned x = 0; x < x2t.size(); ++x) {
            expr* e = x2t.get(x);
            if (!e || !is_uninterp_const(e) || e == T)
                continue;
            expr_ref v(m);
            try {
                v = m_arith.mk_numeral(am, s.value(x), m_arith.is_int(e));
            }
            catch (z3_exception&) {
                v = m_arith.mk_to_int(m_arith.mk_numeral(am, s.value(x), false));
            }
            md->register_decl(to_app(e)->get_decl(), v);
        }
        for (unsigned b = 0; b < b2a.size(); ++b) {
            expr* a = b2a.get(b);
            if (!a || !is_uninterp_const(a))
                continue;
            lbool val = s.bvalue(b);
            if (val == l_undef)
                continue;
            md->register_decl(to_app(a)->get_decl(), val == l_true ? m.mk_true() : m.mk_false());
        }
        if (mc)
            (*mc)(md);
        return md;
    }

    /**
       \brief The round budget was exhausted at a model below an open
       candidate supremum sup. Refuting t >= sup proves a strict upper
       bound, but not that feasible values approach it. Record this partial
       result even if the separate projected limit check cannot finish.
    */
    void nlsat_opt::prove_strict_upper_bound(nlsat::solver& s, nlsat::var t, anum const& sup, anum const& best, result& res) {
        algebraic_numbers::manager& am = s.am();
        if (!am.gt(sup, best))
            return;
        nlsat::literal l = mk_lower_bound(s, t, sup, false);
        if (l == nlsat::null_literal)
            return;
        s.mk_clause(1, &l);
        lbool st = s.check();
        IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat sup-check "; am.display_root_smt2(verbose_stream(), sup); verbose_stream() << " " << st << ")\n");
        if (st != l_false)
            return;
        set_value(am, sup, res.m_sup, res.m_sup_lower, res.m_sup_upper);
        res.m_has_sup = true;
    }

    /**
       \brief Store a numeral with a rational bracket.
    */
    void nlsat_opt::set_value(algebraic_numbers::manager& am, anum const& value,
                             expr_ref& numeral, rational& lower, rational& upper) {
        numeral = m_arith.mk_numeral(am, value, false);
        // is_rational turns value into a basic cell when it succeeds, so the exact
        // bound is available; otherwise one refinement yields both bracket ends.
        if (am.is_rational(value)) {
            am.to_rational(value, lower);
            upper = lower;
        }
        else
            am.get_interval(value, lower, upper, 40);
    }

    // Keep one call's solver, translation maps, and search outcome together.
    struct nlsat_opt::search_state {
        goal_ref m_goal;
        app_ref m_objective;
        model_converter_ref m_converter;
        nlsat::solver m_solver;
        nlsat::var m_variable = nlsat::null_var;
        expr_ref_vector m_x2t, m_b2a;
        // The solver owns their number manager and must outlive these values.
        scoped_anum m_best, m_sup;
        bool const m_has_upper_bound;
        bool m_has_best = false;
        bool m_has_sup = false; // a candidate endpoint, not yet a global upper-bound proof
        lbool m_status = l_undef;

        search_state(ast_manager& m, params_ref const& p, goal* pg, app* objective, bool has_upper_bound):
            m_goal(pg),
            m_objective(objective, m),
            m_converter(pg->mc()),
            m_solver(m.limit(), p, true),
            m_x2t(m), m_b2a(m),
            m_best(m_solver.am()), m_sup(m_solver.am()),
            m_has_upper_bound(has_upper_bound) {}

        search_state(search_state const&) = delete;
        search_state& operator=(search_state const&) = delete;
    };

    // Improve the model and remember the candidate endpoint. After five
    // consecutive rounds without one, probe unboundedness if no upper bound was supplied.
    void nlsat_opt::search_models(search_state& state, unsigned max_rounds, result& res) {
        auto& s = state.m_solver;
        auto& am = s.am();
        unsigned unbounded_rounds = 0;
        for (unsigned round = 0; round < max_rounds && m.inc(); ++round) {
            res.m_rounds = round + 1;
            state.m_status = s.check();
            TRACE(opt, tout << "nlsat round " << round << ": " << state.m_status << "\n";);
            if (state.m_status != l_true)
                break;
            am.set(state.m_best, s.value(state.m_variable));
            state.m_has_best = true;
            bool attained = false;
            state.m_has_sup = s.max_var_sup(state.m_sup, attained);
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat round " << round << " value "; am.display_root_smt2(verbose_stream(), state.m_best);
                       verbose_stream() << (attained ? " sup" : " below-sup") << ")\n");
            res.m_model = extract_model(s, state.m_x2t, state.m_b2a, state.m_objective, state.m_converter.get());
            if (!state.m_has_sup) {
                // Bounds involving later-assigned variables reach t through
                // conflict learning. An unbounded-looking interval alone is
                // inconclusive; without a supplied upper bound, check
                // for a projected feasible ray.
                if (++unbounded_rounds > 4) {
                    IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: feasible set unbounded above)\n");
                    if (!state.m_has_upper_bound && prove_unbounded(*state.m_goal, state.m_objective) == l_true) {
                        res.m_unbounded = true;
                        IF_VERBOSE(1, verbose_stream() << "(optsmt nlsat: objective proven unbounded above)\n");
                    }
                    break;
                }
            }
            else
                unbounded_rounds = 0;
            nlsat::literal l = mk_lower_bound(s, state.m_variable, state.m_best, true);
            if (l == nlsat::null_literal) {
                IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: root index not found)\n");
                state.m_status = l_undef;
                break;
            }
            s.mk_clause(1, &l);
            IF_VERBOSE(4, s.display(verbose_stream() << "(optsmt nlsat state after blocking)\n") << "\n");
        }
    }

    // Fill the result from the search outcome, then certify a remaining finite candidate.
    lbool nlsat_opt::certify_result(search_state& state, unsigned supremum_rlimit, result& res) {
        if (!state.m_has_best)
            return state.m_status == l_false ? l_false : l_undef;

        // Keep the feasible model value separate from an unattained limit.
        set_value(state.m_solver.am(), state.m_best, res.m_value, res.m_lower, res.m_upper);
        res.m_attained = state.m_status == l_false;
        if (state.m_status == l_true && state.m_has_sup) {
            prove_strict_upper_bound(state.m_solver, state.m_variable, state.m_sup, state.m_best, res);
            if (res.m_has_sup)
                res.m_open = bounded_limit_query(m, supremum_rlimit, [&]() {
                    return can_approach_from_below(*state.m_goal, state.m_objective, res.m_sup);
                }) == l_true;
        }
        return res.m_attained || res.m_unbounded || res.m_open ? l_true : l_undef;
    }

    lbool nlsat_opt::maximize(expr_ref_vector const& hard, expr* obj, rational const& lo, std::optional<rational> const& hi,
                              unsigned max_rounds, result& res, unsigned supremum_rlimit) {
        res.reset();
        if (!in_nra_fragment(m, m_arith, hard, obj)) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: outside the nonlinear real arithmetic fragment)\n");
            return l_undef;
        }

        // Inconsistent or unsupported goals need no solver allocation.
        app_ref T(m);
        goal_ref pg;
        lbool st = preprocess(hard, obj, lo, hi, T, pg);
        if (st != l_true)
            return st;

        search_state state(m, m_params, pg.get(), T.get(), hi.has_value());
        if (!load(*state.m_goal, state.m_objective, state.m_solver, state.m_variable, state.m_x2t, state.m_b2a))
            return l_undef;

        search_models(state, max_rounds, res);
        return certify_result(state, supremum_rlimit, res);
    }
}

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
#include "ast/ast_pp.h"
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
        m_has_sup = false;
        m_rounds = 0;
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

    static bool in_nra_fragment(ast_manager& m, arith_util& a, expr_ref_vector const& hard, expr* obj) {
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

    /**
       \brief Build hard /\ T = obj /\ lo <= T <= hi and normalize it for
       goal2nlsat (purified arithmetic, no term-ite, CNF). T is a fresh
       constant that only occurs in these three assertions, so no
       preprocessing step can substitute it away except by eliminating the
       objective. Returns l_true with the preprocessed goal in pg, l_false if
       preprocessing refutes the goal, and l_undef if preprocessing fails or
       loses T.
    */
    lbool nlsat_opt::preprocess(expr_ref_vector const& hard, expr* obj, rational const& lo, bool has_hi, rational const& hi,
                                app_ref& T, goal_ref& pg) {
        T = m.mk_fresh_const("opt.nlsat.obj", m_arith.mk_real());
        goal_ref g = alloc(goal, m, false, true, false);
        for (expr* f : hard)
            g->assert_expr(f);
        g->assert_expr(m.mk_eq(T, obj));
        g->assert_expr(m_arith.mk_ge(T, m_arith.mk_numeral(lo, false)));
        if (has_hi)
            g->assert_expr(m_arith.mk_le(T, m_arith.mk_numeral(hi, false)));

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
       supremum r of the feasible set of t. Check whether t >= r has a model;
       if not, r is a proven upper bound (F-Close at the supremum) and is
       recorded in res.
    */
    static void prove_supremum(nlsat::solver& s, nlsat::var t, anum const& best, nlsat_opt::result& res) {
        algebraic_numbers::manager& am = s.am();
        scoped_anum r(am);
        am.set(r, s.max_var_sup());
        if (!am.gt(r, best))
            return;
        nlsat::literal l = mk_lower_bound(s, t, r, false);
        if (l == nlsat::null_literal)
            return;
        s.mk_clause(1, &l);
        lbool st = s.check();
        IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat sup-check "; am.display_root_smt2(verbose_stream(), r); verbose_stream() << " " << st << ")\n");
        if (st != l_false)
            return;
        res.m_has_sup = true;
        if (am.is_rational(r))
            am.to_rational(r, res.m_sup_upper);
        else
            am.get_upper(r, res.m_sup_upper, 40);
    }

    /**
       \brief Report best as the exact value with a rational bracket.
    */
    void nlsat_opt::set_result(algebraic_numbers::manager& am, anum const& best, bool attained, result& res) {
        res.m_value = m_arith.mk_numeral(am, best, false);
        if (am.is_rational(best)) {
            am.to_rational(best, res.m_lower);
            res.m_upper = res.m_lower;
        }
        else {
            am.get_lower(best, res.m_lower, 40);
            am.get_upper(best, res.m_upper, 40);
        }
        res.m_attained = attained;
    }

    lbool nlsat_opt::maximize(expr_ref_vector const& hard, expr* obj, rational const& lo, bool has_hi, rational const& hi,
                              unsigned max_rounds, result& res) {
        res.reset();
        if (!in_nra_fragment(m, m_arith, hard, obj)) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: outside the nonlinear real arithmetic fragment)\n");
            return l_undef;
        }

        // 1. hard /\ T = obj /\ lo <= T <= hi, normalized for goal2nlsat.
        app_ref T(m);
        goal_ref pg;
        lbool st = preprocess(hard, obj, lo, has_hi, hi, T, pg);
        if (st != l_true)
            return st;
        model_converter_ref mc = pg->mc();

        // 2. nlsat with T as the first variable and maximization target.
        nlsat::solver s(m.limit(), m_params, true);
        nlsat::var t;
        expr_ref_vector x2t(m), b2a(m);
        if (!load(*pg, T, s, t, x2t, b2a))
            return l_undef;
        algebraic_numbers::manager& am = s.am();

        // 3. F-Sat / F-Close loop: each model is blocked by t > value.
        scoped_anum best(am);
        bool has_best = false;
        unsigned unbounded_rounds = 0;
        st = l_undef;
        for (unsigned round = 0; round < max_rounds && m.inc(); ++round) {
            res.m_rounds = round + 1;
            st = s.check();
            TRACE(opt, tout << "nlsat round " << round << ": " << st << "\n";);
            if (st != l_true)
                break;
            am.set(best, s.value(t));
            has_best = true;
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat round " << round << " value "; am.display_root_smt2(verbose_stream(), best); 
                       verbose_stream() << (s.max_var_attained() ? " sup" : " below-sup") << ")\n");
            res.m_model = extract_model(s, x2t, b2a, T, mc.get());
            if (s.max_var_unbounded()) {
                // The feasible set of t was unbounded above when t was
                // assigned: nothing nlsat has learned so far bounds the
                // objective. Keep cutting - a conflict above the optimum
                // teaches nlsat the bound - but not for long: the objective
                // may really be unbounded.
                if (++unbounded_rounds > 4) {
                    IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: feasible set unbounded above)\n");
                    break;
                }
            }
            else
                unbounded_rounds = 0;
            nlsat::literal l = mk_lower_bound(s, t, best, true);
            if (l == nlsat::null_literal) {
                IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: root index not found)\n");
                st = l_undef;
                break;
            }
            s.mk_clause(1, &l);
            IF_VERBOSE(4, s.display(verbose_stream() << "(optsmt nlsat state after blocking)\n") << "\n");
        }
        if (!has_best)
            return st == l_false ? l_false : l_undef;

        if (st == l_true && !s.max_var_unbounded())
            prove_supremum(s, t, best, res);

        // 4. report the exact value and a rational bracket.
        set_result(am, best, st == l_false, res);
        return res.m_attained ? l_true : l_undef;
    }
}

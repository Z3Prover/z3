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

    lbool nlsat_opt::maximize(expr_ref_vector const& hard, expr* obj, rational const& lo, bool has_hi, rational const& hi,
                              unsigned max_rounds, result& res) {
        res.m_value = nullptr;
        res.m_model = nullptr;
        res.m_attained = false;
        res.m_rounds = 0;
        res.m_has_sup = false;
        if (!in_nra_fragment(m, m_arith, hard, obj)) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: outside the nonlinear real arithmetic fragment)\n");
            return l_undef;
        }

        // 1. hard /\ T = obj /\ lo <= T <= hi, normalized for goal2nlsat
        //    (purified arithmetic, no term-ite, CNF). T is a fresh constant
        //    that only occurs in these three assertions, so no preprocessing
        //    step can substitute it away except by eliminating the objective.
        app_ref T(m.mk_fresh_const("opt.nlsat.obj", m_arith.mk_real()), m);
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
        goal_ref pg = pre_result[0];
        if (pg->inconsistent())
            return l_false;
        bool has_T = false;
        for (unsigned i = 0; i < pg->size() && !has_T; ++i)
            has_T = occurs(T, pg->form(i));
        if (!has_T)
            return l_undef;
        model_converter_ref mc = pg->mc();

        // 2. nlsat with T as the first variable and maximization target.
        nlsat::solver s(m.limit(), m_params, true);
        expr2var a2b(m), t2x(m);
        nlsat::var t = s.mk_var(false);
        t2x.insert(T, t);
        goal2nlsat g2n;
        try {
            g2n(*pg, m_params, s, a2b, t2x);
        }
        catch (tactic_exception& ex) {
            IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: unsupported: " << ex.what() << ")\n");
            return l_undef;
        }
        s.set_max_var(t);
        algebraic_numbers::manager& am = s.am();
        polynomial::manager& pm = s.pm();
        expr_ref_vector x2t(m), b2a(m);
        t2x.mk_inv(x2t);
        a2b.mk_inv(b2a);

        scoped_anum best(am);
        bool has_best = false;
        lbool st = l_undef;
        // 3. F-Sat / F-Close loop: each model is blocked by t > value.
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
            // model of the preprocessed goal, mapped back through the model converter
            model_ref md = alloc(model, m);
            for (unsigned x = 0; x < x2t.size(); ++x) {
                expr* e = x2t.get(x);
                if (!e || !is_uninterp_const(e) || e == T.get())
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
            res.m_model = md;
            if (s.max_var_unbounded()) {
                // the feasible set of t was unbounded above when t was assigned:
                // the objective may be unbounded; stop with the improved model.
                IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: feasible set unbounded above)\n");
                break;
            }

            // block: t > best
            if (am.is_rational(best)) {
                rational q;
                am.to_rational(best, q);
                rational d = denominator(q), n = -numerator(q);   // d*t - n > 0  <=>  t > q
                polynomial_ref p(pm);
                p = pm.mk_linear(1, &d, &t, n);
                polynomial::polynomial* pp = p.get();
                bool is_even = false;
                nlsat::literal l = s.mk_ineq_literal(nlsat::atom::GT, 1, &pp, &is_even);
                s.mk_clause(1, &l);
            }
            else {
                svector<mpz> coeffs;
                am.get_polynomial(best, coeffs);
                polynomial_ref p(pm);
                p = pm.mk_univariate(t, coeffs.size() - 1, coeffs.data());   // consumes coeffs
                scoped_anum_vector roots(am);
                am.isolate_roots(p, roots);
                unsigned idx = 0;
                for (unsigned k = 0; k < roots.size(); ++k)
                    if (am.eq(roots[k], best)) { idx = k + 1; break; }
                if (idx == 0) {
                    IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat: root index not found)\n");
                    st = l_undef;
                    break;
                }
                nlsat::bool_var bv = s.mk_root_atom(nlsat::atom::ROOT_GT, t, idx, p.get());
                nlsat::literal l(bv, false);
                s.mk_clause(1, &l);
            }
            IF_VERBOSE(4, s.display(verbose_stream() << "(optsmt nlsat state after blocking)\n") << "\n");
        }
        if (!has_best)
            return st == l_false ? l_false : l_undef;

        if (st == l_true && !s.max_var_unbounded()) {
            // Round budget exhausted below an open supremum r of the feasible
            // set of t: check whether t >= r has a model. If not, r is a
            // proven upper bound (F-Close at the supremum).
            scoped_anum r(am);
            am.set(r, s.max_var_sup());
            if (am.gt(r, best)) {
                nlsat::literal l;
                if (am.is_rational(r)) {
                    rational q;
                    am.to_rational(r, q);
                    rational d = denominator(q), n = -numerator(q);   // !(d*t - n < 0)  <=>  t >= q
                    polynomial_ref p(pm);
                    p = pm.mk_linear(1, &d, &t, n);
                    polynomial::polynomial* pp = p.get();
                    bool is_even = false;
                    l = ~s.mk_ineq_literal(nlsat::atom::LT, 1, &pp, &is_even);
                }
                else {
                    svector<mpz> coeffs;
                    am.get_polynomial(r, coeffs);
                    polynomial_ref p(pm);
                    p = pm.mk_univariate(t, coeffs.size() - 1, coeffs.data());
                    scoped_anum_vector roots(am);
                    am.isolate_roots(p, roots);
                    unsigned idx = 0;
                    for (unsigned k = 0; k < roots.size(); ++k)
                        if (am.eq(roots[k], r)) { idx = k + 1; break; }
                    if (idx > 0)
                        l = nlsat::literal(s.mk_root_atom(nlsat::atom::ROOT_GE, t, idx, p.get()), false);
                }
                if (l != nlsat::null_literal) {
                    s.mk_clause(1, &l);
                    lbool st2 = s.check();
                    IF_VERBOSE(2, verbose_stream() << "(optsmt nlsat sup-check "; am.display_root_smt2(verbose_stream(), r); verbose_stream() << " " << st2 << ")\n");
                    if (st2 == l_false) {
                        res.m_has_sup = true;
                        if (am.is_rational(r))
                            am.to_rational(r, res.m_sup_upper);
                        else
                            am.get_upper(r, res.m_sup_upper, 40);
                    }
                }
            }
        }

        // 4. report the exact value and a rational bracket.
        res.m_value = m_arith.mk_numeral(am, best, false);
        if (am.is_rational(best)) {
            am.to_rational(best, res.m_lower);
            res.m_upper = res.m_lower;
        }
        else {
            am.get_lower(best, res.m_lower, 40);
            am.get_upper(best, res.m_upper, 40);
        }
        res.m_attained = (st == l_false);
        return res.m_attained ? l_true : l_undef;
    }
}

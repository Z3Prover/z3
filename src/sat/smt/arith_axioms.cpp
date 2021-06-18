/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_axioms.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"


namespace arith {

    // q = 0 or q * (p div q) = p
    void solver::mk_div_axiom(expr* p, expr* q) {
        if (a.is_zero(q)) return;
        literal eqz = eq_internalize(q, a.mk_real(0));
        literal eq = eq_internalize(a.mk_mul(q, a.mk_div(p, q)), p);
        add_clause(eqz, eq);
    }

    // to_int (to_real x) = x
    // to_real(to_int(x)) <= x < to_real(to_int(x)) + 1
    void solver::mk_to_int_axiom(app* n) {
        expr* x = nullptr, * y = nullptr;
        VERIFY(a.is_to_int(n, x));
        if (a.is_to_real(x, y)) {
            literal eq = eq_internalize(y, n);
            add_clause(eq);
        }
        else {
            expr_ref to_r(a.mk_to_real(n), m);
            expr_ref lo(a.mk_le(a.mk_sub(to_r, x), a.mk_real(0)), m);
            expr_ref hi(a.mk_ge(a.mk_sub(x, to_r), a.mk_real(1)), m);
            literal llo = mk_literal(lo);
            literal lhi = mk_literal(hi);
            add_clause(llo);
            add_clause(~lhi);
        }
    }

    // t = n^0
    void solver::mk_power0_axioms(app* t, app* n) {
        expr_ref p0(a.mk_power0(n, t->get_arg(1)), m);
        literal eq = eq_internalize(n, a.mk_numeral(rational(0), a.is_int(n)));
        add_clause(~eq, eq_internalize(t, p0));
        add_clause(eq, eq_internalize(t, a.mk_numeral(rational(1), a.is_int(t))));
    }

    // is_int(x) <=> to_real(to_int(x)) = x
    void solver::mk_is_int_axiom(expr* n) {
        expr* x = nullptr;
        VERIFY(a.is_is_int(n, x));
        expr_ref lhs(a.mk_to_real(a.mk_to_int(x)), m);
        literal eq = eq_internalize(lhs, x);
        literal is_int = ctx.expr2literal(n);
        add_equiv(is_int, eq);
    }

    void solver::mk_idiv_mod_axioms(expr* p, expr* q) {
        if (a.is_zero(q)) {
            return;
        }
        TRACE("arith", tout << expr_ref(p, m) << " " << expr_ref(q, m) << "\n";);
        // if q is zero, then idiv and mod are uninterpreted functions.
        expr_ref div(a.mk_idiv(p, q), m);
        expr_ref mod(a.mk_mod(p, q), m);
        expr_ref zero(a.mk_int(0), m);
        if (a.is_zero(p)) {
            // q != 0 => (= (div 0 q) 0)
            // q != 0 => (= (mod 0 q) 0)
            literal q_ge_0 = mk_literal(a.mk_ge(q, zero));
            literal q_le_0 = mk_literal(a.mk_le(q, zero));
            literal d_ge_0 = mk_literal(a.mk_ge(div, zero));
            literal d_le_0 = mk_literal(a.mk_le(div, zero));
            literal m_ge_0 = mk_literal(a.mk_ge(mod, zero));
            literal m_le_0 = mk_literal(a.mk_le(mod, zero));
            add_clause(q_ge_0, d_ge_0);
            add_clause(q_ge_0, d_le_0);
            add_clause(q_ge_0, m_ge_0);
            add_clause(q_ge_0, m_le_0);
            add_clause(q_le_0, d_ge_0);
            add_clause(q_le_0, d_le_0);
            add_clause(q_le_0, m_ge_0);
            add_clause(q_le_0, m_le_0);
            return;
        }
        literal eq = eq_internalize(a.mk_add(a.mk_mul(q, div), mod), p);
        literal mod_ge_0 = mk_literal(a.mk_ge(mod, zero));

        rational k(0);
        expr_ref upper(m);

        if (a.is_numeral(q, k)) {
            if (k.is_pos()) {
                upper = a.mk_numeral(k - 1, true);
            }
            else if (k.is_neg()) {
                upper = a.mk_numeral(-k - 1, true);
            }
        }
        else {
            k = rational::zero();
        }

        if (!k.is_zero()) {
            add_clause(eq);
            add_clause(mod_ge_0);
            add_clause(mk_literal(a.mk_le(mod, upper)));
        }
        else {

            /*literal div_ge_0   = */ mk_literal(a.mk_ge(div, zero));
            /*literal div_le_0   = */ mk_literal(a.mk_le(div, zero));
            /*literal p_ge_0     = */ mk_literal(a.mk_ge(p, zero));
            /*literal p_le_0     = */ mk_literal(a.mk_le(p, zero));

            // q >= 0 or p = (p mod q) + q * (p div q)
            // q <= 0 or p = (p mod q) + q * (p div q)
            // q >= 0 or (p mod q) >= 0
            // q <= 0 or (p mod q) >= 0
            // q <= 0 or (p mod q) <  q
            // q >= 0 or (p mod q) < -q
            literal q_ge_0 = mk_literal(a.mk_ge(q, zero));
            literal q_le_0 = mk_literal(a.mk_le(q, zero));

            add_clause(q_ge_0, eq);
            add_clause(q_le_0, eq);
            add_clause(q_ge_0, mod_ge_0);
            add_clause(q_le_0, mod_ge_0);
            add_clause(q_le_0, ~mk_literal(a.mk_ge(a.mk_sub(mod, q), zero)));
            add_clause(q_ge_0, ~mk_literal(a.mk_ge(a.mk_add(mod, q), zero)));

        }
        if (get_config().m_arith_enum_const_mod && k.is_pos() && k < rational(8)) {
            unsigned _k = k.get_unsigned();
            literal_vector lits;
            for (unsigned j = 0; j < _k; ++j) {
                literal mod_j = eq_internalize(mod, a.mk_int(j));
                lits.push_back(mod_j);
            }
            add_clause(lits);
        }
    }

    //  n < 0 || rem(a, n) =  mod(a, n)
    // !n < 0 || rem(a, n) = -mod(a, n)
    void solver::mk_rem_axiom(expr* dividend, expr* divisor) {
        expr_ref zero(a.mk_int(0), m);
        expr_ref rem(a.mk_rem(dividend, divisor), m);
        expr_ref mod(a.mk_mod(dividend, divisor), m);
        expr_ref mmod(a.mk_uminus(mod), m);
        expr_ref degz_expr(a.mk_ge(divisor, zero), m);
        literal dgez = mk_literal(degz_expr);
        literal pos = eq_internalize(rem, mod);
        literal neg = eq_internalize(rem, mmod);
        add_clause(~dgez, pos);
        add_clause(dgez, neg);
    }

    void solver::mk_bound_axioms(api_bound& b) {
        theory_var v = b.get_var();
        lp_api::bound_kind kind1 = b.get_bound_kind();
        rational const& k1 = b.get_value();
        lp_bounds& bounds = m_bounds[v];

        api_bound* end = nullptr;
        api_bound* lo_inf = end, * lo_sup = end;
        api_bound* hi_inf = end, * hi_sup = end;

        for (api_bound* other : bounds) {
            if (other == &b) continue;
            if (b.get_lit() == other->get_lit()) continue;
            lp_api::bound_kind kind2 = other->get_bound_kind();
            rational const& k2 = other->get_value();
            if (k1 == k2 && kind1 == kind2) {
                // the bounds are equivalent.
                continue;
            }

            SASSERT(k1 != k2 || kind1 != kind2);
            if (kind2 == lp_api::lower_t) {
                if (k2 < k1) {
                    if (lo_inf == end || k2 > lo_inf->get_value()) {
                        lo_inf = other;
                    }
                }
                else if (lo_sup == end || k2 < lo_sup->get_value()) {
                    lo_sup = other;
                }
            }
            else if (k2 < k1) {
                if (hi_inf == end || k2 > hi_inf->get_value()) {
                    hi_inf = other;
                }
            }
            else if (hi_sup == end || k2 < hi_sup->get_value()) {
                hi_sup = other;
            }
        }
        if (lo_inf != end) mk_bound_axiom(b, *lo_inf);
        if (lo_sup != end) mk_bound_axiom(b, *lo_sup);
        if (hi_inf != end) mk_bound_axiom(b, *hi_inf);
        if (hi_sup != end) mk_bound_axiom(b, *hi_sup);
    }

    void solver::mk_bound_axiom(api_bound& b1, api_bound& b2) {
        literal   l1(b1.get_lit());
        literal   l2(b2.get_lit());
        rational const& k1 = b1.get_value();
        rational const& k2 = b2.get_value();
        lp_api::bound_kind kind1 = b1.get_bound_kind();
        lp_api::bound_kind kind2 = b2.get_bound_kind();
        bool v_is_int = b1.is_int();
        SASSERT(b1.get_var() == b2.get_var());
        if (k1 == k2 && kind1 == kind2) return;
        SASSERT(k1 != k2 || kind1 != kind2);

        if (kind1 == lp_api::lower_t) {
            if (kind2 == lp_api::lower_t) {
                if (k2 <= k1)
                    add_clause(~l1, l2);
                else
                    add_clause(l1, ~l2);
            }
            else if (k1 <= k2)
                // k1 <= k2, k1 <= x or x <= k2
                add_clause(l1, l2);
            else {
                // k1 > hi_inf, k1 <= x => ~(x <= hi_inf)
                add_clause(~l1, ~l2);
                if (v_is_int && k1 == k2 + rational(1))
                    // k1 <= x or x <= k1-1
                    add_clause(l1, l2);
            }
        }
        else if (kind2 == lp_api::lower_t) {
            if (k1 >= k2)
                // k1 >= lo_inf, k1 >= x or lo_inf <= x
                add_clause(l1, l2);
            else {
                // k1 < k2, k2 <= x => ~(x <= k1)
                add_clause(~l1, ~l2);
                if (v_is_int && k1 == k2 - rational(1))
                    // x <= k1 or k1+l <= x
                    add_clause(l1, l2);
            }
        }
        else {
            // kind1 == A_UPPER, kind2 == A_UPPER
            if (k1 >= k2)
                // k1 >= k2, x <= k2 => x <= k1
                add_clause(l1, ~l2);
            else
                // k1 <= hi_sup , x <= k1 =>  x <= hi_sup
                add_clause(~l1, l2);
        }
    }

    api_bound* solver::mk_var_bound(sat::literal lit, theory_var v, lp_api::bound_kind bk, rational const& bound) {
        scoped_internalize_state st(*this);
        st.vars().push_back(v);
        st.coeffs().push_back(rational::one());
        init_left_side(st);
        lp::constraint_index cT, cF;
        bool v_is_int = is_int(v);
        auto vi = register_theory_var_in_lar_solver(v);

        lp::lconstraint_kind kT = bound2constraint_kind(v_is_int, bk, true);
        lp::lconstraint_kind kF = bound2constraint_kind(v_is_int, bk, false);

        cT = lp().mk_var_bound(vi, kT, bound);
        if (v_is_int) {
            rational boundF = (bk == lp_api::lower_t) ? bound - 1 : bound + 1;
            cF = lp().mk_var_bound(vi, kF, boundF);
        }
        else {
            cF = lp().mk_var_bound(vi, kF, bound);
        }
        add_ineq_constraint(cT, lit);
        add_ineq_constraint(cF, ~lit);

        return alloc(api_bound, lit, v, vi, v_is_int, bound, bk, cT, cF);
    }

    lp::lconstraint_kind solver::bound2constraint_kind(bool is_int, lp_api::bound_kind bk, bool is_true) {
        switch (bk) {
        case lp_api::lower_t:
            return is_true ? lp::GE : (is_int ? lp::LE : lp::LT);
        case lp_api::upper_t:
            return is_true ? lp::LE : (is_int ? lp::GE : lp::GT);
        }
        UNREACHABLE();
        return lp::EQ;
    }

    void solver::new_eq_eh(euf::th_eq const& e) {
        theory_var v1 = e.v1();
        theory_var v2 = e.v2();
        if (is_bool(v1))
            return;
        force_push();
        expr* e1 = var2expr(v1);
        expr* e2 = var2expr(v2);
        TRACE("arith", tout << "new eq: v" << v1 << " v" << v2 << "\n";);
        if (e1->get_id() > e2->get_id())
            std::swap(e1, e2);
            
        if (m.are_equal(e1, e2))
            return;

        ++m_stats.m_assert_eq;
        m_new_eq = true;
        euf::enode* n1 = var2enode(v1);
        euf::enode* n2 = var2enode(v2);
        lpvar w1 = register_theory_var_in_lar_solver(v1);
        lpvar w2 = register_theory_var_in_lar_solver(v2);
        auto cs = lp().add_equality(w1, w2);            
        add_eq_constraint(cs.first, n1, n2);
        add_eq_constraint(cs.second, n1, n2);
    }

    void solver::new_diseq_eh(euf::th_eq const& e) {
        ensure_column(e.v1());
        ensure_column(e.v2());
        m_delayed_eqs.push_back(std::make_pair(e, false));
        ctx.push(push_back_vector<svector<std::pair<euf::th_eq, bool>>>(m_delayed_eqs));
    }

    void solver::mk_diseq_axiom(euf::th_eq const& e) {
        if (is_bool(e.v1()))
            return;
        force_push();
        expr* e1 = var2expr(e.v1());
        expr* e2 = var2expr(e.v2());
        if (e1->get_id() > e2->get_id())
            std::swap(e1, e2);
        if (m.are_distinct(e1, e2))
            return;       
        literal le, ge;
        if (a.is_numeral(e1))
            std::swap(e1, e2);
        SASSERT(!a.is_numeral(e1));
        literal eq = eq_internalize(e1, e2);
        if (a.is_numeral(e2)) {
            le = mk_literal(a.mk_le(e1, e2));
            ge = mk_literal(a.mk_ge(e1, e2));
        }
        else {
            expr_ref diff(a.mk_sub(e1, e2), m);
            expr_ref zero(a.mk_numeral(rational(0), a.is_int(e1)), m);
            rewrite(diff);
            if (a.is_numeral(diff)) {
                if (!a.is_zero(diff))
                    return;
                if (a.is_zero(diff))
                    add_unit(eq);
                else 
                    add_unit(~eq);
                return;
            }
            le = mk_literal(a.mk_le(diff, zero));
            ge = mk_literal(a.mk_ge(diff, zero));
        }
        ++m_stats.m_assert_diseq;  
        add_clause(~eq, le);
        add_clause(~eq, ge);
        add_clause(~le, ~ge, eq);
    }


    // create axiom for 
    //    u = v + r*w,
    ///   abs(r) > r >= 0
    void solver::assert_idiv_mod_axioms(theory_var u, theory_var v, theory_var w, rational const& r) {
        app_ref term(m);
        term = a.mk_mul(a.mk_numeral(r, true), var2expr(w));
        term = a.mk_add(var2expr(v), term);
        term = a.mk_sub(var2expr(u), term);
        theory_var z = internalize_def(term);
        lpvar zi = register_theory_var_in_lar_solver(z);
        lpvar vi = register_theory_var_in_lar_solver(v);
        add_def_constraint_and_equality(zi, lp::GE, rational::zero());
        add_def_constraint_and_equality(zi, lp::LE, rational::zero());
        add_def_constraint_and_equality(vi, lp::GE, rational::zero());
        add_def_constraint_and_equality(vi, lp::LT, abs(r));
        SASSERT(!is_infeasible());
        TRACE("arith", tout << term << "\n" << lp().constraints(););
    }

    /**
      * n = (div p q)
      *
      * (div p q) * q + (mod p q) = p, (mod p q) >= 0   
      *
      * 0 < q => (p/q <= v(p)/v(q) => n <= floor(v(p)/v(q)))
      * 0 < q => (v(p)/v(q) <= p/q => v(p)/v(q) - 1 < n)
      *
      */

    bool solver::check_idiv_bounds() {
        if (m_idiv_terms.empty()) {
            return true;
        }
        bool all_divs_valid = true;
        for (unsigned i = 0; i < m_idiv_terms.size(); ++i) {
            expr* n = m_idiv_terms[i];
            expr* p = nullptr, * q = nullptr;
            VERIFY(a.is_idiv(n, p, q));
            theory_var v1 = internalize_def(p);
            lp::impq r1 = get_ivalue(v1);
            rational r2;

            if (!r1.x.is_int() || r1.x.is_neg() || !r1.y.is_zero()) {
                // TBD
                // r1 = 223/4, r2 = 2, r = 219/8 
                // take ceil(r1), floor(r1), ceil(r2), floor(r2), for floor(r2) > 0
                // then 
                //      p/q <= ceil(r1)/floor(r2) => n <= div(ceil(r1), floor(r2))
                //      p/q >= floor(r1)/ceil(r2) => n >= div(floor(r1), ceil(r2))
                continue;
            }

            if (a.is_numeral(q, r2) && r2.is_pos()) {
                if (!a.is_bounded(n)) {
                    TRACE("arith", tout << "unbounded " << expr_ref(n, m) << "\n";);
                    continue;
                }
                theory_var v = internalize_def(n);
                lp::impq val_v = get_ivalue(v);
                if (val_v.y.is_zero() && val_v.x == div(r1.x, r2)) continue;

                TRACE("arith", tout << get_value(v) << " != " << r1 << " div " << r2 << "\n";);
                rational div_r = div(r1.x, r2);
                // p <= q * div(r1, q) + q - 1 => div(p, q) <= div(r1, r2)
                // p >= q * div(r1, q) => div(r1, q) <= div(p, q)
                rational mul(1);
                rational hi = r2 * div_r + r2 - 1;
                rational lo = r2 * div_r;

                // used to normalize inequalities so they 
                // don't appear as 8*x >= 15, but x >= 2
                expr* n1 = nullptr, * n2 = nullptr;
                if (a.is_mul(p, n1, n2) && a.is_extended_numeral(n1, mul) && mul.is_pos()) {
                    p = n2;
                    hi = floor(hi / mul);
                    lo = ceil(lo / mul);
                }
                literal p_le_r1 = mk_literal(a.mk_le(p, a.mk_numeral(hi, true)));
                literal p_ge_r1 = mk_literal(a.mk_ge(p, a.mk_numeral(lo, true)));
                literal n_le_div = mk_literal(a.mk_le(n, a.mk_numeral(div_r, true)));
                literal n_ge_div = mk_literal(a.mk_ge(n, a.mk_numeral(div_r, true)));

                add_clause(~p_le_r1, n_le_div);
                add_clause(~p_ge_r1, n_ge_div);

                all_divs_valid = false;

                TRACE("arith", tout << r1 << " div " << r2 << "\n";);
                continue;
            }
        }

        return all_divs_valid;
    }

    void solver::fixed_var_eh(theory_var v, lp::constraint_index ci1, lp::constraint_index ci2, rational const& bound) {
        theory_var w = euf::null_theory_var;
        enode* x = var2enode(v);
        if (bound.is_zero()) 
            w = lp().local_to_external(get_zero(a.is_int(x->get_expr())));
        else if (bound.is_one())
            w = lp().local_to_external(get_one(a.is_int(x->get_expr())));
        else if (!m_value2var.find(bound, w))
            return;
        enode* y = var2enode(w);
        if (x->get_sort() != y->get_sort())
            return;
        if (x->get_root() == y->get_root())
            return;
        reset_evidence();
        set_evidence(ci1, m_core, m_eqs);
        set_evidence(ci2, m_core, m_eqs);
        ++m_stats.m_fixed_eqs;
        auto* jst = euf::th_explain::propagate(*this, m_core, m_eqs, x, y);
        ctx.propagate(x, y, jst->to_index());
    }


}

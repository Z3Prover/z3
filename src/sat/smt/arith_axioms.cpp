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
        literal eq  = eq_internalize(a.mk_mul(q, a.mk_div(p, q)), p);
        add_clause(eqz, eq);
    }

    // to_int (to_real x) = x
    // to_real(to_int(x)) <= x < to_real(to_int(x)) + 1
    void solver::mk_to_int_axiom(app* n) {
        expr* x = nullptr, *y = nullptr;
        VERIFY (a.is_to_int(n, x));            
        if (a.is_to_real(x, y)) {
            literal eq = eq_internalize(y, n);
            add_clause(eq);
        }
        else {
            expr_ref to_r(a.mk_to_real(n), m);
            expr_ref lo(a.mk_le(a.mk_sub(to_r, x), a.mk_real(0)), m);
            expr_ref hi(a.mk_ge(a.mk_sub(x, to_r), a.mk_real(1)), m);
            literal llo = b_internalize(lo);
            literal lhi = b_internalize(hi);
            add_clause(llo);
            add_clause(~lhi);
        }
    }

    // is_int(x) <=> to_real(to_int(x)) = x
    void solver::mk_is_int_axiom(app* n) {
        expr* x = nullptr;
        VERIFY(a.is_is_int(n, x));
        expr_ref lhs(a.mk_to_real(a.mk_to_int(x)), m);
        literal eq = eq_internalize(lhs, x);
        literal is_int = ctx.expr2literal(n);
        add_equiv(is_int, eq);
    }


#if 0


    void mk_ite_axiom(expr* n) {
        return;
        expr* c = nullptr, *t = nullptr, *e = nullptr;
        VERIFY(m.is_ite(n, c, t, e));
        literal e1 = th.mk_eq(n, t, false);
        literal e2 = th.mk_eq(n, e, false);
        scoped_trace_stream sts(th, e1, e2);
        mk_axiom(e1, e2);
    }


    // create axiom for 
    //    u = v + r*w,
    ///   abs(r) > r >= 0
    void assert_idiv_mod_axioms(theory_var u, theory_var v, theory_var w, rational const& r) {
        app_ref term(m);
        term = a.mk_mul(a.mk_numeral(r, true), get_enode(w)->get_owner());
        term = a.mk_add(get_enode(v)->get_owner(), term);
        term = a.mk_sub(get_enode(u)->get_owner(), term);
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

    void mk_idiv_mod_axioms(expr * p, expr * q) {
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
            mk_axiom(q_ge_0, d_ge_0);
            mk_axiom(q_ge_0, d_le_0);
            mk_axiom(q_ge_0, m_ge_0);
            mk_axiom(q_ge_0, m_le_0);
            mk_axiom(q_le_0, d_ge_0);
            mk_axiom(q_le_0, d_le_0);
            mk_axiom(q_le_0, m_ge_0);
            mk_axiom(q_le_0, m_le_0);
            return;
        }
#if 0
        expr_ref eqr(m.mk_eq(a.mk_add(a.mk_mul(q, div), mod), p), m);
        ctx().get_rewriter()(eqr);
        literal eq = mk_literal(eqr);
#else
        literal eq         = th.mk_eq(a.mk_add(a.mk_mul(q, div), mod), p, false);
#endif
        literal mod_ge_0   = mk_literal(a.mk_ge(mod, zero));

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

        context& c = ctx();
        if (!k.is_zero()) {
            mk_axiom(eq);
            mk_axiom(mod_ge_0);
            mk_axiom(mk_literal(a.mk_le(mod, upper)));
            {
                std::function<void(void)> log = [&,this]() {
                    th.log_axiom_unit(m.mk_implies(m.mk_not(m.mk_eq(q, zero)), c.bool_var2expr(eq.var())));
                    th.log_axiom_unit(m.mk_implies(m.mk_not(m.mk_eq(q, zero)), c.bool_var2expr(mod_ge_0.var())));
                    th.log_axiom_unit(m.mk_implies(m.mk_not(m.mk_eq(q, zero)), a.mk_le(mod, upper)));
                };
                if_trace_stream _ts(m, log);
            }
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

            mk_axiom(q_ge_0, eq);
            mk_axiom(q_le_0, eq);
            mk_axiom(q_ge_0, mod_ge_0);
            mk_axiom(q_le_0, mod_ge_0);
            mk_axiom(q_le_0, ~mk_literal(a.mk_ge(a.mk_sub(mod, q), zero)));            
            mk_axiom(q_ge_0, ~mk_literal(a.mk_ge(a.mk_add(mod, q), zero)));        

        }
        if (params().m_arith_enum_const_mod && k.is_pos() && k < rational(8)) {
            unsigned _k = k.get_unsigned();
            literal_buffer lits;
            expr_ref_vector exprs(m);
            for (unsigned j = 0; j < _k; ++j) {
                literal mod_j = th.mk_eq(mod, a.mk_int(j), false);
                lits.push_back(mod_j);
                exprs.push_back(c.bool_var2expr(mod_j.var()));
                ctx().mark_as_relevant(mod_j);
            }
            ctx().mk_th_axiom(get_id(), lits.size(), lits.begin());                
        }            
    }
#endif

}

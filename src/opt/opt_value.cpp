/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_value.cpp

Abstract:

    Exact finite parts and the legacy rational view of optimization bounds.

--*/

#include "opt/opt_value.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/polynomial/algebraic_numbers.h"

namespace opt {

    void objective_value::set_exact(inf_eps const& bound, expr* finite) {
        SASSERT(bound.is_finite());
        SASSERT(finite);
        SASSERT(arith_util(m_exact.m()).is_numeral(finite) ||
                arith_util(m_exact.m()).is_irrational_algebraic_numeral(finite));
        m_exact = finite;
        update_rational_bound(bound);
    }

    void objective_value::update_rational_bound(inf_eps const& bound) {
        // Lex model refreshes may change an isolating endpoint, but not the
        // exact finite value already established for an earlier objective.
        SASSERT(!m_exact || bound.is_finite());
        DEBUG_CODE(
            rational q;
            if (m_exact && arith_util(m_exact.m()).is_numeral(m_exact, q))
                SASSERT(q == bound.get_rational());
        );
        m_bound = bound;
    }

    objective_value objective_value::adjusted(rational const& offset, bool negate) const {
        objective_value result(*this);
        if (negate)
            result.m_bound.neg();
        result.m_bound += offset;
        if (result.m_exact) {
            arith_util a(m_exact.m());
            if (negate)
                result.m_exact = a.mk_uminus(result.m_exact);
            if (!offset.is_zero())
                result.m_exact = a.mk_add(result.m_exact, a.mk_numeral(offset, false));
            th_rewriter rw(m_exact.m());
            rw(result.m_exact);
        }
        return result;
    }

    bool objective_value::operator==(objective_value const& other) const {
        SASSERT(&m_exact.m() == &other.m_exact.m());
        if (m_bound.get_infinity() != other.m_bound.get_infinity() ||
            m_bound.get_infinitesimal() != other.m_bound.get_infinitesimal())
            return false;
        if (!m_exact && !other.m_exact)
            return m_bound.get_rational() == other.m_bound.get_rational();
        arith_util a(m_exact.m());
        bool algebraic = m_exact && a.is_irrational_algebraic_numeral(m_exact);
        bool other_algebraic = other.m_exact && a.is_irrational_algebraic_numeral(other.m_exact);
        if (algebraic != other_algebraic)
            return false;
        if (algebraic)
            return a.am().eq(a.to_irrational_algebraic_numeral(m_exact),
                             a.to_irrational_algebraic_numeral(other.m_exact));
        return m_bound.get_rational() == other.m_bound.get_rational();
    }

    void objective_value::to_exprs(expr_ref_vector& es) const {
        arith_util a(m_exact.m());
        rational const& inf = m_bound.get_infinity();
        rational const& r = m_bound.get_rational();
        rational const& eps = m_bound.get_infinitesimal();
        es.push_back(a.mk_numeral(inf, inf.is_int()));
        // Preserve the API's numeral sorts: integral rationals are Int,
        // fractions and irrational algebraic values are Real.
        es.push_back(m_exact && a.is_irrational_algebraic_numeral(m_exact) ?
                     m_exact.get() : a.mk_numeral(r, r.is_int()));
        es.push_back(a.mk_numeral(eps, eps.is_int()));
    }

    expr_ref objective_value::to_expr() const {
        ast_manager& m = m_exact.m();
        arith_util a(m);
        rational const& inf = m_bound.get_infinity();
        rational const& r = m_bound.get_rational();
        rational const& eps = m_bound.get_infinitesimal();
        expr_ref_vector args(m);
        bool algebraic = m_exact && a.is_irrational_algebraic_numeral(m_exact);
        bool is_int = !algebraic && eps.is_zero() && r.is_int();
        if (!inf.is_zero()) {
            expr* oo = m.mk_const(symbol("oo"), is_int ? a.mk_int() : a.mk_real());
            if (inf.is_one())
                args.push_back(oo);
            else
                args.push_back(a.mk_mul(a.mk_numeral(inf, is_int), oo));
        }
        if (algebraic)
            args.push_back(m_exact);
        else if (!r.is_zero())
            args.push_back(a.mk_numeral(r, is_int));
        if (!eps.is_zero()) {
            expr* ep = m.mk_const(symbol("epsilon"), a.mk_real());
            if (eps.is_one())
                args.push_back(ep);
            else
                args.push_back(a.mk_mul(a.mk_numeral(eps, is_int), ep));
        }
        switch (args.size()) {
        case 0: return expr_ref(a.mk_numeral(rational(0), true), m);
        case 1: return expr_ref(args[0].get(), m);
        default: return expr_ref(a.mk_add(args.size(), args.data()), m);
        }
    }
}

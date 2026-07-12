/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    bv_divrem_bounds.cpp

Abstract:

    Simplifier that adds range/bound lemmas for bit-vector division and
    remainder terms with a non-constant divisor. See bv_divrem_bounds.h.

Author:

    Nikolaj Bjorner (nbjorner)

--*/
#include "ast/simplifiers/bv_divrem_bounds.h"
#include "ast/for_each_expr.h"

namespace bv {

    bool divrem_bounds::is_target(expr* t) const {
        return m_util.is_bv_urem(t)  || m_util.is_bv_uremi(t) ||
               m_util.is_bv_srem(t)  || m_util.is_bv_sremi(t) ||
               m_util.is_bv_smod(t)  || m_util.is_bv_smodi(t) ||
               m_util.is_bv_udiv(t)  || m_util.is_bv_udivi(t) ||
               m_util.is_bv_sdiv(t)  || m_util.is_bv_sdivi(t);
    }

    // build the range lemma for a div/rem term, or nullptr if none applies
    expr* divrem_bounds::mk_lemma(expr* t) {
        expr* a = to_app(t)->get_arg(0);
        expr* b = to_app(t)->get_arg(1);
        if (m_util.is_numeral(b))
            return nullptr;
        expr* zero = m_util.mk_zero(b->get_sort());
        expr* b_nz = m.mk_not(m.mk_eq(b, zero));
        expr* bound = nullptr;
        if (m_util.is_bv_urem(t) || m_util.is_bv_uremi(t))
            bound = m_util.mk_ult(t, b);
        else if (m_util.is_bv_srem(t) || m_util.is_bv_sremi(t) ||
                 m_util.is_bv_smod(t) || m_util.is_bv_smodi(t))
            bound = m_util.mk_ult(m_util.mk_abs(t), m_util.mk_abs(b));
        else if (m_util.is_bv_udiv(t) || m_util.is_bv_udivi(t))
            bound = m_util.mk_ule(t, a);
        else if (m_util.is_bv_sdiv(t) || m_util.is_bv_sdivi(t))
            bound = m_util.mk_ule(m_util.mk_abs(t), m_util.mk_abs(a));
        if (!bound)
            return nullptr;
        return m.mk_implies(b_nz, bound);
    }

    void divrem_bounds::reduce() {
        expr_ref_vector targets(m), fmls(m);
        for (unsigned i : indices())
            fmls.push_back(m_fmls[i].fml());
        for (expr* e : subterms::ground(fmls))
            if (is_target(e))
                targets.push_back(e);
        for (expr* t : targets) {
            expr_ref lemma(mk_lemma(t), m);
            if (!lemma)
                continue;
            // the lemma is a bit-vector theory axiom (valid with no premises)
            proof_ref pr(m);
            if (m.proofs_enabled())
                pr = m.mk_th_lemma(m_util.get_fid(), lemma, 0, nullptr);
            m_fmls.add(dependent_expr(m, lemma, pr, nullptr));
            ++m_num_lemmas;
        }
    }
}

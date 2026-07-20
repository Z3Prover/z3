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

    void divrem_bounds::reduce() {
        expr_ref_vector targets(m), fmls(m), clause(m);
        for (unsigned i : indices())
            fmls.push_back(m_fmls[i].fml());
        for (expr* e : subterms::ground(fmls))
            if (m_util.is_bv_divrem(e))
                targets.push_back(e);
        for (expr* t : targets) {
            m_util.mk_bv_divrem_bound(t, clause);
            if (clause.empty())
                continue;
            expr_ref lemma(m.mk_or(clause), m);
            // the lemma is a bit-vector theory axiom (valid with no premises)
            proof_ref pr(m);
            if (m.proofs_enabled())
                pr = m.mk_th_lemma(m_util.get_fid(), lemma, 0, nullptr);
            m_fmls.add(dependent_expr(m, lemma, pr, nullptr));
            ++m_num_lemmas;
        }
    }
}

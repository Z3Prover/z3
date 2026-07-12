/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    bv_divrem_bounds.h

Abstract:

    Simplifier that adds range/bound lemmas for bit-vector division and
    remainder terms with a non-constant divisor.

    Bit-blasting a division circuit with a symbolic divisor hides the algebraic
    fact that the remainder magnitude is bounded by the divisor magnitude. For a
    divisor b that is not a numeral the following facts hold and are added as
    (implied) lemmas so that a downstream bit-blasting + SAT solver can reason
    about the magnitudes without unfolding the division circuit:

        b != 0 => bvult (bvurem a b) b                 (unsigned remainder)
        b != 0 => bvult |bvsrem a b| |b|               (signed remainder)
        b != 0 => bvult |bvsmod a b| |b|               (signed modulo)
        b != 0 => bvule (bvudiv a b) a                 (unsigned quotient)
        b != 0 => bvule |bvsdiv a b| |a|               (signed quotient)

    where |x| = ite(x <s 0, -x, x). These lemmas are logically implied by the
    semantics of the operators for a non-zero divisor, so the transformation
    preserves satisfiability and all models. The unsigned comparison on the
    absolute values keeps the bounds sound at INT_MIN: -INT_MIN overflows to
    INT_MIN whose unsigned value is the maximum magnitude, so the bound only
    ever loosens, never becomes unsound.

Author:

    Nikolaj Bjorner (nbjorner)

--*/
#pragma once

#include "ast/bv_decl_plugin.h"
#include "ast/simplifiers/dependent_expr_state.h"

namespace bv {

    class divrem_bounds : public dependent_expr_simplifier {
        bv_util  m_util;
        unsigned m_num_lemmas = 0;

        expr* mk_lemma(expr* t);
        bool  is_target(expr* t) const;

    public:
        divrem_bounds(ast_manager& m, dependent_expr_state& fmls) :
            dependent_expr_simplifier(m, fmls), m_util(m) {}

        char const* name() const override { return "bv-divrem-bounds"; }

        void reduce() override;

        bool supports_proofs() const override { return true; }

        void collect_statistics(statistics& st) const override {
            st.update("bv-divrem-bounds", m_num_lemmas);
        }

        void reset_statistics() override { m_num_lemmas = 0; }
    };
}

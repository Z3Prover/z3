/*++
Copyright (c) 2026

Module Name:

    bv_mul_bounds.h

Abstract:

    Guarded order lemmas for unsigned multiplication with a common factor.

--*/
#pragma once

#include "ast/bv_decl_plugin.h"
#include "ast/simplifiers/dependent_expr_state.h"

namespace bv {

    class mul_bounds : public dependent_expr_simplifier {
        bv_util m_util;
        unsigned m_num_lemmas = 0;

    public:
        mul_bounds(ast_manager& m, dependent_expr_state& fmls) :
            dependent_expr_simplifier(m, fmls), m_util(m) {}

        char const* name() const override { return "bv-mul-bounds"; }

        void reduce() override;

        bool supports_proofs() const override { return true; }

        void collect_statistics(statistics& st) const override {
            st.update("bv-mul-bounds", m_num_lemmas);
        }

        void reset_statistics() override { m_num_lemmas = 0; }
    };
}

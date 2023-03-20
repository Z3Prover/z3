/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    seq_simplifier.h

Abstract:

    Global simplifier for sequences

Author:

    Nikolaj Bjorner (nbjorner) 2023-03-12.

--*/


#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/elim_unconstrained.h"


class seq_simplifier : public dependent_expr_simplifier {
    seq_util m_seq;

    void eliminate(elim_unconstrained& elim);
    bool invert(elim_unconstrained& elim, app* t, expr_ref& r);
public:

    seq_simplifier(ast_manager& m, dependent_expr_state& fmls) : dependent_expr_simplifier(m, fmls), m_seq(m) {}
    char const* name() const override { return "seq-simplifier"; }
    void reduce() override;
};

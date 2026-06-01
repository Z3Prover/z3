/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    expand_records.h

Abstract:

    Expand free constants of single-constructor algebraic datatype sort
    (a.k.a. records) into applications of that constructor over fresh
    variables.  For a free constant v : T where T has the single
    constructor c(f1:T1, ..., fn:Tn), introduce fresh constants
    v!f1 : T1, ..., v!fn : Tn and substitute v -> (c v!f1 ... v!fn).

    After the substitution, every accessor application (fi v) collapses
    via standard datatype simplification to v!fi.  This enables solve-eqs
    and arithmetic preprocessing to operate on the field variables
    directly, which in turn enables more aggressive constant folding.

Author:

    Lev Nachmanson 2026-05

--*/
#pragma once

#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/simplifiers/dependent_expr_state.h"


class expand_records_simplifier : public dependent_expr_simplifier {
    datatype_util  m_dt;
    th_rewriter    m_rewriter;
    bool           m_enabled = true;

    bool is_expandable(sort* s) {
        if (!m_dt.is_datatype(s))
            return false;
        if (m_dt.is_recursive(s))
            return false;
        auto const* ctors = m_dt.get_datatype_constructors(s);
        return ctors && ctors->size() == 1;
    }

public:
    expand_records_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls), m_dt(m), m_rewriter(m, p) {}

    char const* name() const override { return "expand-records"; }

    void reduce() override;

    void updt_params(params_ref const& p) override {
        m_rewriter.updt_params(p);
        m_enabled = p.get_bool("expand_records", true);
    }
};

/*
  ADD_SIMPLIFIER("expand-records", "expand single-constructor datatype constants.", "alloc(expand_records_simplifier, m, p, s)")
*/

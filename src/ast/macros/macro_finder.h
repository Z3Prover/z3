/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    macro_finder.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-05.

Revision History:

--*/
#pragma once

#include "ast/macros/macro_manager.h"


/**
   \brief Macro finder is responsible for finding universally quantified sub-formulas that can be used
   as macros.
*/
class macro_finder {
    ast_manager &               m;
    macro_manager &             m_macro_manager;
    macro_util &                m_util;
    arith_util                  m_autil;
    bool expand_macros(expr_ref_vector const& exprs, proof_ref_vector const& prs, expr_dependency_ref_vector const & deps, 
                       expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector& new_deps);
    bool expand_macros(unsigned n, justified_expr const * fmls, vector<justified_expr>& new_fmls);
    bool is_arith_macro(expr * n, proof * pr, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);
    bool is_arith_macro(expr * n, proof * pr, vector<justified_expr>& new_fmls);
    bool is_arith_macro(expr * n, proof * pr, bool deps_valid, expr_dependency * dep, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps);

    bool is_macro(expr * n, app_ref & head, expr_ref & def);

public:
    macro_finder(ast_manager & m, macro_manager & mm);
    ~macro_finder();
    void operator()(expr_ref_vector const& exprs, proof_ref_vector const& prs, expr_dependency_ref_vector const& deps, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps);
    void operator()(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls);
};



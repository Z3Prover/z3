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
#ifndef MACRO_FINDER_H_
#define MACRO_FINDER_H_

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
    bool expand_macros(unsigned num, expr * const * exprs, proof * const * prs, expr_dependency * const* deps, 
                       expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector& new_deps);
    bool expand_macros(unsigned n, justified_expr const * fmls, vector<justified_expr>& new_fmls);
    bool is_arith_macro(expr * n, proof * pr, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);
    bool is_arith_macro(expr * n, proof * pr, vector<justified_expr>& new_fmls);
    bool is_arith_macro(expr * n, proof * pr, expr_dependency * dep, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps);

    bool is_macro(expr * n, app_ref & head, expr_ref & def);

public:
    macro_finder(ast_manager & m, macro_manager & mm);
    ~macro_finder();
    void operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_dependency * const* deps, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps);
    void operator()(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls);
};

#endif /* MACRO_FINDER_H_ */


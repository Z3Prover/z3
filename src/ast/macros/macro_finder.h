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

#include"macro_manager.h"
#include"arith_simplifier_plugin.h"


bool is_macro_head(expr * n, unsigned num_decls);
bool is_simple_macro(ast_manager & m, expr * n, unsigned num_decls, obj_hashtable<func_decl> const * forbidden_set, app * & head, expr * & def);
inline bool is_simple_macro(ast_manager & m, expr * n, unsigned num_decls, app * & head, expr * & def) {
    return is_simple_macro(m, n, num_decls, 0, head, def);
}

/**
   \brief Macro finder is responsible for finding universally quantified sub-formulas that can be used
   as macros.
*/
class macro_finder {
    ast_manager &               m_manager; 
    macro_manager &             m_macro_manager;
    macro_util &                m_util;
    arith_simplifier_plugin * get_arith_simp() { return m_util.get_arith_simp(); }
    bool expand_macros(unsigned num, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);
    bool is_arith_macro(expr * n, proof * pr, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);

    bool is_macro(expr * n, app_ref & head, expr_ref & def);
    bool is_pseudo_head(expr * n, unsigned num_decls, app * & head, app * & t);
    bool is_pseudo_predicate_macro(expr * n, app * & head, app * & t, expr * & def);

public:
    macro_finder(ast_manager & m, macro_manager & mm);
    ~macro_finder();
    void operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);
};

#endif /* MACRO_FINDER_H_ */


/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    quasi_macros.cpp

Abstract:

    <abstract>

Author:

    Christoph Wintersteiger (t-cwinte) 2010-04-23

Revision History:

--*/
#ifndef QUASI_MACROS_H_
#define QUASI_MACROS_H_

#include<sstream>
#include "ast/justified_expr.h"
#include "ast/macros/macro_manager.h"
#include "ast/rewriter/th_rewriter.h"

/**
   \brief Finds quasi macros and applies them.
*/
class quasi_macros {
    typedef obj_map<func_decl, unsigned> occurrences_map;

    ast_manager &             m_manager;
    macro_manager &           m_macro_manager;
    th_rewriter               m_rewriter;
    occurrences_map           m_occurrences;
    ptr_vector<expr>          m_todo;

    vector<symbol>            m_new_var_names;
    expr_ref_vector           m_new_vars;
    expr_ref_vector           m_new_eqs;
    sort_ref_vector           m_new_qsorts;
    std::stringstream         m_new_name;
    expr_mark                 m_visited_once;
    expr_mark                 m_visited_more;

    bool is_unique(func_decl * f) const;
    bool is_non_ground_uninterp(expr const * e) const;
    bool fully_depends_on(app * a, quantifier * q) const;
    bool depends_on(expr * e, func_decl * f) const;

    bool is_quasi_macro(expr * e, app_ref & a, expr_ref &v) const;
    void quasi_macro_to_macro(quantifier * q, app * a, expr * t, quantifier_ref & macro);

    void find_occurrences(expr * e);
    bool find_macros(unsigned n, expr * const * exprs);
    bool find_macros(unsigned n, justified_expr const* expr);
    void apply_macros(unsigned n, expr * const * exprs, proof * const * prs, expr_dependency * const* deps,
                      expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector& new_deps);
    void apply_macros(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls);

public:
    quasi_macros(ast_manager & m, macro_manager & mm);
    ~quasi_macros();

    /**
       \brief Find pure function macros and apply them.
    */
    // bool operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);    
    bool operator()(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls);
    bool operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_dependency * const * deps, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps);

};

#endif

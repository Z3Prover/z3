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
#ifndef _QUASI_MACROS_H_
#define _QUASI_MACROS_H_

#include<sstream>
#include"macro_manager.h"
#include"basic_simplifier_plugin.h"
#include"simplifier.h"

/**
   \brief Finds quasi macros and applies them.
*/
class quasi_macros {
    typedef obj_map<func_decl, unsigned> occurrences_map;

    ast_manager &             m_manager;
    macro_manager &           m_macro_manager;
    simplifier &              m_simplifier;
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
    void apply_macros(unsigned n, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);

public:
    quasi_macros(ast_manager & m, macro_manager & mm, simplifier & s);
    ~quasi_macros();
    
    /**
       \brief Find pure function macros and apply them.
    */
    bool operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_ref_vector & new_exprs, proof_ref_vector & new_prs);    
};

#endif

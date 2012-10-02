/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    preprocessor.h

Abstract:

    Preprocess AST before adding them to the logical context

Author:

    Leonardo de Moura (leonardo) 2008-01-17.

Revision History:

--*/
#ifndef _PREPROCESSOR_H_
#define _PREPROCESSOR_H_

#include"preprocessor_params.h"
#include"simplifier.h"
#include"pattern_inference.h"
#include"nnf.h"
#include"cnf.h"
#include"der.h"
#include"push_app_ite.h"

/**
   \brief Functor used to preprocess expressions before adding them to
   the logical context.
*/
class preprocessor {
    preprocessor_params & m_params;
    ast_manager &         m_manager;
    simplifier &          m_simp;
    nnf                   m_nnf;
    cnf                   m_cnf;
    der_star              m_der;                  
    push_app_ite          m_push_app_ite;
    expr_ref_vector       m_cnf_todo;
    proof_ref_vector      m_cnf_todo_prs;
    expr_ref_vector       m_push_todo;
    proof_ref_vector      m_push_todo_prs;
public:
    preprocessor(ast_manager & m, defined_names & d, simplifier & s, preprocessor_params & p);
    void operator()(expr * e, proof * in_pr, expr_ref_vector & result, proof_ref_vector & result_prs);
};

#endif /* _PREPROCESSOR_H_ */

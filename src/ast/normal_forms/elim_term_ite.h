/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    elim_term_ite.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-12.

Revision History:

--*/
#ifndef _ELIM_TERM_ITE_H_
#define _ELIM_TERM_ITE_H_

#include"simplifier.h"
#include"defined_names.h"

class elim_term_ite : public simplifier {
    defined_names &    m_defined_names;
    proof_ref_vector   m_coarse_proofs;
    expr_ref_vector *  m_new_defs;
    proof_ref_vector * m_new_def_proofs;
    void reduce_core(expr * n);
    bool visit_children(expr * n);
    void reduce1(expr * n);
    void reduce1_app(app * n);
    void reduce1_quantifier(quantifier * q);
public:
    elim_term_ite(ast_manager & m, defined_names & d):simplifier(m), m_defined_names(d), m_coarse_proofs(m) { 
        m_use_oeq = true; 
        enable_ac_support(false);
    }
    virtual ~elim_term_ite() {}
    void operator()(expr * n,                          // [IN]
                    expr_ref_vector & new_defs,        // [OUT] new definitions
                    proof_ref_vector & new_def_proofs, // [OUT] proofs of the new definitions 
                    expr_ref & r,                      // [OUT] resultant expression
                    proof_ref & pr                     // [OUT] proof for (~ n r)
                    );
};

#endif /* _ELIM_TERM_ITE_H_ */


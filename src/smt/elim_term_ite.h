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
#ifndef ELIM_TERM_ITE_H_
#define ELIM_TERM_ITE_H_

#include "ast/normal_forms/defined_names.h"
#include "ast/rewriter/rewriter.h"
#include "ast/simplifier/simplifier.h"

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


class elim_term_ite_cfg : public default_rewriter_cfg {
    ast_manager&           m;
    defined_names &        m_defined_names;
    vector<justified_expr> m_new_defs;
public:
    elim_term_ite_cfg(ast_manager & m, defined_names & d): m(m), m_defined_names(d) { 
        // TBD enable_ac_support(false);
    }
    virtual ~elim_term_ite_cfg() {}
    vector<justified_expr> const& new_defs() const { return m_new_defs; }
    void reset() { m_new_defs.reset(); }
    br_status reduce_app(func_decl* f, unsigned n, expr *const* args, expr_ref& result, proof_ref& result_pr);
};

class elim_term_ite_rw : public rewriter_tpl<elim_term_ite_cfg> {
    elim_term_ite_cfg m_cfg;
public:
    elim_term_ite_rw(ast_manager& m, defined_names & dn):
        rewriter_tpl<elim_term_ite_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, dn) 
    {}
    vector<justified_expr> const& new_defs() const { return m_cfg.new_defs(); }
    void reset() { m_cfg.reset(); }
};



#endif /* ELIM_TERM_ITE_H_ */


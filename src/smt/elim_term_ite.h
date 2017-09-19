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
#include "ast/justified_expr.h"

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


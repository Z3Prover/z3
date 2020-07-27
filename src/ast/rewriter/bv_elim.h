/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    bv_elim.h

Abstract:

    Eliminate bit-vectors variables from clauses, by
    replacing them by bound Boolean variables.

Author:

    Nikolaj Bjorner (nbjorner) 2008-12-16.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"

class bv_elim_cfg : public default_rewriter_cfg {
    ast_manager& m;
public:
    bv_elim_cfg(ast_manager& m) : m(m) {}

    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr);
};

class bv_elim_rw : public rewriter_tpl<bv_elim_cfg> {
protected:
    bv_elim_cfg  m_cfg;
public:
    bv_elim_rw(ast_manager & m):
        rewriter_tpl<bv_elim_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m)
    {} 
};



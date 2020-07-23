/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    push_app_ite.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-05-14.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"

/**
   \brief Functor for applying the following transformation:

   (f s (ite c t1 t2)) ==> (ite c (f s t1) (f s t2))
*/

struct push_app_ite_cfg : public default_rewriter_cfg {
    ast_manager& m;
    bool m_conservative;
    virtual bool is_target(func_decl * decl, unsigned num_args, expr * const * args);
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr);
    push_app_ite_cfg(ast_manager& m): m(m), m_conservative(true) {}
    void set_conservative(bool c) { m_conservative = c; }
    bool rewrite_patterns() const { return false; }
};

/**
   \brief Variation of push_app_ite that applies the transformation on nonground terms only.

   \remark This functor uses the app::is_ground method. This method is not
   completely precise, for instance, any term containing a quantifier is marked as non ground.
*/
class ng_push_app_ite_cfg : public push_app_ite_cfg {
protected:
    bool is_target(func_decl * decl, unsigned num_args, expr * const * args) override;
public:
    ng_push_app_ite_cfg(ast_manager& m): push_app_ite_cfg(m) {}
    virtual ~ng_push_app_ite_cfg() {}
};

struct push_app_ite_rw : public rewriter_tpl<push_app_ite_cfg> {
    push_app_ite_cfg m_cfg;
public:
    push_app_ite_rw(ast_manager& m):
        rewriter_tpl<push_app_ite_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m)
    {}
    void set_conservative(bool c) { m_cfg.set_conservative(c); }
};

struct ng_push_app_ite_rw : public rewriter_tpl<ng_push_app_ite_cfg> {
    ng_push_app_ite_cfg m_cfg;
public:
    ng_push_app_ite_rw(ast_manager& m):
        rewriter_tpl<ng_push_app_ite_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m)
    {}
    void set_conservative(bool c) { m_cfg.set_conservative(c); }
};




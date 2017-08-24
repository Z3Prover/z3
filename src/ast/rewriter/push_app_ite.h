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
#ifndef PUSH_APP_ITE_H_
#define PUSH_APP_ITE_H_

#include "ast/ast.h"
#include "ast/simplifier/simplifier.h"
#include "ast/rewriter/rewriter.h"

/**
   \brief Functor for applying the following transformation:

   (f s (ite c t1 t2)) ==> (ite c (f s t1) (f s t2))
*/
class push_app_ite : public simplifier {
protected:
    bool          m_conservative;
    void apply(func_decl * decl, unsigned num_args, expr * const * args, expr_ref & result);
    virtual bool is_target(func_decl * decl, unsigned num_args, expr * const * args);
    void reduce_core(expr * n);
    bool visit_children(expr * n);
    void reduce1(expr * n);
    void reduce1_app(app * n);
    void reduce1_quantifier(quantifier * q);

public:
    push_app_ite(simplifier & s, bool conservative = true);
    virtual ~push_app_ite();
    void operator()(expr * s, expr_ref & r, proof_ref & p);
};

/**
   \brief Variation of push_app_ite that applies the transformation on nonground terms only.

   \remark This functor uses the app::is_ground method. This method is not
   completly precise, for instance, any term containing a quantifier is marked as non ground.
*/
class ng_push_app_ite : public push_app_ite {
protected:
    virtual bool is_target(func_decl * decl, unsigned num_args, expr * const * args);
public:
    ng_push_app_ite(simplifier & s, bool conservative = true);
    virtual ~ng_push_app_ite() {}
};

struct push_app_ite_cfg : public default_rewriter_cfg {
    ast_manager& m;
    bool m_conservative;
    virtual bool is_target(func_decl * decl, unsigned num_args, expr * const * args);
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr);
    push_app_ite_cfg(ast_manager& m, bool conservative = true): m(m), m_conservative(conservative) {}
};

/**
   \brief Variation of push_app_ite that applies the transformation on nonground terms only.

   \remark This functor uses the app::is_ground method. This method is not
   completly precise, for instance, any term containing a quantifier is marked as non ground.
*/
class ng_push_app_ite_cfg : public push_app_ite_cfg {
protected:
    virtual bool is_target(func_decl * decl, unsigned num_args, expr * const * args);
public:
    ng_push_app_ite_cfg(ast_manager& m, bool conservative = true): push_app_ite_cfg(m, conservative) {}
    virtual ~ng_push_app_ite_cfg() {}
};

struct push_app_ite_rw : public rewriter_tpl<push_app_ite_cfg> {
    push_app_ite_cfg m_cfg;
public:
    push_app_ite_rw(ast_manager& m, bool conservative = true):
        rewriter_tpl<push_app_ite_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, conservative)
    {}
};

struct ng_push_app_ite_rw : public rewriter_tpl<ng_push_app_ite_cfg> {
    ng_push_app_ite_cfg m_cfg;
public:
    ng_push_app_ite_rw(ast_manager& m, bool conservative = true):
        rewriter_tpl<ng_push_app_ite_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, conservative)
    {}
};


#endif /* PUSH_APP_ITE_H_ */


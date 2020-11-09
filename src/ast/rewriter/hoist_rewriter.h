/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    hoist_rewriter.h

Abstract:

    Hoist predicates over disjunctions

Author:

    Nikolaj Bjorner (nbjorner) 2019-2-4

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "util/params.h"
#include "util/union_find.h"
#include "util/obj_hashtable.h"

class hoist_rewriter {
    ast_manager &  m_manager;
    expr_ref_vector                 m_args1, m_args2;
    obj_hashtable<expr>             m_preds1, m_preds2;
    basic_union_find                m_uf1, m_uf2, m_uf0;
    ptr_vector<expr>                m_es;
    svector<std::pair<expr*,expr*>> m_eqs;
    u_map<expr*>                    m_roots;
    expr_safe_replace               m_subst;
    obj_map<expr, unsigned> m_expr2var;
    ptr_vector<expr>        m_var2expr;
    expr_mark               m_mark;

    br_status mk_or(unsigned num_args, expr * const * args, expr_ref & result);

    bool is_and(expr* e, expr_ref_vector* args);

    bool is_var(expr* e) { return m_expr2var.contains(e); }
    expr* mk_expr(unsigned v) { return m_var2expr[v]; }
    unsigned mk_var(expr* e);

    void reset(basic_union_find& uf);

    expr_ref hoist_predicates(obj_hashtable<expr> const& p, unsigned num_args, expr* const* args);

public:
    hoist_rewriter(ast_manager & m, params_ref const & p = params_ref());
    ast_manager& m() const { return m_manager; }
    family_id get_fid() const { return m().get_basic_family_id(); }
    bool is_eq(expr * t) const { return m().is_eq(t); }       
    void updt_params(params_ref const & p) {}
    static void get_param_descrs(param_descrs & r) {}
    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);    
};

struct hoist_rewriter_cfg : public default_rewriter_cfg {
    hoist_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        if (f->get_family_id() != m_r.get_fid())
            return BR_FAILED;
        return m_r.mk_app_core(f, num, args, result);
    }
    hoist_rewriter_cfg(ast_manager & m, params_ref const & p):m_r(m, p) {}
};

class hoist_rewriter_star : public rewriter_tpl<hoist_rewriter_cfg> {
    hoist_rewriter_cfg m_cfg;
public:
    hoist_rewriter_star(ast_manager & m, params_ref const & p = params_ref()):
        rewriter_tpl<hoist_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m, p) {}
};


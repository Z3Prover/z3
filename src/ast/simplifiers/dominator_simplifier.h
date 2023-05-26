/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    dom_simplifier.h

--*/

#pragma once
#include "ast/ast.h"
#include "ast/expr_substitution.h"
#include "ast/rewriter/dom_simplifier.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "util/obj_pair_hashtable.h"

class dominator_simplifier : public dependent_expr_simplifier {

    ast_manager&         m;
    dom_simplifier*      m_simplifier;
    params_ref           m_params;
    expr_ref_vector      m_trail, m_args;
    obj_map<expr, expr*> m_result;
    expr_dominators      m_dominators;
    unsigned             m_depth;
    unsigned             m_max_depth;
    ptr_vector<expr>     m_empty;
    obj_pair_map<expr, expr, bool> m_subexpr_cache;
    bool                 m_forward;

    expr_ref simplify_rec(expr* t);
    expr_ref simplify_arg(expr* t);
    expr_ref simplify_ite(app * ite);
    expr_ref simplify_and(app * e) { return simplify_and_or(true, e); }
    expr_ref simplify_or(app * e) { return simplify_and_or(false, e); }
    expr_ref simplify_and_or(bool is_and, app * e);
    expr_ref simplify_not(app * e);

    bool init();

    bool is_subexpr(expr * a, expr * b);

    expr_ref get_cached(expr* t) { expr* r = nullptr; if (!m_result.find(t, r)) r = t; return expr_ref(r, m); }
    void cache(expr *t, expr* r) { m_result.insert(t, r); m_trail.push_back(r); m_trail.push_back(t); }
    void reset_cache() { m_result.reset(); }

    ptr_vector<expr> const & tree(expr * e);
    expr* idom(expr *e) const { return m_dominators.idom(e); }

    unsigned scope_level() { return m_simplifier->scope_level(); }
    void local_pop(unsigned n) { SASSERT(n <= m_simplifier->scope_level()); m_simplifier->pop(n); }
    bool assert_expr(expr* f, bool sign) { return m_simplifier->assert_expr(f, sign); }


public:
    dominator_simplifier(ast_manager & m, dependent_expr_state& st, dom_simplifier* s, params_ref const & p = params_ref()):
        dependent_expr_simplifier(m, st),
        m(m), m_simplifier(s), m_params(p), 
        m_trail(m), m_args(m), 
        m_dominators(m), m_depth(0), m_max_depth(1024), m_forward(true) {}

    ~dominator_simplifier() override;

    char const* name() const override { return "dom-simplify"; }

    void reduce() override;

    void updt_params(params_ref const & p) override { m_simplifier->updt_params(p); }
    void collect_param_descrs(param_descrs & r) override { m_simplifier->collect_param_descrs(r); }   
};


/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    factor_rewriter.h

Abstract:

    Rewriting utilities for factoring polynomials in equations,
    and inequalities.

Author:

    Nikolaj (nbjorner) 2011-19-05

Notes:

--*/
#ifndef FACTOR_REWRITER_H_
#define FACTOR_REWRITER_H_

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/arith_decl_plugin.h"

class factor_rewriter {
    typedef obj_map<expr,unsigned> powers_t;
    ast_manager &                  m_manager;
    arith_util                     m_arith;
    powers_t                       m_powers;
    vector<std::pair<expr*,bool> > m_adds;
    vector<ptr_vector<expr> >      m_muls;
    expr_ref_vector                m_factors;

public:
    factor_rewriter(ast_manager & m);
    ast_manager & m() const { return m_manager; }
    arith_util & a() { return m_arith; }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

private:
    br_status mk_eq(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_le(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ge(expr * a1, expr * a2, expr_ref & r) { return mk_le(a2,a1,r); }
    br_status mk_gt(expr * a1, expr * a2, expr_ref & r) { return mk_lt(a2,a1,r); }

    void mk_adds(expr* arg1, expr* arg2);
    void mk_muls();
    void mk_expand_muls(ptr_vector<expr>& muls);
    void collect_powers();
    bool extract_factors();
    bool even(unsigned n) const { return 0 == (n & 0x1); }
    void mk_is_negative(expr_ref& result, expr_ref_vector& eqs);
};

struct factor_rewriter_cfg : public default_rewriter_cfg {
    factor_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        return m_r.mk_app_core(f, num, args, result);
    }
    factor_rewriter_cfg(ast_manager & m):m_r(m) {}
};

class factor_rewriter_star : public rewriter_tpl<factor_rewriter_cfg> {
    factor_rewriter_cfg m_cfg;
public:
    factor_rewriter_star(ast_manager & m):
        rewriter_tpl<factor_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m) {}
};

#endif

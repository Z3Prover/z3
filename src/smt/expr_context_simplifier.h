/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    expr_context_simplifier.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2008-06-03

Revision History:

--*/
#ifndef EXPR_CONTEXT_SIMPLIFIER_H_
#define EXPR_CONTEXT_SIMPLIFIER_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "smt/params/smt_params.h"
#include "smt/smt_kernel.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/bool_rewriter.h"

class expr_context_simplifier {
    typedef obj_map<expr, bool> context_map;

    ast_manager& m_manager;
    arith_util   m_arith;
    context_map  m_context;
    expr_ref_vector m_trail;
    bool_rewriter m_simp;
    expr_mark m_mark;
    bool m_forward;
public:
    expr_context_simplifier(ast_manager & m);
    void reduce_fix(expr * m, expr_ref & result);
    void operator()(expr * m, expr_ref & result) { reduce(m, result); }
    void insert_context(expr* e, bool polarity);
private:
    void reduce(expr * m, expr_ref & result);
    void reduce_rec(expr * m, expr_ref & result);
    void reduce_rec(quantifier* q, expr_ref & result);
    void reduce_rec(app * a, expr_ref & result);
    void clean_trail(unsigned old_lim);
    bool insert_arg(bool is_and, expr* arg, expr_ref_vector& args);
    void reduce_and_or(bool is_and, unsigned num_args, expr * const* args, expr_ref & result);
    void reduce_and(unsigned num_args, expr * const* args, expr_ref & result);
    void reduce_or(unsigned num_args, expr * const* args, expr_ref & result);
    bool is_true(expr* e) const;
    bool is_false(expr* e) const;
};

class expr_strong_context_simplifier {
    ast_manager& m_manager;
    arith_util    m_arith;
    func_decl_ref m_fn;
    smt::kernel   m_solver;
    
    void simplify(expr* e, expr_ref& result) { simplify_model_based(e, result); }
    void simplify_basic(expr* fml, expr_ref& result);
    void simplify_model_based(expr* fml, expr_ref& result);

    bool is_forced(expr* e, expr* v);

public:
    expr_strong_context_simplifier(smt_params& p, ast_manager& m);
    void operator()(expr* e, expr_ref& result) { simplify(e, result); }
    void operator()(expr_ref& result) { simplify(result.get(), result); }
    void push() { m_solver.push(); }
    void pop() { m_solver.pop(1); }
    void assert_expr(expr* e) { m_solver.assert_expr(e); }
    
    void collect_statistics(statistics & st) const { m_solver.collect_statistics(st); }
    void reset_statistics() { m_solver.reset_statistics(); }
};

#endif /* EXPR_CONTEXT_SIMPLIFIER_H_ */


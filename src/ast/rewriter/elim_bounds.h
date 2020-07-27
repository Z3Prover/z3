/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    elim_bounds2.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-28.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/rewriter.h"

/**
   \brief Functor for eliminating irrelevant bounds in quantified formulas.
   
   Example:
   (forall (x Int) (y Int) (or (not (>= y x) (not (>= x 0)) (= (select a x) 1))))

   The bound (>= y x) is irrelevant and can be eliminated.

   This can be easily proved by using Fourier-Motzkin elimination.

   Limitations & Assumptions:
   - It assumes the input formula was already simplified.
   - It can only handle bounds in the diff-logic fragment.

   \remark This operation is subsumed by Fourier-Motzkin elimination.
*/
class elim_bounds_cfg : public default_rewriter_cfg {
    ast_manager &      m;
    arith_util         m_util;
    bool is_bound(expr * n, var * & lower, var * & upper);
    bool is_bound(expr * n);
public:
    elim_bounds_cfg(ast_manager & m);
    
    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr);
};

/**
   \brief Functor for applying elim_bounds2 in all
   universal quantifiers in an expression.

   Assumption: the formula was already skolemized.
*/
class elim_bounds_rw : public rewriter_tpl<elim_bounds_cfg> {
protected:
    elim_bounds_cfg  m_cfg;
public:
    elim_bounds_rw(ast_manager & m):
        rewriter_tpl<elim_bounds_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m)
    {} 

    ~elim_bounds_rw() override {}
};



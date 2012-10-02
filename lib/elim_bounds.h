/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    elim_bounds.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-28.

Revision History:

--*/
#ifndef _ELIM_BOUNDS_H_
#define _ELIM_BOUNDS_H_

#include"ast.h"
#include"arith_decl_plugin.h"
#include"simplifier.h"

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
class elim_bounds {
    ast_manager &      m_manager;
    arith_util         m_util;
    bool is_bound(expr * n, var * & lower, var * & upper);
    bool is_bound(expr * n);
public:
    elim_bounds(ast_manager & m);
    void operator()(quantifier * q, expr_ref & r);
};

/**
   \brief Functor for applying elim_bounds in all
   universal quantifiers in an expression.

   Assumption: the formula was already skolemized.
*/
class elim_bounds_star : public simplifier {
protected:
    elim_bounds  m_elim;
    virtual bool visit_quantifier(quantifier * q);
    virtual void reduce1_quantifier(quantifier * q);
public:
    elim_bounds_star(ast_manager & m):simplifier(m), m_elim(m) { enable_ac_support(false); }
    virtual ~elim_bounds_star() {}
};

#endif /* _ELIM_BOUNDS_H_ */


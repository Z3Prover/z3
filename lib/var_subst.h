/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    var_subst.h

Abstract:

    Variable substitution.

Author:

    Leonardo (leonardo) 2008-01-10

Notes:

--*/
#ifndef _VAR_SUBST_H_
#define _VAR_SUBST_H_

#include"rewriter.h"

/**
   \brief Alias for var_shifter class.
*/
typedef var_shifter shift_vars;

/**
   \brief Variable substitution functor. It substitutes variables by expressions.
   The expressions may contain variables.
*/
class var_subst { 
    beta_reducer   m_reducer;
    bool           m_std_order;
public:
    var_subst(ast_manager & m, bool std_order = true):m_reducer(m), m_std_order(std_order) {}
    bool std_order() const { return m_std_order; }

    /**
       When std_order() == true, 
       I'm using the same standard used in quantifier instantiation.
       (VAR 0) is stored in the last position of the array.
       ...
       (VAR (num_args - 1)) is stored in the first position of the array.

       Otherwise, (VAR 0) is stored in the first position, (VAR 1) in the second, and so on.
    */
    void operator()(expr * n, unsigned num_args, expr * const * args, expr_ref & result);
    void reset() { m_reducer.reset(); }
};

/**
   \brief Eliminate the unused variables from \c q. Store the result in \c r.
*/
void elim_unused_vars(ast_manager & m, quantifier * q, expr_ref & r);

/**
   \brief Instantiate quantifier q using the given exprs.
   The vector exprs should contain at least q->get_num_decls() expressions.

   I'm using the same standard used in quantifier instantiation.
   (VAR 0) is stored in the last position of the array.
   ...
   (VAR (q->get_num_decls() - 1)) is stored in the first position of the array.
*/
void instantiate(ast_manager & m, quantifier * q, expr * const * exprs, expr_ref & result);

/**
   \brief Enumerate set of free variables in expression.

   Return the sorts of the free variables.
*/
void get_free_vars(expr* e, ptr_vector<sort>& sorts);

#endif



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
#pragma once

#include "ast/rewriter/rewriter.h"
#include "ast/used_vars.h"
#include "util/params.h"

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
    expr_ref operator()(expr * n, unsigned num_args, expr * const * args);
    inline expr_ref operator()(expr * n, expr_ref_vector const& args) { return (*this)(n, args.size(), args.data()); }
    inline expr_ref operator()(expr * n, var_ref_vector const& args) { return (*this)(n, args.size(), (expr*const*)args.data()); }
    inline expr_ref operator()(expr * n, app_ref_vector const& args) { return (*this)(n, args.size(), (expr*const*)args.data()); }
    inline expr_ref operator()(expr * n, ptr_vector<expr> const& args) { return (*this)(n, args.size(), args.data()); }
    void reset() { m_reducer.reset(); }
};

/**
   \brief Eliminate the unused variables from \c q. Store the result in \c r.
*/
class unused_vars_eliminator {
    ast_manager & m;
    var_subst     m_subst;
    used_vars     m_used;
    params_ref    m_params;
    bool          m_ignore_patterns_on_ground_qbody;
public:
    unused_vars_eliminator(ast_manager & m, params_ref const & params);
    expr_ref operator()(quantifier* q);
};

expr_ref elim_unused_vars(ast_manager & m, quantifier * q, params_ref const & params);

/**
   \brief Instantiate quantifier q using the given exprs.
   The vector exprs should contain at least q->get_num_decls() expressions.

   I'm using the same standard used in quantifier instantiation.
   (VAR 0) is stored in the last position of the array.
   ...
   (VAR (q->get_num_decls() - 1)) is stored in the first position of the array.
*/
expr_ref instantiate(ast_manager & m, quantifier * q, expr * const * exprs);

/**
   \brief Enumerate set of free variables in expression.

   Return the sorts of the free variables.
*/

class expr_free_vars {
    expr_sparse_mark m_mark;
    ptr_vector<sort> m_sorts;
    ptr_vector<expr> m_todo;
public:
    expr_free_vars() {}
    expr_free_vars(expr* e) { (*this)(e); }
    void reset();
    void operator()(expr* e);
    void accumulate(expr* e);
    bool empty() const { return m_sorts.empty(); }
    unsigned size() const { return m_sorts.size(); }
    sort* operator[](unsigned idx) const { return m_sorts[idx]; }
    bool contains(unsigned idx) const { return idx < m_sorts.size() && m_sorts[idx] != 0; }
    void set_default_sort(sort* s);
    void reverse() { m_sorts.reverse(); }
    sort*const* data() const { return m_sorts.data(); }
};




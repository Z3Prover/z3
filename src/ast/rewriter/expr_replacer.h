/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr_replacer.h

Abstract:

    Abstract (functor) for replacing expressions.

Author:

    Leonardo (leonardo) 2011-04-29

Notes:

--*/
#ifndef EXPR_REPLACER_H_
#define EXPR_REPLACER_H_

#include "ast/ast.h"
#include "ast/expr_substitution.h"
#include "util/params.h"

/**
   \brief Abstract interface for functors that replace constants with expressions.
*/
class expr_replacer {
    struct scoped_set_subst;
public:
    virtual ~expr_replacer() {}

    virtual ast_manager & m() const = 0;
    virtual void set_substitution(expr_substitution * s) = 0;

    virtual void operator()(expr * t, expr_ref & result, proof_ref & result_pr, expr_dependency_ref & deps) = 0;
    virtual void operator()(expr * t, expr_ref & result, proof_ref & result_pr);
    virtual void operator()(expr * t, expr_ref & result);
    virtual void operator()(expr_ref & t) { expr_ref s(t, m()); (*this)(s, t); }

    virtual unsigned get_num_steps() const { return 0; }
    virtual void reset() = 0;
    
    void apply_substitution(expr * s, expr * def, proof * def_pr, expr_ref & t);
    void apply_substitution(expr * s, expr * def, expr_ref & t);
};

/**
   \brief Create a vanilla replacer. It just applies the substitution.
*/
expr_replacer * mk_default_expr_replacer(ast_manager & m);

/**
   \brief Apply substitution and simplify.
*/
expr_replacer * mk_expr_simp_replacer(ast_manager & m, params_ref const & p = params_ref());

#endif

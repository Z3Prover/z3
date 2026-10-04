/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    distribute_forall.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-02.

Revision History:

    Christoph Wintersteiger 2010-04-06: Added implementation

--*/
#pragma once

#include "ast/ast.h"
#include "ast/act_cache.h"
#include "ast/array_decl_plugin.h"

/**
   \brief Apply the following transformation
   (forall X (and F1 ... Fn))
   -->
   (and (forall X F1) ... (forall X Fn))

   Quantifiers with patterns or no-patterns are left intact because their
   annotations need not apply to each conjunct.

   In restricted mode (see set_restricted) a quantifier is only split when
   the split is known to help:
     - every conjunct is an equality with a select over a ground array on at
       least one side, i.e. a conjunction of pointwise array equalities such as
       (forall ((i I)) (and (= (select a i) (select b i)) (= (select c i) d))),
       where splitting avoids MBQI loops that generate one counterexample per
       conjunct in turn (quantifiers ranging over the arrays themselves are
       left alone); or
     - some conjunct omits at least one of the bound variables, so the split
       produces a quantifier over strictly fewer variables, or a ground
       formula, for that conjunct (e.g. (forall ((p Bool) (x Real)) (and
       (not p) (<= x 8)))), and no conjunct applies an uninterpreted function
       (including Skolem functions of nested existentials) to the bound
       variables, since those occurrences drive E-matching and nested
       quantifier reasoning and must stay in one quantifier.
   Splitting arbitrary conjunctions, on the other hand, changes the shape of
   quantified formulas in ways that break E-matching based proofs and nested
   quantifier (qsat) solving, so unrestricted mode is opt-in.

   The actual transformation is slightly different since the "and" connective is eliminated and
   replaced with a "not or".
   So, the actual transformation is:

   (forall X (not (or F1 ... Fn)))
   -->
   (not (or (not (forall X (not F1)))
            ...
            (not (forall X (not Fn)))))


   The implementation uses the visit_children/reduce1 idiom. A cache is used as usual.   
*/
class distribute_forall {
    typedef act_cache expr_map;
    ast_manager &             m_manager;
    array_util                m_autil;
    ptr_vector<expr>          m_todo;
    expr_map                  m_cache;
    ptr_vector<expr>          m_new_args;
    bool                      m_restricted = false;
    // The new expressions are stored in a mapping that increments their reference counter. So, we do not need to store them in
    // m_new_exprs
    // expr_ref_vector  m_new_exprs;


public:
    distribute_forall(ast_manager & m);

    /**
       \brief Apply the distribute_forall transformation (when possible) to all universal quantifiers in \c f.
       Store the result in \c result.
    */
    void operator()(expr * f, expr_ref & result);

    /**
       \brief When set, only distribute over conjunctions of array select equalities
       or conjunctions where some conjunct omits a bound variable.
    */
    void set_restricted(bool f) { m_restricted = f; }

    /**
       \brief Drop all cached results and the references they hold.
    */
    void release_cache() { flush_cache(); }

protected:
    inline void visit(expr * n, bool & visited);
    bool is_array_select_eq(expr * conjunct) const;
    bool omits_bound_var(expr * conjunct, unsigned num_decls) const;
    bool has_uninterp_over_bound_vars(expr * conjunct) const;
    bool should_distribute(quantifier * q, app * or_e) const;
    bool visit_children(expr * n);
    void reduce1(expr * n);
    void reduce1_quantifier(quantifier * q);
    void reduce1_app(app * a);

    expr * get_cached(expr * n) const;
    bool is_cached(expr * n) const {  return get_cached(n) != nullptr; }
    void cache_result(expr * n, expr * r);
    void reset_cache() { m_cache.reset(); }
    void flush_cache() { m_cache.cleanup(); }
};

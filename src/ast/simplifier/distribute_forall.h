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
#ifndef DISTRIBUTE_FORALL_H_
#define DISTRIBUTE_FORALL_H_

#include"ast.h"
#include"basic_simplifier_plugin.h"
#include"act_cache.h"

/**
   \brief Apply the following transformation
   (forall X (and F1 ... Fn))
   -->
   (and (forall X F1) ... (forall X Fn))

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
    basic_simplifier_plugin & m_bsimp; // useful for constructing formulas and/or/not in simplified form.
    ptr_vector<expr>          m_todo;
    expr_map                  m_cache;
    ptr_vector<expr>          m_new_args;
    // The new expressions are stored in a mapping that increments their reference counter. So, we do not need to store them in
    // m_new_exprs
    // expr_ref_vector  m_new_exprs;


public:
    distribute_forall(ast_manager & m, basic_simplifier_plugin & p);

    /**
       \brief Apply the distribute_forall transformation (when possible) to all universal quantifiers in \c f.
       Store the result in \c result.
    */
    void operator()(expr * f, expr_ref & result);

protected:
    inline void visit(expr * n, bool & visited);
    bool visit_children(expr * n);
    void reduce1(expr * n);
    void reduce1_quantifier(quantifier * q);
    void reduce1_app(app * a);

    expr * get_cached(expr * n) const;
    bool is_cached(expr * n) const {  return get_cached(n) != 0; }
    void cache_result(expr * n, expr * r);
    void reset_cache() { m_cache.reset(); }
    void flush_cache() { m_cache.cleanup(); }
};

#endif /* DISTRIBUTE_FORALL_H_ */

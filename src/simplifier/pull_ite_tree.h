/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pull_ite_tree.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-22.

Revision History:

--*/
#ifndef _PULL_ITE_TREE_H_
#define _PULL_ITE_TREE_H_

#include"ast.h"
#include"simplifier.h"
#include"recurse_expr.h"
#include"obj_hashtable.h"
#include"expr_map.h"

/**
   \brief Functor for applying the following transformation
   F[(p (ite c t1 t2) args)] = F'[(ite c t1 t2), p, args]

   F'[(ite c t1 t2), p, args] = (ite c F'[t1, p, args] F'[t2, p, args])
   F'[t, p, args] = (p t args)
*/
class pull_ite_tree {
    ast_manager &         m_manager;
    simplifier &          m_simplifier;
    func_decl *           m_p;
    ptr_vector<expr>      m_args;
    unsigned              m_arg_idx; //!< position of the ite argument
    expr_map              m_cache;
    ptr_vector<expr>      m_todo;

    bool is_cached(expr * n) const { return m_cache.contains(n); }
    void get_cached(expr * n, expr * & r, proof * & p) const { m_cache.get(n, r, p); }
    void cache_result(expr * n, expr * r, proof * pr);
    void visit(expr * n, bool & visited);
    bool visit_children(expr * n);
    void reduce(expr * n);
    /**
       \brief Creante an application (m_p ... n ...) where n is the argument m_arg_idx and the other arguments
       are in m_args.
    */
    expr * mk_p_arg(expr * n) {
        m_args[m_arg_idx] = n;
        return m_manager.mk_app(m_p, m_args.size(), m_args.c_ptr());
    }
public:
    pull_ite_tree(ast_manager & m, simplifier & s);
    /**
       \brief Apply the transformation above if n contains an ite-expression.
       Store the result in r. If n does not contain an ite-expression, then
       store n in r.

       When proof generation is enabled, pr is a proof for n = r.
    */
    void operator()(app * n, app_ref & r, proof_ref & pr);
};

/**
   \brief Functor for applying the pull_ite_tree on subexpressions n that
   satisfy the is_target virtual predicate.
*/
class pull_ite_tree_star : public simplifier {
protected:
    pull_ite_tree m_proc;
    virtual bool get_subst(expr * n, expr_ref & r, proof_ref & p);
public:
    pull_ite_tree_star(ast_manager & m, simplifier & s);
    virtual ~pull_ite_tree_star() { release_plugins(); }
    virtual bool is_target(app * n) const = 0;
};

/**
   \brief Apply pull_ite_tree on predicates of the form
   (p ite v) and (p v ite)

   where:
   - p is an interpreted predicate
   - ite is an ite-term expression
   - v is a value
*/
class pull_cheap_ite_tree_star : public pull_ite_tree_star {
public:
    pull_cheap_ite_tree_star(ast_manager & m, simplifier & s):pull_ite_tree_star(m, s) {}
    virtual ~pull_cheap_ite_tree_star() {}
    virtual bool is_target(app * n) const;
};

#endif /* _PULL_ITE_TREE_H_ */


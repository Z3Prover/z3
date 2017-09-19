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
#ifndef PULL_ITE_TREE_H_
#define PULL_ITE_TREE_H_

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_map.h"
#include "ast/recurse_expr.h"
#include "util/obj_hashtable.h"

/**
   \brief Functor for applying the following transformation
   F[(p (ite c t1 t2) args)] = F'[(ite c t1 t2), p, args]

   F'[(ite c t1 t2), p, args] = (ite c F'[t1, p, args] F'[t2, p, args])
   F'[t, p, args] = (p t args)
*/
class pull_ite_tree {
    ast_manager &         m_manager;
    th_rewriter           m_rewriter;
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
    pull_ite_tree(ast_manager & m);
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
class pull_ite_tree_cfg : public default_rewriter_cfg {
protected:
    ast_manager& m;
    expr_ref_vector m_trail;
    pull_ite_tree m_proc;
public:
    pull_ite_tree_cfg(ast_manager & m);
    virtual ~pull_ite_tree_cfg() {}
    virtual bool is_target(app * n) const = 0;
    bool get_subst(expr * n, expr* & r, proof* & p);
};

/**
   \brief Apply pull_ite_tree on predicates of the form
   (p ite v) and (p v ite)

   where:
   - p is an interpreted predicate
   - ite is an ite-term expression
   - v is a value
*/
class pull_cheap_ite_tree_cfg : public pull_ite_tree_cfg {
public:
    pull_cheap_ite_tree_cfg(ast_manager & m):pull_ite_tree_cfg(m) {}
    virtual ~pull_cheap_ite_tree_cfg() {}
    virtual bool is_target(app * n) const;
};

class pull_cheap_ite_tree_rw  : public rewriter_tpl<pull_cheap_ite_tree_cfg> {
    pull_cheap_ite_tree_cfg m_cfg;
public:
    pull_cheap_ite_tree_rw(ast_manager& m):
        rewriter_tpl<pull_cheap_ite_tree_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m)
    {}
};

#endif /* PULL_ITE_TREE_H_ */


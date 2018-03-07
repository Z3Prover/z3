/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    macro_manager.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-05.

Revision History:

--*/
#ifndef MACRO_MANAGER_H_
#define MACRO_MANAGER_H_

#include "util/obj_hashtable.h"
#include "ast/ast_util.h"
#include "ast/justified_expr.h"
#include "ast/recurse_expr.h"
#include "ast/func_decl_dependencies.h"
#include "ast/macros/macro_util.h"

/**
   \brief Macros are universally quantified formulas of the form:
     (forall X  (= (f X) T[X]))
     (forall X  (iff (f X) T[X]))
   where T[X] does not contain X.

   This class is responsible for storing macros and expanding them.
   It has support for backtracking and tagging declarations in an expression as forbidded for being macros.
*/
class macro_manager {
    ast_manager &                    m;
    macro_util                       m_util;

    obj_map<func_decl, quantifier *> m_decl2macro;    // func-decl -> quantifier
    obj_map<func_decl, proof *>      m_decl2macro_pr; // func-decl -> quantifier_proof
    obj_map<func_decl, expr_dependency *> m_decl2macro_dep; // func-decl -> unsat core dependency
    func_decl_ref_vector             m_decls;
    quantifier_ref_vector            m_macros;
    proof_ref_vector                 m_macro_prs;
    expr_dependency_ref_vector       m_macro_deps;
    obj_hashtable<func_decl>         m_forbidden_set;
    func_decl_ref_vector             m_forbidden;
    struct scope {
        unsigned m_decls_lim;
        unsigned m_forbidden_lim;
    };
    svector<scope>                   m_scopes;

    func_decl_dependencies           m_deps;

    void restore_decls(unsigned old_sz);
    void restore_forbidden(unsigned old_sz);
    
    struct macro_expander_cfg;
    struct macro_expander_rw;

public:
    macro_manager(ast_manager & m);
    ~macro_manager();
    ast_manager & get_manager() const { return m; }
    macro_util & get_util() { return m_util; }
    bool insert(func_decl * f, quantifier * m, proof * pr, expr_dependency * dep = nullptr);
    bool has_macros() const { return !m_macros.empty(); }
    void push_scope();
    void pop_scope(unsigned num_scopes);
    void reset();
    void mark_forbidden(unsigned n, expr * const * exprs);
    void mark_forbidden(unsigned n, justified_expr const * exprs);
    void mark_forbidden(expr * e) { mark_forbidden(1, &e); }
    bool is_forbidden(func_decl * d) const { return m_forbidden_set.contains(d); }
    obj_hashtable<func_decl> const & get_forbidden_set() const { return m_forbidden_set; }
    void display(std::ostream & out);
    unsigned get_num_macros() const { return m_decls.size(); }
    unsigned get_first_macro_last_level() const { return m_scopes.empty() ? 0 : m_scopes.back().m_decls_lim; }
    func_decl * get_macro_func_decl(unsigned i) const { return m_decls.get(i); }
    func_decl * get_macro_interpretation(unsigned i, expr_ref & interp) const;
    quantifier * get_macro_quantifier(func_decl * f) const { quantifier * q = nullptr; m_decl2macro.find(f, q); return q; }
    void get_head_def(quantifier * q, func_decl * d, app * & head, expr * & def) const;
    void expand_macros(expr * n, proof * pr, expr_dependency * dep, expr_ref & r, proof_ref & new_pr, expr_dependency_ref & new_dep);


};

#endif /* MACRO_MANAGER_H_ */


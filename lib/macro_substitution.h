/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    macro_substitution.h

Abstract:

    Mapping from func_decl to quantifiers of the form
             Forall X. f(X) = T[X]
             Forall X. f(X) iff C[X]

Author:

    Leonardo (leonardo) 2012-02-17

Notes:

--*/
#ifndef _MACRO_SUBSTITUTION_H_
#define _MACRO_SUBSTITUTION_H_

#include"ast.h"

class macro_substitution {
    ast_manager &                                      m_manager;
    obj_map<func_decl, quantifier *>                   m_decl2macro;
    scoped_ptr<obj_map<func_decl, proof *> >           m_decl2macro_pr;
    scoped_ptr<obj_map<func_decl, expr_dependency *> > m_decl2macro_dep;
    unsigned                                           m_cores_enabled:1;
    unsigned                                           m_proofs_enabled:1;

    void init();
public:
    macro_substitution(ast_manager & m);
    macro_substitution(ast_manager & m, bool cores_enabled);
    macro_substitution(ast_manager & m, bool cores_enabled, bool proofs_enabled);
    ~macro_substitution();

    ast_manager & m() const { return m_manager; }

    bool proofs_enabled() const { return m_proofs_enabled; }
    bool unsat_core_enabled() const { return m_cores_enabled; }

    bool empty() const { return m_decl2macro.empty(); }

    void insert(func_decl * f, quantifier * m, proof * pr, expr_dependency * dep = 0);
    void erase(func_decl * f);
    bool contains(func_decl * f) { return m_decl2macro.contains(f); }
    bool find(func_decl * f, quantifier * & q, proof * & pr);
    bool find(func_decl * f, quantifier * & q, proof * & pr, expr_dependency * & dep);
    void get_head_def(quantifier * q, func_decl * f, app * & head, expr * & def);
    
    void reset();
    void cleanup();
};

#endif

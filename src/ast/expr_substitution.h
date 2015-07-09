/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    expr_substitution.h

Abstract:

    expr -> expr substitution

Author:

    Leonardo (leonardo) 2011-04-29

Notes:

--*/
#ifndef EXPR_SUBSTITUTION_H_
#define EXPR_SUBSTITUTION_H_

#include"ast.h"

class expr_substitution {
    ast_manager &                                m_manager;
    obj_map<expr, expr*>                         m_subst;
    scoped_ptr<obj_map<expr, proof*> >           m_subst_pr;
    scoped_ptr<obj_map<expr, expr_dependency*> > m_subst_dep;
    unsigned                                     m_cores_enabled:1;
    unsigned                                     m_proofs_enabled:1;

    void init();

public:
    expr_substitution(ast_manager & m);
    expr_substitution(ast_manager & m, bool cores_enabled);
    expr_substitution(ast_manager & m, bool cores_enabled, bool proofs_enabled);
    ~expr_substitution();

    ast_manager & m() const { return m_manager; }

    bool proofs_enabled() const { return m_proofs_enabled; }
    bool unsat_core_enabled() const { return m_cores_enabled; }

    bool empty() const { return m_subst.empty(); }
    void insert(expr * s, expr * def, proof * def_pr = 0, expr_dependency * def_dep = 0);
    void erase(expr * s);
    bool find(expr * s, expr * & def, proof * & def_pr);
    bool find(expr * s, expr * & def, proof * & def_pr, expr_dependency * & def_dep);
    bool contains(expr * s);
    void reset();
    void cleanup();
};

#endif

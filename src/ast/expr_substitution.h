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

#include "ast/ast.h"

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
    unsigned size() const { return m_subst.size(); }
    void insert(expr * s, expr * def, proof * def_pr = nullptr, expr_dependency * def_dep = nullptr);
    void erase(expr * s);
    bool find(expr * s, expr * & def, proof * & def_pr);
    bool find(expr * s, expr * & def, proof * & def_pr, expr_dependency * & def_dep);
    bool contains(expr * s);
    void reset();
    void cleanup();

    std::ostream& display(std::ostream& out);
};

class scoped_expr_substitution {
    expr_substitution& m_subst;
    expr_ref_vector    m_trail;
    unsigned_vector    m_trail_lim;
public:

    scoped_expr_substitution(expr_substitution& s): m_subst(s), m_trail(s.m()) {}
    ~scoped_expr_substitution() {}

    void insert(expr * s, expr * def, proof * def_pr = nullptr, expr_dependency * def_dep = nullptr) {
        if (!m_subst.contains(s)) {
            m_subst.insert(s, def, def_pr, def_dep); 
            m_trail.push_back(s);
        }
    }
    void reset() { m_subst.reset(); m_trail.reset(); m_trail_lim.reset(); }
    void push() { m_trail_lim.push_back(m_trail.size()); }
    void pop(unsigned n) { 
        if (n > 0) {
            unsigned new_sz = m_trail_lim.size() - n;
            unsigned old_sz = m_trail_lim[new_sz];
            for (unsigned i = old_sz; i < m_trail.size(); ++i) m_subst.erase(m_trail[i].get());  
            m_trail.resize(old_sz); 
            m_trail_lim.resize(new_sz); 
        }
    }
    unsigned scope_level() const { return m_trail_lim.size(); }
    bool empty() const { return m_subst.empty(); }
    unsigned size() const { return m_subst.size(); }
    expr* find(expr * e) { proof* pr; expr* d = nullptr; if (find(e, d, pr)) return d; else return e; }
    bool find(expr * s, expr * & def, proof * & def_pr) { return m_subst.find(s, def, def_pr); }
    bool find(expr * s, expr * & def, proof * & def_pr, expr_dependency * & def_dep) { return m_subst.find(s, def, def_pr, def_dep); }
    bool contains(expr * s) { return m_subst.contains(s); }
    void cleanup() { m_subst.cleanup(); }
    std::ostream& display(std::ostream& out) { return m_subst.display(out); }
};

#endif

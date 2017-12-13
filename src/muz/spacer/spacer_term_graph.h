/**++
Copyright (c) Arie Gurfinkel

Module Name:

    spacer_term_graph.h

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel

Notes:

--*/
#ifndef _SPACER_TERM_GRAPH_H_
#define  _SPACER_TERM_GRAPH_H_

#include "ast/ast.h"

#include "util/plugin_manager.h"

namespace spacer {

class term;

class term_graph_plugin {
    family_id m_id;
public:
    term_graph_plugin(family_id fid) : m_id(fid) {}
    virtual ~term_graph_plugin() {}

    family_id get_family_id() const {return m_id;}

    /// Process (and potentially augment) a literal
    virtual app* process_lit (app *lit) {return lit;}
};

class term_graph {
    ast_manager &m;
    ptr_vector<term> m_terms;
    app_ref_vector m_lits;
    u_map<term* > m_app2term;

    app_ref_vector m_pinned;
    u_map<app*> m_term2app;

    plugin_manager<term_graph_plugin> m_plugins;

    void merge(term &t1, term &t2);

    term *mk_term(app *t);
    term *get_term(app *t);

    term *internalize_term(app *t);
    void internalize_eq(app *a1, app *a2);
    void internalize_lit(app *lit);

    bool is_internalized(app *a);

    bool term_le(term const &t1, term const &t2);
    void pick_root (term &t);
    void pick_roots();

    void reset_marks();

    app *mk_app_core(app* a);
    app_ref mk_app(term const &t);
    app_ref mk_app(app *a);
    void mk_equalities(term const &t, app_ref_vector &out);
    void mk_all_equalities(term const &t, app_ref_vector &out);
    void display(std::ostream &out);
public:
    term_graph(ast_manager &man);
    ~term_graph();

    ast_manager &get_ast_manager() const {return m;}

    void add_lit(app *lit);

    void reset();
    void to_lits (app_ref_vector &lits, bool all_equalities = false);
    app_ref to_app();

};

}
#endif

/**++
Copyright (c) Arie Gurfinkel

Module Name:

    qe_term_graph.h

Abstract:

    Equivalence graph of terms

Author:

    Arie Gurfinkel

Notes:

--*/
#ifndef QE_TERM_GRAPH_H__
#define QE_TERM_GRAPH_H__

#include "ast/ast.h"
#include "util/plugin_manager.h"

namespace qe {

    class term;

    class term_graph_plugin {
        family_id m_id;
    public:
        term_graph_plugin(family_id fid) : m_id(fid) {}
        virtual ~term_graph_plugin() {}

        family_id get_family_id() const {return m_id;}
        
        /// Process (and potentially augment) a literal
        virtual expr_ref process_lit (expr *lit) = 0;
    };
   

    class term_graph {
        struct term_hash { unsigned operator()(term const* t) const; };
        struct term_eq { bool operator()(term const* a, term const* b) const; };
        ast_manager &     m;
        ptr_vector<term>  m_terms;
        expr_ref_vector    m_lits; // NSB: expr_ref_vector?
        u_map<term* >     m_app2term;        
        ast_ref_vector    m_pinned;
        u_map<expr*>      m_term2app;
        plugin_manager<term_graph_plugin> m_plugins;
        ptr_hashtable<term, term_hash, term_eq> m_cg_table;
        vector<std::pair<term*,term*>> m_merge;
        
        void merge(term &t1, term &t2);
        void merge_flush();
        
        term *mk_term(expr *t);
        term *get_term(expr *t);
        
        term *internalize_term(expr *t);
        void internalize_eq(expr *a1, expr *a2);
        void internalize_lit(expr *lit);
        
        bool is_internalized(expr *a);
        
        bool term_lt(term const &t1, term const &t2);
        void pick_root (term &t);
        void pick_roots();
        
        void reset_marks();
        
        expr* mk_app_core(expr* a);
        expr_ref mk_app(term const &t);
        expr* mk_pure(term& t);
        expr_ref mk_app(expr *a);
        void mk_equalities(term const &t, expr_ref_vector &out);
        void mk_all_equalities(term const &t, expr_ref_vector &out);
        void display(std::ostream &out);        

    public:
        term_graph(ast_manager &m);
        ~term_graph();
        
        ast_manager& get_ast_manager() const { return m;}
        
        void add_lit(expr *lit); 
        void add_lits(expr_ref_vector const &lits) { for (expr* e : lits) add_lit(e); }
        void add_eq(expr* a, expr* b) { internalize_eq(a, b); }
        
        void reset();

        // deprecate?
        void to_lits(expr_ref_vector &lits, bool all_equalities = false);
        expr_ref to_app(); 

        /**
         * Return literals obtained by projecting added literals 
         * onto the vocabulary of decls (if exclude is false) or outside the 
         * vocabulary of decls (if exclude is true).
         */
         expr_ref_vector project(func_decl_ref_vector const& decls, bool exclude);
        
    };

}
#endif

/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_semantic_tautology.h

Abstract:

    Semantic tautology detection

Author:

    Leonardo de Moura (leonardo) 2008-02-11.

Revision History:

--*/
#ifndef _SPC_SEMANTIC_TAUTOLOGY_H_
#define _SPC_SEMANTIC_TAUTOLOGY_H_

#include"spc_literal.h"
#include"list.h"
#include"obj_hashtable.h"
#include"map.h"

namespace spc {

    typedef obj_map<expr, expr *> expr2expr;

    expr * find(expr2expr & f, expr * e);

    /**
       \brief Functor for detecting semantic tautology.
       A clause C is a semantic tautology if it has the following form:

       s_1 != t_1 or ... or s_n != t_n or s = t or R

       sigma(s_1 = t_1), ..., sigma(s_n t_n) |= sigma(s = t)
       where sigma maps variables to constants.
    */
    class semantic_tautology {
        typedef std::pair<expr *, expr *> expr_pair;
        
        typedef obj_hashtable<expr> already_found;
        typedef expr2expr find_map;
        typedef obj_map<expr, list<app*> *> use_list;
        typedef obj_map<expr, unsigned> size_map;        

        struct k_hash {
            unsigned operator()(app * n) const { return n->get_decl()->get_id(); }
        };

        struct c_hash {
            find_map & m_find;
            c_hash(find_map & f):m_find(f) {}
            unsigned operator()(app * n, unsigned i) const { 
                unsigned id = spc::find(m_find, n->get_arg(i))->get_id();
                TRACE("semantic_tautology_detail", tout << "child(" << i << ") = #" << id << "\n";);
                return id;
            }
        };

        struct cg_hash {
            ast_manager & m_manager;
            k_hash     m_k_hash;
            c_hash     m_c_hash;
            cg_hash(ast_manager & m, find_map & f):m_manager(m), m_c_hash(f) {}
            unsigned operator()(app * n) const;
        };

        struct cg_eq {
            find_map & m_find;
            cg_eq(find_map & f):m_find(f) {}
            bool operator()(app * n1, app * n2) const;
        };
        
        typedef ptr_hashtable<app, cg_hash, cg_eq> cg_table;

        ast_manager &      m_manager;
        region             m_region;
        ptr_vector<app>    m_init_todo;
        svector<expr_pair> m_todo;
        already_found      m_already_found;
        use_list           m_use_list;
        find_map           m_find;
        size_map           m_size;
        cg_table           m_cg_table;

        bool is_target(unsigned num_lits, literal * lits);
        void reset();
        void update_use_list(app * parent, expr * child);
        void push_init_core(expr * n);
        void push_init(expr * atom);
        void init_use_list();
        void init(unsigned num_lits, literal * lits);
        expr * find(expr * n) { return spc::find(m_find, n); }
        void remove_parents(expr * n1);
        void restore_parents(expr * n1, expr * n2);
        void assert_eq(expr * n1, expr * n2);
        void process_eqs();
        bool contains_complement(unsigned num_lits, literal * lits, unsigned i, bool sign, expr * atom);
        bool is_tautology(unsigned num_lits, literal * lits);

    public:
        semantic_tautology(ast_manager & m);
        
        bool operator()(unsigned num_lits, literal * lits);
    };

};

#endif /* _SPC_SEMANTIC_TAUTOLOGY_H_ */


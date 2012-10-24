/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_superposition.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-15.

Revision History:

--*/
#ifndef _SPC_SUPERPOSITION_H_
#define _SPC_SUPERPOSITION_H_

#include"spc_clause.h"
#include"spc_clause_pos_set.h"
#include"substitution_tree.h"
#include"obj_hashtable.h"
#include"sparse_use_list.h"
#include"normalize_vars.h"
#include"spc_statistics.h"

namespace spc {

    /**
       \brief Functor for applying the superposition right/left rules.

       - Superposition Left
       s = t or S,  u != v or R
       ==>
       sigma(u[p<-t] != v or S or R)
       
       sigma is the mgu(u|p, s)
       sigma(s) not greater than sigma(t)
       sigma(u) not greater than sigma(v)
       sigma(s = t) is eligible for paramodulation
       sigma(u != v) is eligible for resolution
       u|p is not a variable
       

       - Superposition Right
       s = t or S,  u = v or R
       ==>
       sigma(u[p<-t] != v or S or R)
       
       Same restrictions of Superposition Left
    
       This functor also applied binary resolution rule.

       We say the left clause is the main clause in the superposition.
    */
    class superposition {
        ast_manager &     m_manager;
        order &           m_order;
        statistics &      m_stats;
        substitution      m_subst;

        // indexes for left clause
        substitution_tree m_p; // potential left hand sides for superposition
        typedef sparse_use_list<expr, svector<clause_pos_pair> > p2clause_set;
        p2clause_set      m_p2clause_set;

        void insert_p(clause * cls, expr * lhs, unsigned i);
        void insert_p(clause * cls, literal & l, unsigned i);

        void erase_p(clause * cls, expr * lhs, unsigned i);
        void erase_p(clause * cls, literal & l, unsigned i);

        // indexes for right clause
        substitution_tree m_r; // potential targets for superposition 
        typedef sparse_use_list<expr, clause_pos_set> r2clause_set;
        r2clause_set      m_r2clause_set;
        ptr_vector<app>   m_todo;

        void insert_r(clause * cls, expr * n, unsigned i, bool lhs);
        void insert_r(clause * cls, literal & l, unsigned i);
        void erase_r(clause * cls, literal & l, unsigned i);

        normalize_vars       m_normalize_vars;
        
        // temporary fields...
        ptr_vector<clause> * m_new_clauses;
        clause *             m_clause;
        literal *            m_lit;
        expr *               m_lhs;
        expr *               m_rhs;
        app *                m_target;
        unsigned             m_idx;
        unsigned             m_deltas[2];
        family_id            m_spc_fid;

        void normalize_literals(unsigned num_lits, literal * lits, literal_buffer & result);
        void copy_literals(clause * s, unsigned idx, unsigned offset, literal_buffer & result);
        void mk_sp_clause(unsigned num_lits, literal * lits, justification * p1, justification * p2);
        void mk_res_clause(unsigned num_lits, literal * lits, justification * p1, justification * p2);
        void try_superposition_main(expr * lhs, expr * rhs);
        void try_superposition_main();
        void found_r(expr * r);
        void try_superposition_aux(expr * lhs, expr * rhs);
        void try_superposition_aux();
        void found_p(expr * p);
        void try_resolution();
        void found_res(expr * r);

        friend struct r_visitor;
        struct r_visitor : public st_visitor {
            superposition & m_owner;
            r_visitor(superposition & o, substitution & s):st_visitor(s), m_owner(o) {}
            virtual bool operator()(expr * e) { m_owner.found_r(e); return true; /* continue */ }
        };

        friend struct p_visitor;
        struct p_visitor : public st_visitor {
            superposition & m_owner;
            p_visitor(superposition & o, substitution & s):st_visitor(s), m_owner(o) {}
            virtual bool operator()(expr * e) { m_owner.found_p(e); return true; /* continue */ }
        };

        friend struct res_visitor;
        struct res_visitor : public st_visitor {
            superposition & m_owner;
            res_visitor(superposition & o, substitution & s):st_visitor(s), m_owner(o) {}
            virtual bool operator()(expr * e) { m_owner.found_res(e); return true; /* continue */ }
        };

    public:
        superposition(ast_manager & m, order & o, statistics & stats);
        ~superposition();

        void insert(clause * cls);
        void erase(clause * cls);
        void reset();
        
        void operator()(clause * cls, ptr_vector<clause> & new_clauses);
    };

};

#endif /* _SPC_SUPERPOSITION_H_ */


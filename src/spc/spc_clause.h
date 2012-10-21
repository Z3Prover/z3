/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_clause.h

Abstract:

    Superposition Calculus Clause

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef _SPC_CLAUSE_H_
#define _SPC_CLAUSE_H_

#include"ast.h"
#include"splay_tree.h"
#include"use_list.h"
#include"spc_literal.h"
#include"spc_justification.h"
#include"use_list.h"

namespace spc {

    class context;

    /**
       \brief Superposition Calculus clause.
    */
    class clause {
        struct compare {
            // ignoring potential overflow/underflow
            int operator()(clause * c1, clause * c2) const {
                return static_cast<int>(c1->get_id()) - static_cast<int>(c2->get_id());
            }
        };
    public:
        typedef splay_tree<clause *, compare> set;
    private:
        unsigned            m_id;           // clause unique id
        unsigned            m_time;         // how old is the clause. 
        unsigned            m_num_vars;     // approx. number of variables (i.e., max_var_id + 1)
        unsigned            m_sym_count;    // number of symbols
        unsigned            m_const_count;  // number of constants
        unsigned            m_depth;        // depth (i.e., max depth of a literal)
        unsigned            m_proof_depth;  
        unsigned            m_scope_lvl;    // which scope level owns the clause
        unsigned            m_num_lits[2];  // number of positive [0] and negative [1] literals. 
        unsigned            m_num_lits_capacity; // some of the clause literals can be simplified and removed, this field contains the original number of literals (used for GC).
        unsigned            m_bidx;         // position on the backtracking stack
        bool                m_ground:1;
        bool                m_processed:1;  
        bool                m_indexed:1;
        bool                m_has_sel_lit:1;
        justification *     m_justification;
        set                 m_children;
        literal             m_lits[0];
        friend class context;

        void set_fields(unsigned num_lits, literal * lits);
        unsigned get_bidx() const { return m_bidx; }
        void init(unsigned idx, unsigned time);
        void update_parents(ptr_buffer<clause> & parents);
        void set_bidx(unsigned idx) { SASSERT(m_bidx == UINT_MAX); m_bidx = idx; }
        void add_child(clause * c) { m_children.insert(c); }
        void del_child(clause * c) { m_children.erase(c); }
        void set_processed(bool f) { m_processed = f; }
        void set_indexed(bool f) { m_indexed = f; }
        void sort_literals();
        /**
           \brief Release ownership of the justification.
        */
        justification * release_justification() { justification * r = m_justification; m_justification = 0; return r; }

        clause(ast_manager & m, unsigned num_lits, literal * lits, justification * p, unsigned scope_lvl);

    public:
        static clause * mk(ast_manager & m, unsigned num_lits, literal * lits, justification * p, unsigned scope_lvl);
        void deallocate(ast_manager & m);

        unsigned get_id() const { SASSERT(m_id != UINT_MAX); return m_id; }
        unsigned get_time() const { return m_time; }
        unsigned get_symbol_count() const { return m_sym_count; }
        unsigned get_proof_depth() const { return m_proof_depth; }
        unsigned get_num_literals() const { return m_num_lits[0] + m_num_lits[1]; }
        unsigned get_num_literals_capacity() const { return m_num_lits_capacity; }
        unsigned get_num_pos_literals() const { return m_num_lits[0]; }
        unsigned get_num_neg_literals() const { return m_num_lits[1]; }
        unsigned get_depth() const { return m_depth; }
        unsigned get_const_count() const { return m_const_count; }
        unsigned get_scope_lvl() const { return m_scope_lvl; }
        unsigned get_num_vars() const { return m_num_vars; }
        bool empty() const { return m_num_lits[0] == 0 && m_num_lits[1] == 0; }
        literal const & get_literal(unsigned idx) const { return m_lits[idx]; }
        literal & get_literal(unsigned idx) { return m_lits[idx]; }
        literal * get_literals() const { return const_cast<literal*>(m_lits); }
        justification * get_justification() const { return m_justification; }
        bool is_processed() const { return m_processed; }
        bool is_indexed() const { return m_indexed; }
        bool is_ground() const { return m_ground; }
        void select_literal(unsigned idx);
        bool is_maximal(order & o, literal const & l, unsigned offset = 0, substitution * s = 0) const;
        bool is_sel_maximal(order & o, literal const & l, unsigned offset = 0, substitution * s = 0) const ;
        bool is_eligible_for_resolution(order & o, literal const & l, unsigned offset = 0, substitution * s = 0) const;
        bool is_eligible_for_paramodulation(order & o, literal const & l, unsigned offset = 0, substitution * s = 0) const;
        bool has_sel_lit() const { return m_has_sel_lit; }
        void try_to_orient_literals(order & o);
        void update_lits(ast_manager & m, unsigned num_lits, literal * lits, justification * j);

        void display(std::ostream & out, ast_manager & m, bool detailed = false);
        unsigned hash() const { return m_id; }
    };

    typedef ptr_vector<clause> clause_vector;

    /**
       \brief Clause Statistics (used to build clauses, subsumption, etc).
    */
    struct clause_stat : public expr_stat {
        unsigned m_num_lits[2];
        clause_stat() {
            m_num_lits[0] = 0;
            m_num_lits[1] = 0;
        }
    };

    /**
       \brief Compute the statistics for a clause with num_lits
       literals lits, and store the results in stat.
    */
    void get_clause_stat(unsigned num_lits, literal * lits, clause_stat & stat);

    /**
       \brief A mapping from clause-id's to clauses
    */
    class id2clause {
        ptr_vector<clause> m_clauses;
    public:
        void insert(clause * c) { return m_clauses.setx(c->get_id(), c, 0); }
        void erase(clause * c) { unsigned id = c->get_id(); if (id < m_clauses.size()) m_clauses[id] = 0; }
        clause * operator()(unsigned id) const { return m_clauses.get(id, 0); }
    };
};

#endif /* _SPC_CLAUSE_H_ */


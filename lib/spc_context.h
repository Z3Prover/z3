/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_context.h

Abstract:

    Superposition Calculus Engine

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#ifndef _SPC_CONTEXT_H_
#define _SPC_CONTEXT_H_

#include"spc_params.h"
#include"spc_clause.h"
#include"spc_clause_selection.h"
#include"spc_literal_selection.h"
#include"spc_semantic_tautology.h"
#include"spc_rewriter.h"
#include"spc_asserted_literals.h"
#include"spc_subsumption.h"
#include"spc_eq_resolution.h"
#include"spc_factoring.h"
#include"spc_superposition.h"
#include"spc_statistics.h"
#include"spc_der.h"
#include"substitution_tree.h"
#include"order.h"

namespace spc {

    /**
       \brief Logical context of the superposition calculus engine.
    */
    class context {
    public:
        statistics                  m_stats;
    protected:
        typedef clause::set clause_set;
        
        ast_manager &               m_manager;
        spc_params &                m_params;
        small_object_allocator &    m_alloc;
        order &                     m_order;
        clause_selection &          m_cls_sel;
        literal_selection &         m_lit_sel;
        simplifier &                m_simplifier;
        unsigned                    m_time;
        unsigned                    m_scope_lvl;
        id_gen                      m_cls_id_gen;
        found_literals              m_found_literals;
        semantic_tautology          m_sem_taut;
        asserted_literals           m_asserted_literals;
        rewriter                    m_rewriter;
        der                         m_der;
        subsumption                 m_subsumption;
        eq_resolution               m_eq_resolution;
        factoring                   m_factoring;
        superposition               m_superposition;
        vector<clause_vector>       m_clauses_to_unfreeze;
        vector<clause_vector>       m_clauses_to_delete;
        unsigned_vector             m_time_trail;
        clause *                    m_unsat;
        ptr_vector<clause>          m_new_clauses;

        void insert_index(clause * cls);
        void erase_index(clause * cls);

        void init_clause(clause * cls);
        clause * mk_clause(unsigned num_lits, literal * lits, justification * p, unsigned scope_lvl);

        void del_clause(clause * cls);
        void del_clauses(unsigned scope_lvl);

        void freeze_clause_until(clause * cls, unsigned scope_lvl);
        void unfreeze_clause(clause * cls);
        void unfreeze_clauses(unsigned scope_lvl);

        bool trivial(unsigned num_lits, literal * lits);
        bool trivial(clause * cls);
        clause * simplify(clause * cls);
        void simplify_processed(clause * cls);
        bool redundant(clause * cls);
        void generate(clause * cls);
        void process_new_clause(clause * cls);

        void display(std::ostream & out, vector<clause_vector> const & cvs, unsigned scope_lvl, bool frozen) const;
        
        void set_conflict(clause * cls);

    public:
        context(ast_manager & m, order & o, clause_selection & cs, literal_selection & ls, simplifier & s, spc_params & params);
        ~context();
        
        simplifier & get_simplifier() { return m_simplifier; }
        order & get_order() { return m_order; }
        ast_manager & get_manager() { return m_manager; }

        unsigned get_scope_lvl() const { return m_scope_lvl; }

        void assert_expr(expr * n, proof * p, unsigned scope_lvl = 0);
        void assert_expr(expr * n, justification * p, unsigned scope_lvl = 0);
        void saturate(unsigned threshold);
        bool inconsistent() const { return m_unsat != 0; }
        bool processed_all() const { return m_cls_sel.empty(); }
        void push_scope();
        void pop_scope(unsigned num_scopes);
        void reset();
        void display(std::ostream & out) const;
        void display_statistics(std::ostream & out) const;
    };
};

#endif /* _SPC_CONTEXT_H_ */

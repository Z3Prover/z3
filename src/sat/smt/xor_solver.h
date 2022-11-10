/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    xor_solver.h

Abstract:

    XOR solver.
    Interface outline.

--*/

#pragma once

#include "sat/smt/euf_solver.h"
#include "sat/smt/xor_gaussian.h"

namespace xr {
    
    class solver;

    class solver : public euf::th_solver {
        friend class xor_matrix_finder;
        friend class EGaussian;

        euf::solver*              m_ctx = nullptr;

        unsigned                  m_num_scopes = 0;

        literal_vector            m_prop_queue;
        unsigned_vector           m_prop_queue_lim;
        unsigned                  m_prop_queue_head = 0;
        // ptr_vector<justification> m_justifications;
        // unsigned_vector           m_justifications_lim;

        bool_var_vector                m_tmp_xor_clash_vars;
             
        vector<xor_clause>             m_xorclauses;
        vector<xor_clause>             m_xorclauses_orig;
        vector<xor_clause>             m_xorclauses_unused;
             
        bool_var_vector                m_removed_xorclauses_clash_vars;
        bool                           m_detached_xor_clauses = false;
        bool                           m_xor_clauses_updated = false;
        
        vector<svector<gauss_watched>> m_gwatches;
        ptr_vector<EGaussian>          m_gmatrices;
        svector<gauss_data>            m_gqueuedata;
        
        visit_helper                   m_visited;
        
        // tmp
        bool_var_vector m_occurrences;
        // unfortunately, we cannot use generic "m_visited" here, 
        // as the number of occurrences might be quite high 
        // and we need the list of occurrences
        unsigned_vector m_occ_cnt; 
        bool_var_vector m_interesting;
        
        void force_push();
        void push_core();
        void pop_core(unsigned num_scopes);

        bool xor_has_interesting_var(const xor_clause& x);
        
        void clean_xor_no_prop(sat::literal_vector& ps, bool& rhs);
        void add_every_combination_xor(const sat::literal_vector& lits, const bool attach);
        
        void add_xor_clause(const sat::literal_vector& lits, bool rhs, const bool attach);
        
        bool inconsistent() const { return s().inconsistent(); }
        
    public:
        solver(euf::solver& ctx);
        solver(ast_manager& m, euf::theory_id id);
        ~solver() override;
        th_solver* clone(euf::solver& ctx) override;

        void add_xor(const sat::literal_vector& lits) override { 
            add_xor_clause(lits, true, true);
        }
        
        sat::literal internalize(expr* e, bool sign, bool root)  override { UNREACHABLE(); return sat::null_literal; }

        void internalize(expr* e) override { UNREACHABLE(); }
        
        void asserted(sat::literal l) override;
        bool unit_propagate() override;
        sat::justification gauss_jordan_elim(const sat::literal p, const unsigned currLevel);
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override;

        void pre_simplify() override;
        void simplify() override;

        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        
        void init_search() override {
            find_and_init_all_matrices();
        }
        
        bool clean_xor_clauses(vector<xor_clause>& xors);
        bool clean_one_xor(xor_clause& x);
        bool clear_gauss_matrices(const bool destruct);
        bool find_and_init_all_matrices();
        bool init_all_matrices();
        
        void move_xors_without_connecting_vars_to_unused();
        void clean_equivalent_xors(vector<xor_clause>& txors);
        
        bool xor_together_xors(vector<xor_clause>& xors);
        
        sat::justification mk_justification(const int level, const unsigned int matrix_no, const unsigned int row_i);
        
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
};
}

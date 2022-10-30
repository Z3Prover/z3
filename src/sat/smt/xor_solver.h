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
    
#if 0
    class xor_finder {
        
        solver& m_solver;
        
        unsigned_vector occcnt;
        sat::literal_vector& toClear;
        unsigned_vector& seen;
        vector<unsigned char>& seen2;
        unsigned_vector interesting;
        
        public:
        
        xor_finder(solver& s) : m_solver(s) {} 
        
        void grab_mem();
        
        void move_xors_without_connecting_vars_to_unused();
        
        bool xor_together_xors(vector<Xor>& this_xors);
        
        void clean_xors_from_empty(vector<Xor>& thisxors);
        
        unsigned xor_two(Xor const* x1_p, Xor const* x2_p, uint32_t& clash_var);
        
        bool xor_has_interesting_var(const Xor& x) {
            for(uint32_t v: x) {
                if (solver->seen[v] > 1) {
                    return true;
                }
            }
            return false;
        }
    };
#endif

    class solver : public euf::th_solver {
        friend class xor_matrix_finder;
        friend class EGaussian;


        euf::solver* m_ctx = nullptr;
        sat::sat_internalizer& si;
        
        unsigned            m_num_scopes = 0;
        
        sat::literal_vector  m_prop_queue;
        unsigned_vector      m_prop_queue_lim;
        unsigned             m_prop_queue_head = 0;

        ptr_vector<Xor> m_xorclauses;
        ptr_vector<Xor> m_xorclauses_orig;
        ptr_vector<Xor> m_xorclauses_unused;
        
        vector<unsigned> removed_xorclauses_clash_vars;
        bool detached_xor_clauses = false;
        bool xor_clauses_updated = false;

        svector<svector<GaussWatched>> gwatches;
        
        svector<EGaussian*> gmatrices;
        svector<gauss_data> gqueuedata;
        
        void force_push();
        void push_core();
        void pop_core(unsigned num_scopes);

    public:
        solver(euf::solver& ctx);
        solver(ast_manager& m, sat::sat_internalizer& si, euf::theory_id id);
        th_solver* clone(euf::solver& ctx) override;

        sat::literal internalize(expr* e, bool sign, bool root)  override { UNREACHABLE(); return sat::null_literal; }

        void internalize(expr* e) override { UNREACHABLE(); }

        void asserted(sat::literal l) override;
        bool unit_propagate() override;
        justification gauss_jordan_elim(const sat::literal p, const unsigned currLevel);
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override;

        void pre_simplify() override;
        void simplify() override;

        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        
        void init_search() override {
            find_and_init_all_matrices();
        }
        
        bool find_and_init_all_matrices();
        bool init_all_matrices();

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
    };
}

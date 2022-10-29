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

namespace xr {

    class solver;
    
    class constraint {
        unsigned        m_size;
        bool            m_detached = false;
        size_t          m_obj_size;
        bool            m_rhs;
        sat::bool_var   m_vars[0];
        
    public:
        static size_t get_obj_size(unsigned num_lits) { return sat::constraint_base::obj_size(sizeof(constraint) + num_lits * sizeof(sat::bool_var)); }
        
        constraint(const svector<sat::bool_var>& ids, bool expected_result) : m_size(ids.size()), m_obj_size(get_obj_size(ids.size())), m_rhs(expected_result) {
            unsigned i = 0;
            for (auto v : ids)
                m_vars[i++] = v;
        }
        sat::ext_constraint_idx cindex() const { return sat::constraint_base::mem2base(this); }
        void deallocate(small_object_allocator& a) { a.deallocate(m_obj_size, sat::constraint_base::mem2base_ptr(this)); }
        sat::bool_var operator[](unsigned i) const { return m_vars[i]; }
        bool is_detached() const { return m_detached; }
        unsigned get_size() const { return m_size; }
        bool get_rhs() const { return m_rhs; }
        sat::bool_var const* begin() const { return m_vars; }
        sat::bool_var const* end() const { return m_vars + m_size; }
        std::ostream& display(std::ostream& out) const {
            bool first = true;
            for (auto v : *this)
                out << (first ? "" : " ^ ") << v, first = false;
            return out << " = " << m_rhs;
        }
    };

#if 0
    class EGaussian {
    public:
        EGaussian(
            solver* solver,
            const uint32_t matrix_no,
            const vector<constraint>& xorclauses
        );
        ~EGaussian();
        bool is_initialized() const;

        ///returns FALSE in case of conflict
        bool find_truths(
            GaussWatched*& i,
            GaussWatched*& j,
            const uint32_t var,
            const uint32_t row_n,
            gauss_data& gqd
        );

        vector<Lit>* get_reason(const uint32_t row, int32_t& out_ID);

        // when basic variable is touched , eliminate one col
        void eliminate_col(
            uint32_t p,
            gauss_data& gqd
        );
        void canceling();
        bool full_init(bool& created);
        void update_cols_vals_set(bool force = false);
        void print_matrix_stats(uint32_t verbosity);
        bool must_disable(gauss_data& gqd);
        void check_invariants();
        void update_matrix_no(uint32_t n);
        void check_watchlist_sanity();
        uint32_t get_matrix_no();
        void finalize_frat();
        void move_back_xor_clauses();

        vector<constraint> xorclauses;

    private:
        solver* solver;   // orignal sat solver

        //Cleanup
        void clear_gwatches(const uint32_t var);
        void delete_gauss_watch_this_matrix();
        void delete_gausswatch(const uint32_t  row_n);

        //Invariant checks, debug
        void check_no_prop_or_unsat_rows();
        void check_tracked_cols_only_one_set();
        bool check_row_satisfied(const uint32_t row);
        void print_gwatches(const uint32_t var) const;
        void check_row_not_in_watch(const uint32_t v, const uint32_t row_num) const;

        //Reason generation
        vector<XorReason> xor_reasons;
        vector<Lit> tmp_clause;
        uint32_t get_max_level(const GaussQData& gqd, const uint32_t row_n);

        //Initialisation
        void eliminate();
        void fill_matrix();
        void select_columnorder();
        gret init_adjust_matrix(); // adjust matrix, include watch, check row is zero, etc.
        double get_density();

        //Helper functions
        void prop_lit(
            const gauss_data& gqd, const uint32_t row_i, const Lit ret_lit_prop);

        ///////////////
        // Internal data
        ///////////////
        uint32_t matrix_no;
        bool initialized = false;
        bool cancelled_since_val_update = true;
        uint32_t last_val_update = 0;

        //Is the clause at this ROW satisfied already?
        //satisfied_xors[decision_level][row] tells me that
        vector<char> satisfied_xors;

        // Someone is responsible for this column if TRUE
        ///we always WATCH this variable
        vector<char> var_has_resp_row;

        ///row_to_var_non_resp[ROW] gives VAR it's NOT responsible for
        ///we always WATCH this variable
        vector<uint32_t> row_to_var_non_resp;


        PackedMatrix mat;
        vector<vector<char>> bdd_matrix;
        vector<uint32_t>  var_to_col; ///var->col mapping. Index with VAR
        vector<uint32_t> col_to_var; ///col->var mapping. Index with COL
        uint32_t num_rows = 0;
        uint32_t num_cols = 0;

        //quick lookup
        PackedRow* cols_vals = NULL;
        PackedRow* cols_unset = NULL;
        PackedRow* tmp_col = NULL;
        PackedRow* tmp_col2 = NULL;
        void update_cols_vals_set(const Lit lit1);

        //Data to free (with delete[] x)
        vector<int64_t*> tofree;
    };
#endif
    
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

    class solver : public euf::th_solver {
        friend class xor_matrix_finder;


        euf::solver* m_ctx = nullptr;
        sat::sat_internalizer& si;
        
        unsigned            m_num_scopes = 0;
        
        sat::literal_vector  m_prop_queue;
        unsigned_vector      m_prop_queue_lim;
        unsigned             m_prop_queue_head = 0;

        ptr_vector<constraint> m_xorclauses;
        ptr_vector<constraint> m_xorclauses_orig;
        ptr_vector<constraint> m_xorclauses_unused;
        
        vector<unsigned> removed_xorclauses_clash_vars;
        bool detached_xor_clauses = false;
        bool xor_clauses_updated = false;

//        ptr_vector<EGaussian>       gmatrices;

    public:
        solver(euf::solver& ctx);
        solver(ast_manager& m, sat::sat_internalizer& si, euf::theory_id id);
        th_solver* clone(euf::solver& ctx) override;

        sat::literal internalize(expr* e, bool sign, bool root)  override { UNREACHABLE(); return sat::null_literal; }

        void internalize(expr* e) override { UNREACHABLE(); }

        void asserted(sat::literal l) override;
        bool unit_propagate() override;
        sat::ext_justification_idx gauss_jordan_elim(const sat::literal p, const unsigned currLevel);
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override;

        void pre_simplify() override;
        void simplify() override;

        sat::check_result check() override;
        void force_push();
        void push_core();
        void pop_core(unsigned num_scopes);
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

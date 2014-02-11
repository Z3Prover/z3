/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    simplex.h

Abstract:

    Multi-precision simplex tableau.

    - It uses code from theory_arith where applicable.

    - It is detached from the theory class and ASTs.

    - It uses non-shared mpz/mpq's avoiding global locks and operations on rationals.

    - It follows the same sparse tableau layout (no LU yet).

    - It does not include features for non-linear arithmetic.
   
    - Branch/bound/cuts is external.

Author:

    Nikolaj Bjorner (nbjorner) 2014-01-15

Notes:

--*/

#ifndef _SIMPLEX_H_
#define _SIMPLEX_H_

#include "sparse_matrix.h"
#include "mpq_inf.h"
#include "heap.h"
#include "lbool.h"
#include "uint_set.h"

namespace simplex {

    template<typename Ext>
    class simplex {

        typedef unsigned var_t;
        typedef typename Ext::eps_numeral eps_numeral;
        typedef typename Ext::numeral numeral;
        typedef typename Ext::manager manager;
        typedef typename Ext::eps_manager eps_manager;
        typedef typename Ext::scoped_numeral scoped_numeral;
        typedef _scoped_numeral<eps_manager> scoped_eps_numeral;

        typedef typename _scoped_numeral_vector<eps_manager> scoped_eps_numeral_vector;

        typedef sparse_matrix<Ext> matrix;

        struct var_lt {
            bool operator()(var_t v1, var_t v2) const { return v1 < v2; }
        };
        typedef heap<var_lt> var_heap;

        enum pivot_strategy_t {
            S_BLAND,
            S_GREATEST_ERROR,
            S_LEAST_ERROR,
            S_DEFAULT
        };

        struct var_info {
            unsigned    m_base2row:29;
            unsigned    m_is_base:1;
            unsigned    m_lower_valid:1;
            unsigned    m_upper_valid:1;
            eps_numeral m_value;
            eps_numeral m_lower;
            eps_numeral m_upper;
            numeral     m_base_coeff;            
            var_info():
                m_base2row(0),
                m_is_base(false),
                m_lower_valid(false),
                m_upper_valid(false)
            {}
        };

        static const var_t null_var = UINT_MAX;
        mutable matrix              M;
        unsigned                    m_max_iterations;
        volatile bool               m_cancel;
        var_heap                    m_to_patch;
        mutable manager             m;
        mutable eps_manager         em;
        vector<var_info>            m_vars;
        svector<var_t>              m_row2base;
        bool                        m_bland;
        unsigned                    m_blands_rule_threshold;
        random_gen                  m_random;
        uint_set                    m_left_basis;
        unsigned                    m_infeasible_var;

    public:
        simplex():
            m_max_iterations(UINT_MAX),
            m_cancel(false),
            m_to_patch(1024),
            m_bland(false),
            m_blands_rule_threshold(1000) {}

        typedef typename matrix::row row;
        typedef typename matrix::row_iterator row_iterator;
        typedef typename matrix::col_iterator col_iterator;

        void  ensure_var(var_t v);
        row   add_row(var_t base, unsigned num_vars, var_t const* vars, numeral const* coeffs);
        row   get_infeasible_row();
        void  del_row(row const& r);
        void  set_lower(var_t var, eps_numeral const& b);
        void  set_upper(var_t var, eps_numeral const& b);
        void  unset_lower(var_t var);
        void  unset_upper(var_t var); 
        void  set_value(var_t var, eps_numeral const& b);        
        void  set_cancel(bool f) { m_cancel = f; }
        void  set_max_iterations(unsigned m) { m_max_iterations = m; }
        lbool make_feasible();
        lbool minimize(var_t var);
        eps_numeral const& get_value(var_t v);
        void display(std::ostream& out) const;

        unsigned get_num_vars() const { return m_vars.size(); }


    private:

        var_t select_var_to_fix();
        pivot_strategy_t pivot_strategy();
        var_t select_smallest_var() { return m_to_patch.empty()?null_var:m_to_patch.erase_min(); }
        var_t select_error_var(bool least);
        // row get_infeasible_row() { }
        void check_blands_rule(var_t v, unsigned& num_repeated);
        bool make_var_feasible(var_t x_i);
        void update_and_pivot(var_t x_i, var_t x_j, numeral const& a_ij, eps_numeral const& new_value);
        void update_value(var_t v, eps_numeral const& delta);
        void update_value_core(var_t v, eps_numeral const& delta);
        void pivot(var_t x_i, var_t x_j, numeral const& a_ij);
        void move_to_bound(var_t x, bool to_lower);
        var_t select_pivot(var_t x_i, bool is_below, scoped_numeral& out_a_ij);
        var_t select_pivot_blands(var_t x_i, bool is_below, scoped_numeral& out_a_ij);
        var_t select_pivot_core(var_t x_i, bool is_below, scoped_numeral& out_a_ij);
        int get_num_non_free_dep_vars(var_t x_j, int best_so_far);

        var_t pick_var_to_leave(var_t x_j, bool inc, scoped_eps_numeral& gain, scoped_numeral& new_a_ij);


        void  select_pivot_primal(var_t v, var_t& x_i, var_t& x_j, scoped_numeral& a_ij, bool& inc);


        bool at_lower(var_t v) const;
        bool at_upper(var_t v) const;
        bool below_lower(var_t v) const;
        bool above_upper(var_t v) const;
        bool above_lower(var_t v) const;
        bool below_upper(var_t v) const;
        bool outside_bounds(var_t v) const { return below_lower(v) || above_upper(v); }
        bool is_free(var_t v) const { return !m_vars[v].m_lower_valid && !m_vars[v].m_upper_valid; }
        bool is_non_free(var_t v) const { return !is_free(v); }
        bool is_base(var_t x) const { return m_vars[x].m_is_base; }
        void add_patch(var_t v);

        bool well_formed() const;
        bool well_formed_row(row const& r) const;
        bool is_feasible() const;
    };

};

#endif

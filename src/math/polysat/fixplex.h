/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    fixplex.h

Abstract:

    Fixed-precision unsigned integer simplex tableau.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/

#pragma once

#include "math/simplex/sparse_matrix.h"
#include "util/heap.h"
#include "util/lbool.h"
#include "util/uint_set.h"

namespace polysat {

    template<typename Ext>
    class fixplex {

        typedef unsigned var_t;
        typedef typename Ext::numeral numeral;
        typedef typename Ext::scoped_numeral scoped_numeral;
        typedef typename Ext::manager manager;
        typedef simplex::sparse_matrix<Ext> matrix;
        struct var_lt {
            bool operator()(var_t v1, var_t v2) const { return v1 < v2; }
        };
        typedef heap<var_lt> var_heap;

        struct stats {
            unsigned m_num_pivots;
            unsigned m_num_infeasible;
            unsigned m_num_checks;
            stats() { reset(); }
            void reset() {
                memset(this, 0, sizeof(*this));
            }
        };

        enum pivot_strategy_t {
            S_BLAND,
            S_GREATEST_ERROR,
            S_LEAST_ERROR,
            S_DEFAULT
        };

        struct var_info {
            unsigned    m_base2row:29;
            unsigned    m_is_base:1;
            numeral     m_lo;
            numeral     m_hi;
            numeral     m_value;
            var_info():
                m_base2row(0),
                m_is_base(false)
            {}
        };

        static const var_t null_var;
        reslimit&                   m_limit;
        mutable manager             m;
        mutable matrix              M;
        unsigned                    m_max_iterations;
        var_heap                    m_to_patch;
        vector<var_info>            m_vars;
        svector<var_t>              m_row2base;
        bool                        m_bland;
        unsigned                    m_blands_rule_threshold;
        random_gen                  m_random;
        uint_set                    m_left_basis;
        unsigned                    m_infeasible_var;
        unsigned_vector             m_base_vars;
        unsigned_vector             m_to_fix_base;
        stats                       m_stats;

    public:
        fixplex(reslimit& lim):
            m_limit(lim),
            M(m),
            m_max_iterations(UINT_MAX),
            m_to_patch(1024),
            m_bland(false),
            m_blands_rule_threshold(1000) {}

        ~fixplex();

        typedef typename matrix::row row;
        typedef typename matrix::row_iterator row_iterator;
        typedef typename matrix::col_iterator col_iterator;

        var_t get_base_var(row const& r) const { return m_row2base[r.id()]; }
        numeral const& get_lo(var_t var) const { return m_vars[var].m_lo; }
        numeral const& get_hi(var_t var) const { return m_vars[var].m_hi; }
        void set_max_iterations(unsigned n) { m_max_iterations = n; }
        row_iterator row_begin(row const& r) { return M.row_begin(r); }
        row_iterator row_end(row const& r) { return M.row_end(r); }
        unsigned get_num_vars() const { return m_vars.size(); }
        void  ensure_var(var_t v);
        void  reset();
        lbool make_feasible();
        row   add_row(var_t base, unsigned num_vars, var_t const* vars, numeral const* coeffs);

#if 0
        row   get_infeasible_row();
        void  del_row(var_t base_var);
        void  set_lo(var_t var, numeral const& b);
        void  set_hi(var_t var, numeral const& b);
        bool  in_range(var_t var, numeral const& b) const;
        void  unset_lo(var_t var);
        void  unset_hi(var_t var); 
        void  set_value(var_t var, numeral const& b);        
        numeral const& get_value(var_t v);
        void display(std::ostream& out) const;
        void display_row(std::ostream& out, row const& r, bool values = true);



        void collect_statistics(::statistics & st) const;

#endif

    private:

        void gauss_jordan();
        bool gauss_jordan(row const& r);

#if 0
        void  del_row(row const& r);
        var_t select_var_to_fix();
        pivot_strategy_t pivot_strategy();
        var_t select_smallest_var() { return m_to_patch.empty()?null_var:m_to_patch.erase_min(); }
        var_t select_error_var(bool least);
        void check_blands_rule(var_t v, unsigned& num_repeated);
        bool make_var_feasible(var_t x_i);
        void update_and_pivot(var_t x_i, var_t x_j, numeral const& a_ij, numeral const& new_value);
        void update_value(var_t v, numeral const& delta);
        void update_value_core(var_t v, numeral const& delta);
        void pivot(var_t x_i, var_t x_j, numeral const& a_ij);
        void move_to_bound(var_t x, bool to_lower);
        var_t select_pivot(var_t x_i, bool is_below, scoped_numeral& out_a_ij);
        var_t select_pivot_blands(var_t x_i, bool is_below, scoped_numeral& out_a_ij);
        var_t select_pivot_core(var_t x_i, bool is_below, scoped_numeral& out_a_ij);
        int get_num_non_free_dep_vars(var_t x_j, int best_so_far);

        var_t pick_var_to_leave(var_t x_j, bool is_pos, 
                                scoped_numeral& gain, scoped_numeral& new_a_ij, bool& inc);


        void  select_pivot_primal(var_t v, var_t& x_i, var_t& x_j, scoped_numeral& a_ij, bool& inc_x_i, bool& inc_x_j);


        bool at_lower(var_t v) const;
        bool at_upper(var_t v) const;
        bool above_lower(var_t v) const;
        bool below_upper(var_t v) const;
        bool outside_bounds(var_t v) const { return below_lower(v) || above_upper(v); }
        bool is_free(var_t v) const { return m_vars[v].m_lo == m_vars[v].m_hi; }
        bool is_non_free(var_t v) const { return !is_free(v); }
        bool is_base(var_t x) const { return m_vars[x].m_is_base; }
        void add_patch(var_t v);

        bool well_formed() const;
        bool well_formed_row(row const& r) const;
        bool is_feasible() const;

#endif
    };

    struct uint64_ext {
        typedef uint64_t numeral;
        struct manager {
            void reset() {}
            void reset(numeral& n) {}
            bool is_zero(numeral const& n) const { return n == 0; }
        };
        struct scoped_numeral {
            scoped_numeral(manager& m) { n = 0; }
            numeral n;
            numeral& operator()() { return n; }
        };
    };

};


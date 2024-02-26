/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "math/lp/lp_settings.h"
#include "math/lp/static_matrix.h"
#include "util/uint_set.h"
#include "math/lp/lar_term.h"
#include "math/lp/lar_constraints.h"
#include "math/lp/hnf_cutter.h"
#include "math/lp/int_gcd_test.h"
#include "math/lp/lia_move.h"
#include "math/lp/explanation.h"

namespace lp {
class lar_solver;
class lar_core_solver;

class int_solver {
    friend struct create_cut;
    friend class gomory;
    friend class int_cube;
    friend class int_branch;
    friend class int_gcd_test;
    friend class hnf_cutter;

    class patcher {
        int_solver&         lia;
        lar_solver&         lra;
        lar_core_solver&    lrac;
    public:
        patcher(int_solver& lia);
        bool should_apply() const { return true; }
        lia_move operator()() { return patch_basic_columns(); }
        void patch_basic_column(unsigned j);
        bool try_patch_column(unsigned v, unsigned j, mpq const& delta);
        unsigned count_non_int();
    private:
        bool patch_basic_column_on_row_cell(unsigned v, row_cell<mpq> const& c);
        lia_move patch_basic_columns();
    };

    lar_solver&         lra;
    lar_core_solver&    lrac;
    int_gcd_test        m_gcd;
    patcher             m_patcher;
    unsigned            m_number_of_calls;
    lar_term            m_t;               // the term to return in the cut
    mpq                 m_k;               // the right side of the cut
    bool                m_upper;           // cut is an upper bound
    explanation         *m_ex;             // the conflict explanation
    hnf_cutter          m_hnf_cutter;
    unsigned            m_hnf_cut_period;
    unsigned_vector     m_cut_vars;        // variables that should not be selected for cuts
    
    vector<equality>       m_equalities;
public:
    int_solver(lar_solver& lp);
    
    // main function to check that the solution provided by lar_solver is valid for integral values,
    // or provide a way of how it can be adjusted.
    lia_move check(explanation *);
    lar_term const& get_term() const { return m_t; }
    mpq const& get_offset() const { return m_k; }
    bool is_upper() const { return m_upper; }
    bool is_base(unsigned j) const;
    bool is_real(unsigned j) const;
    const impq & lower_bound(unsigned j) const;
    const impq & upper_bound(unsigned j) const;
    bool column_is_int(lpvar j) const;
    const impq & get_value(unsigned j) const;
    bool at_lower(unsigned j) const;
    bool at_upper(unsigned j) const;
    void simplify(std::function<bool(unsigned)>& is_root);
    vector<equality> const& equalities() const { return m_equalities; }

private:
    // lia_move patch_nbasic_columns();
    bool get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m);
    bool is_boxed(unsigned j) const;
    bool is_free(unsigned j) const;
    bool value_is_int(unsigned j) const;
    bool is_feasible() const;
    bool column_is_int_inf(unsigned j) const;
    std::ostream& display_inf_rows(std::ostream&) const;
    bool should_find_cube();
    bool should_gomory_cut();
    bool should_hnf_cut();

    lp_settings& settings();
    const lp_settings& settings() const;
    bool at_bound(unsigned j) const;
    bool has_lower(unsigned j) const;
    bool has_upper(unsigned j) const;
    unsigned row_of_basic_column(unsigned j) const;
    bool cut_indices_are_columns() const;
        
public:
    bool is_fixed(unsigned j) const;
    std::ostream& display_column(std::ostream & out, unsigned j) const;
    u_dependency* column_upper_bound_constraint(unsigned j) const;
    u_dependency* column_lower_bound_constraint(unsigned j) const;
    bool current_solution_is_inf_on_cut() const;

    bool shift_var(unsigned j, unsigned range);
    std::ostream&  display_row_info(std::ostream & out, unsigned row_index) const;
    std::ostream & display_row(std::ostream & out, vector<row_cell<rational>> const & row) const;

private:
    unsigned random();
    bool has_inf_int() const;
public:
    bool is_term(unsigned j) const;
    unsigned column_count() const;
    lia_move hnf_cut();

    int select_int_infeasible_var();
    
};
}

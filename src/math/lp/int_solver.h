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
#include "math/lp/int_set.h"
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
    friend class create_cut;
    friend class gomory;
    friend class int_cube;
    friend class int_branch;
    friend class int_gcd_test;
    friend class hnf_cutter;

    class patcher {
        int_solver&         lia;
        lar_solver&         lra;
        lar_core_solver&    lrac;
        unsigned            m_num_nbasic_patches;
        unsigned            m_patch_cost;
        unsigned            m_next_patch;
        unsigned            m_delay;
    public:
        patcher(int_solver& lia);
        bool should_apply();
        lia_move operator()();
        void patch_nbasic_column(unsigned j);
    private:
        lia_move patch_nbasic_columns();
    };

    lar_solver&         lra;
    lar_core_solver&    lrac;
    int_gcd_test        m_gcd;
    patcher             m_patcher;
    unsigned            m_number_of_calls;
    lar_term            m_t;               // the term to return in the cut
    mpq                 m_k;               // the right side of the cut
    explanation         *m_ex;             // the conflict explanation
    bool                m_upper;           // we have a cut m_t*x <= k if m_upper is true nad m_t*x >= k otherwise
    hnf_cutter          m_hnf_cutter;
    unsigned            m_hnf_cut_period;

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
    bool column_is_int(unsigned j) const;
    const impq & get_value(unsigned j) const;
    bool at_lower(unsigned j) const;
    bool at_upper(unsigned j) const;
    
private:
    // lia_move patch_nbasic_columns();
    bool get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m);
    bool is_boxed(unsigned j) const;
    bool is_fixed(unsigned j) const;
    bool is_free(unsigned j) const;
    bool value_is_int(unsigned j) const;
    void set_value_for_nbasic_column_ignore_old_values(unsigned j, const impq & new_val);
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
    bool non_basic_columns_are_at_bounds() const;


public:
    std::ostream& display_column(std::ostream & out, unsigned j) const;
    constraint_index column_upper_bound_constraint(unsigned j) const;
    constraint_index column_lower_bound_constraint(unsigned j) const;
    bool current_solution_is_inf_on_cut() const;

    bool shift_var(unsigned j, unsigned range);
private:
    void display_row_info(std::ostream & out, unsigned row_index) const;
    unsigned random();
    bool has_inf_int() const;
public:
    bool is_term(unsigned j) const;
    unsigned column_count() const;
    bool all_columns_are_bounded() const;
    void find_feasible_solution();
    lia_move hnf_cut();
    void patch_nbasic_column(unsigned j) { m_patcher.patch_nbasic_column(j); }
  };
}

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
#include "util/lp/lp_settings.h"
#include "util/lp/static_matrix.h"
#include "util/lp/int_set.h"
#include "util/lp/lar_term.h"
#include "util/lp/lar_constraints.h"
#include "util/lp/hnf_cutter.h"
#include "util/lp/lia_move.h"
#include "util/lp/explanation.h"

namespace lp {
class lar_solver;

template <typename T, typename X>
struct lp_constraint;


class int_solver {
public:
    // fields
    lar_solver          *m_lar_solver;
    unsigned            m_number_of_calls;
    lar_term            m_t; // the term to return in the cut
    mpq                 m_k; // the right side of the cut
    explanation         m_ex; // the conflict explanation
    bool                m_upper; // we have a cut m_t*x <= k if m_upper is true nad m_t*x >= k otherwise
    hnf_cutter          m_hnf_cutter;
    // methods
    int_solver(lar_solver* lp);

    // main function to check that the solution provided by lar_solver is valid for integral values,
    // or provide a way of how it can be adjusted.
    lia_move check();
    lar_term const& get_term() const { return m_t; }
    mpq const& get_offset() const { return m_k; }
    explanation const& get_explanation() const { return m_ex; }
    bool is_upper() const { return m_upper; }

    bool is_base(unsigned j) const;
    bool is_real(unsigned j) const;
    const impq & lower_bound(unsigned j) const;
    const impq & upper_bound(unsigned j) const;
    bool is_int(unsigned j) const;
    const impq & get_value(unsigned j) const;
    bool at_lower(unsigned j) const;
    bool at_upper(unsigned j) const;
    
private:

    // how to tighten bounds for integer variables.

    bool gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i); 
    
    // gcd test
    // 5*x + 3*y + 6*z = 5
    // suppose x is fixed at 2.
    // so we have 10 + 3(y + 2z) = 5
    //             5 = -3(y + 2z)
    // this is unsolvable because 5/3 is not an integer.
    // so we create a lemma that rules out this condition.
    // 
    bool gcd_test(); // returns false in case of failure. Creates a theory lemma in case of failure.

    bool branch(const lp_constraint<mpq, mpq> & new_inequality);
    bool ext_gcd_test(const row_strip<mpq>& row,
                      mpq const & least_coeff, 
                      mpq const & lcm_den,
                      mpq const & consts);
    void fill_explanation_from_fixed_columns(const row_strip<mpq> & row);
    void add_to_explanation_from_fixed_or_boxed_column(unsigned j);
    lia_move patch_nbasic_columns();
    bool get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m);
private:
    bool is_boxed(unsigned j) const;
    bool is_fixed(unsigned j) const;
    bool is_free(unsigned j) const;
    bool value_is_int(unsigned j) const;
    void set_value_for_nbasic_column_ignore_old_values(unsigned j, const impq & new_val);
    bool non_basic_columns_are_at_bounds() const;
    bool is_feasible() const;
    bool column_is_int_inf(unsigned j) const;
    void trace_inf_rows() const;
    lia_move branch_or_sat();
    int find_any_inf_int_column_basis_first();
    int find_inf_int_base_column();
    int find_inf_int_boxed_base_column_with_smallest_range(unsigned&);
    int get_kth_inf_int(unsigned) const;
    lp_settings& settings();
    const lp_settings& settings() const;
    void branch_infeasible_int_var(unsigned);
    lia_move mk_gomory_cut(unsigned inf_col, const row_strip<mpq>& row);
    lia_move proceed_with_gomory_cut(unsigned j);
    bool is_gomory_cut_target(const row_strip<mpq>&);
    bool at_bound(unsigned j) const;
    bool has_low(unsigned j) const;
    bool has_upper(unsigned j) const;
    unsigned row_of_basic_column(unsigned j) const;

public:
    void display_column(std::ostream & out, unsigned j) const;
    constraint_index column_upper_bound_constraint(unsigned j) const;
    constraint_index column_lower_bound_constraint(unsigned j) const;
    bool current_solution_is_inf_on_cut() const;

    bool shift_var(unsigned j, unsigned range);
private:
    void display_row_info(std::ostream & out, unsigned row_index) const;
    unsigned random();
    bool has_inf_int() const;
    lia_move create_branch_on_column(int j);
public:
    bool is_term(unsigned j) const;
    bool left_branch_is_more_narrow_than_right(unsigned);
    lia_move find_cube();
    bool tighten_terms_for_cube();
    bool tighten_term_for_cube(unsigned);
    unsigned column_count() const;
    bool all_columns_are_bounded() const;
    impq get_cube_delta_for_term(const lar_term&) const;
    void find_feasible_solution();
    int find_inf_int_nbasis_column() const;
    lia_move run_gcd_test();
    lia_move gomory_cut();
    lia_move hnf_cut();
    lia_move make_hnf_cut();
    bool init_terms_for_hnf_cut();
    bool hnf_matrix_is_empty() const;
    void try_add_term_to_A_for_hnf(unsigned term_index);
    bool hnf_has_var_with_non_integral_value() const;
    bool hnf_cutter_is_full() const;
    void patch_nbasic_column(unsigned j, bool patch_only_int_vals);
  };
}

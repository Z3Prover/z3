/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#pragma once
#include "util/lp/lp_settings.h"
#include "util/lp/static_matrix.h"
#include "util/lp/iterator_on_row.h"
#include "util/lp/int_set.h"
#include "util/lp/lar_term.h"
namespace lp {
class lar_solver;
template <typename T, typename X>
struct lp_constraint;
enum class lia_move {
        ok,
        branch,
        cut,
        conflict,
        continue_with_check,
        give_up
};

struct explanation {
    vector<std::pair<mpq, constraint_index>> m_explanation;
    void push_justification(constraint_index j, const mpq& v) {
        m_explanation.push_back(std::make_pair(v, j));
    }
};

class int_solver {
public:
    // fields
    lar_solver *m_lar_solver;
    int_set m_old_values_set;
    vector<impq> m_old_values_data;
    unsigned m_branch_cut_counter;
    
    // methods
    int_solver(lar_solver* lp);
    int_set& inf_int_set();
    const int_set& inf_int_set() const;
    // main function to check that solution provided by lar_solver is valid for integral values,
    // or provide a way of how it can be adjusted.
    lia_move check(lar_term& t, mpq& k, explanation& ex);
    lia_move check_wrapper(lar_term& t, mpq& k, explanation& ex);
private:

    // how to tighten bounds for integer variables.

    bool gcd_test_for_row(static_matrix<mpq, numeric_pair<mpq>> & A, unsigned i, explanation &); 
    
    // gcd test
    // 5*x + 3*y + 6*z = 5
    // suppose x is fixed at 2.
    // so we have 10 + 3(y + 2z) = 5
    //             5 = -3(y + 2z)
    // this is unsolvable because 5/3 is not an integer.
    // so we create a lemma that rules out this condition.
    // 
    bool gcd_test(explanation & ); // returns false in case of failure. Creates a theory lemma in case of failure.

    // create goromy cuts
    // either creates a conflict or a bound.

    // branch and bound: 
    // decide what to branch and bound on
    // creates a fresh inequality.

    bool branch(const lp_constraint<mpq, mpq> & new_inequality);
    bool ext_gcd_test(iterator_on_row<mpq> & it,
                      mpq const & least_coeff, 
                      mpq const & lcm_den,
                      mpq const & consts,
                      explanation & ex);
    void fill_explanation_from_fixed_columns(iterator_on_row<mpq> & it, explanation &);
    void add_to_explanation_from_fixed_or_boxed_column(unsigned j, explanation &);
    void remove_fixed_vars_from_base();
    void patch_int_infeasible_columns();
    bool get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m);
    linear_combination_iterator<mpq> * get_column_iterator(unsigned j);
    const impq & low_bound(unsigned j) const;
    const impq & upper_bound(unsigned j) const;
    bool is_int(unsigned j) const;
    bool is_real(unsigned j) const;
    bool is_base(unsigned j) const;
    bool is_boxed(unsigned j) const;
    bool is_fixed(unsigned j) const;
    bool is_free(unsigned j) const;
    bool value_is_int(unsigned j) const;
    void set_value_for_nbasic_column(unsigned j, const impq & new_val);
    void set_value_for_nbasic_column_ignore_old_values(unsigned j, const impq & new_val);
    void fix_non_base_columns();
    void failed();
    bool is_feasible() const;
    const impq & get_value(unsigned j) const;
    void display_column(std::ostream & out, unsigned j) const;
    bool inf_int_set_is_correct() const;
    void update_column_in_int_inf_set(unsigned j);
    bool column_is_int_inf(unsigned j) const;
    void trace_inf_rows() const;
    int find_inf_int_base_column();
    int find_inf_int_boxed_base_column_with_smallest_range();
    lp_settings& settings();
    bool move_non_base_vars_to_bounds();
    void branch_infeasible_int_var(unsigned);
    lia_move mk_gomory_cut(lar_term& t, mpq& k,explanation & ex, unsigned inf_col, linear_combination_iterator<mpq>& iter);
    lia_move report_conflict_from_gomory_cut(mpq & k);
    void adjust_term_and_k_for_some_ints_case_gomory(lar_term& t, mpq& k, mpq& lcm_den);
	void init_check_data();
    bool constrain_free_vars(linear_combination_iterator<mpq> *  r);
    lia_move proceed_with_gomory_cut(lar_term& t, mpq& k, explanation& ex, unsigned j);
    int find_free_var_in_gomory_row(linear_combination_iterator<mpq>& iter);
    bool is_gomory_cut_target(linear_combination_iterator<mpq> &iter);
    bool at_bound(unsigned j) const;
    bool at_low(unsigned j) const;
    bool at_upper(unsigned j) const;
    bool has_low(unsigned j) const;
    bool has_upper(unsigned j) const;
    unsigned row_of_basic_column(unsigned j) const;
    inline static bool is_rational(const impq & n) {
        return is_zero(n.y);  
    }

    inline static
    mpq fractional_part(const impq & n) {
        lp_assert(is_rational(n));
        return n.x - floor(n.x);
    }
    void real_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term& t, explanation & ex, unsigned inf_column);
    void int_case_in_gomory_cut(const mpq & a, unsigned x_j, mpq & k, lar_term& t, explanation& ex, mpq & lcm_den, unsigned inf_column);
    constraint_index column_upper_bound_constraint(unsigned j) const;
    constraint_index column_low_bound_constraint(unsigned j) const;
    void display_row_info(std::ostream & out, unsigned row_index) const;
    void gomory_cut_adjust_t_and_k(vector<std::pair<mpq, unsigned>> & pol, lar_term & t, mpq &k, bool num_ints, mpq &lcm_den);
    bool current_solution_is_inf_on_cut(const lar_term& t, const mpq& k) const;
public:
    bool shift_var(unsigned j, unsigned range);
private:
    unsigned random();
    bool non_basic_columns_are_at_bounds() const;
    bool has_inf_int() const;
    lia_move create_branch_on_column(int j, lar_term& t, mpq& k, bool free_column) const;
public:
    void display_inf_or_int_inf_columns(std::ostream & out) const;
};
}

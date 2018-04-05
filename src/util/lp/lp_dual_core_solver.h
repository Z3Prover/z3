/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "util/lp/static_matrix.h"
#include "util/lp/lp_core_solver_base.h"
#include <string>
#include <limits>
#include <set>
#include <algorithm>
#include "util/vector.h"

namespace lp {
template <typename T, typename X>
class lp_dual_core_solver:public lp_core_solver_base<T, X> {
public:
    vector<bool> & m_can_enter_basis;
    int m_r; // the row of the leaving column
    int m_p; // leaving column; that is m_p = m_basis[m_r]
    T m_delta; // the offset of the leaving basis variable
    int m_sign_of_alpha_r; // see page 27
    T m_theta_D;
    T m_theta_P;
    int m_q;
    // todo : replace by a vector later
    std::set<unsigned> m_breakpoint_set; // it is F in "Progress in the dual simplex method ..."
    std::set<unsigned> m_flipped_boxed;
    std::set<unsigned> m_tight_set; // it is the set of all breakpoints that become tight when m_q becomes tight
    vector<T> m_a_wave;
    vector<T> m_betas; // m_betas[i] is approximately a square of the norm of the i-th row of the reverse of B
    T m_harris_tolerance;
    std::set<unsigned> m_forbidden_rows;

    lp_dual_core_solver(static_matrix<T, X> & A,
                        vector<bool> & can_enter_basis,
                        vector<X> & b, // the right side vector
                        vector<X> & x, // the number of elements in x needs to be at least as large as the number of columns in A
                        vector<unsigned> & basis,
                        vector<unsigned> & nbasis,
                        vector<int> & heading,
                        vector<T> & costs,
                        vector<column_type> & column_type_array,
                        vector<X> & low_bound_values,
                        vector<X> & upper_bound_values,
                        lp_settings & settings,
                        const column_namer & column_names):
        lp_core_solver_base<T, X>(A,
                                  b,
                                  basis,
                                  nbasis,
                                  heading,
                                  x,
                                  costs,
                                  settings,
                                  column_names,
                                  column_type_array,
                                  low_bound_values,
                                  upper_bound_values),
        m_can_enter_basis(can_enter_basis),
        m_a_wave(this->m_m()),
        m_betas(this->m_m()) {
        m_harris_tolerance = numeric_traits<T>::precise()? numeric_traits<T>::zero() : T(this->m_settings.harris_feasibility_tolerance);
        this->solve_yB(this->m_y);
        this->init_basic_part_of_basis_heading();
        fill_non_basis_with_only_able_to_enter_columns();
    }

    void init_a_wave_by_zeros();

    void fill_non_basis_with_only_able_to_enter_columns() {
        auto & nb = this->m_nbasis;
        nb.reset();
        unsigned j = this->m_n();
        while (j--) {
            if (this->m_basis_heading[j] >= 0 || !m_can_enter_basis[j]) continue;
            nb.push_back(j);
            this->m_basis_heading[j] = - static_cast<int>(nb.size());
        }
    }

    void restore_non_basis();

    bool update_basis(int entering, int leaving);

    void recalculate_xB_and_d();

    void recalculate_d();

    void init_betas();

    void adjust_xb_for_changed_xn_and_init_betas();

    void start_with_initial_basis_and_make_it_dual_feasible();

    bool done();

    T get_edge_steepness_for_low_bound(unsigned p);

    T get_edge_steepness_for_upper_bound(unsigned p);

    T pricing_for_row(unsigned i);

    void pricing_loop(unsigned number_of_rows_to_try, unsigned offset_in_rows);

    bool advance_on_known_p();

    int define_sign_of_alpha_r();

    bool can_be_breakpoint(unsigned j);

    void fill_breakpoint_set();

    void DSE_FTran();
    T get_delta();

    void restore_d();

    bool d_is_correct();

    void xb_minus_delta_p_pivot_column();

    void update_betas();

    void apply_flips();

    void snap_xN_column_to_bounds(unsigned j);

    void snap_xN_to_bounds();

    void init_beta_precisely(unsigned i);

    void init_betas_precisely();

    // step 7 of the algorithm from Progress
    bool basis_change_and_update();

    void revert_to_previous_basis();

    non_basic_column_value_position m_entering_boundary_position;
    bool update_basis_and_x_local(int entering, int leaving, X const & tt);
    void recover_leaving();

    bool problem_is_dual_feasible() const;

    bool snap_runaway_nonbasic_column(unsigned);

    bool snap_runaway_nonbasic_columns();

    unsigned get_number_of_rows_to_try_for_leaving();

    void update_a_wave(const T & del, unsigned j) {
        this->m_A.add_column_to_vector(del, j, & m_a_wave[0]);
    }

    bool delta_keeps_the_sign(int initial_delta_sign, const T & delta);

    void set_status_to_tentative_dual_unbounded_or_dual_unbounded();

    // it is positive if going from low bound to upper bound and negative if going from upper bound to low bound
    T signed_span_of_boxed(unsigned j) {
        return this->x_is_at_low_bound(j)? this->bound_span(j): - this->bound_span(j);
    }

    void add_tight_breakpoints_and_q_to_flipped_set();

    T delta_lost_on_flips_of_tight_breakpoints();

    bool tight_breakpoinst_are_all_boxed();

    T calculate_harris_delta_on_breakpoint_set();

    void fill_tight_set_on_harris_delta(const T & harris_delta );

    void find_q_on_tight_set();

    void find_q_and_tight_set();

    void erase_tight_breakpoints_and_q_from_breakpoint_set();

    bool ratio_test();

    void process_flipped();
    void update_d_and_xB();

    void calculate_beta_r_precisely();
    // see "Progress in the dual simplex method for large scale LP problems: practical dual phase 1 algorithms"

    void update_xb_after_bound_flips();

    void one_iteration();

    void solve();

    bool low_bounds_are_set() const override { return true; }
};
}

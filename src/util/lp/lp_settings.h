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
#include "util/vector.h"
#include <string>
#include <algorithm>
#include <limits>
#include <iomanip>
#include "util/lp/lp_utils.h"
#include "util/stopwatch.h"

namespace lp {
typedef unsigned var_index;
typedef unsigned constraint_index;
typedef unsigned row_index;

typedef vector<std::pair<mpq, constraint_index>> explanation_t;

enum class column_type  {
    free_column = 0,
    lower_bound = 1,
    upper_bound = 2,
    boxed = 3,
    fixed = 4
};

enum class simplex_strategy_enum {
    undecided = 3,
    tableau_rows = 0,
    tableau_costs = 1,
    lu = 2
};

std::string column_type_to_string(column_type t);

enum class lp_status {
    UNKNOWN,
    INFEASIBLE,
    TENTATIVE_UNBOUNDED,
    UNBOUNDED,
    TENTATIVE_DUAL_UNBOUNDED,
    DUAL_UNBOUNDED,
    OPTIMAL,
    FEASIBLE,
    FLOATING_POINT_ERROR,
    TIME_EXHAUSTED,
    ITERATIONS_EXHAUSTED,
    EMPTY,
    UNSTABLE,
    CANCELLED
};

// when the ratio of the vector length to domain size to is greater than the return value we switch to solve_By_for_T_indexed_only
template <typename X>
unsigned ratio_of_index_size_to_all_size() {
    if (numeric_traits<X>::precise())
        return 10;
    return 120;
}

const char* lp_status_to_string(lp_status status);

inline std::ostream& operator<<(std::ostream& out, lp_status status) {
    return out << lp_status_to_string(status);
}

lp_status lp_status_from_string(std::string status);

enum non_basic_column_value_position { at_lower_bound, at_upper_bound, at_fixed, free_of_bounds, not_at_bound };

template <typename X> bool is_epsilon_small(const X & v, const double& eps);    // forward definition

class lp_resource_limit {
public:
    virtual bool get_cancel_flag() = 0;
};

struct stats {
    unsigned m_make_feasible;
    unsigned m_total_iterations;
    unsigned m_iters_with_no_cost_growing;
    unsigned m_num_factorizations;
    unsigned m_num_of_implied_bounds;
    unsigned m_need_to_solve_inf;
    unsigned m_max_cols;
    unsigned m_max_rows;
    unsigned m_gcd_calls;
    unsigned m_gcd_conflicts;
    unsigned m_cube_calls;
    unsigned m_cube_success;
    unsigned m_patches;
    unsigned m_patches_success;
    unsigned m_hnf_cutter_calls;
    unsigned m_hnf_cuts;
    stats() { reset(); }
    void reset() { memset(this, 0, sizeof(*this)); }
};

struct lp_settings {
private:
    class default_lp_resource_limit : public lp_resource_limit {
        lp_settings& m_settings;
        stopwatch    m_sw;
    public:
        default_lp_resource_limit(lp_settings& s): m_settings(s) {
            m_sw.start();
        }
        bool get_cancel_flag() override {
            return (m_sw.get_current_seconds()  > m_settings.time_limit);
        }
    };

    default_lp_resource_limit m_default_resource_limit;
    lp_resource_limit*        m_resource_limit;
    // used for debug output
    std::ostream*             m_debug_out;
    // used for messages, for example, the computation progress messages
    std::ostream*             m_message_out;

    stats                     m_stats;
    random_gen                m_rand;

public:
    unsigned      reps_in_scaler;
    // when the absolute value of an element is less than pivot_epsilon
    // in pivoting, we treat it as a zero
    double        pivot_epsilon;
    // see Chatal, page 115
    double        positive_price_epsilon;
    // a quotation "if some choice of the entering variable leads to an eta matrix
    // whose diagonal element in the eta column is less than e2 (entering_diag_epsilon) in magnitude, the this choice is rejected ...
    double        entering_diag_epsilon;
    int           c_partial_pivoting; // this is the constant c from page 410
    unsigned      depth_of_rook_search;
    bool          using_partial_pivoting;
    // dissertation of Achim Koberstein
    // if Bx - b is different at any component more that refactor_epsilon then we refactor
    double       refactor_tolerance;
    double       pivot_tolerance;
    double       zero_tolerance;
    double       drop_tolerance;
    double       tolerance_for_artificials;
    double       can_be_taken_to_basis_tolerance;

    unsigned     percent_of_entering_to_check; // we try to find a profitable column in a percentage of the columns
    bool         use_scaling;
    double       scaling_maximum;
    double       scaling_minimum;
    double       harris_feasibility_tolerance; // page 179 of Istvan Maros
    double       ignore_epsilon_of_harris;
    unsigned     max_number_of_iterations_with_no_improvements;
    unsigned     max_total_number_of_iterations;
    double       time_limit; // the maximum time limit of the total run time in seconds
    // dual section
    double       dual_feasibility_tolerance; // // page 71 of the PhD thesis of Achim Koberstein
    double       primal_feasibility_tolerance; // page 71 of the PhD thesis of Achim Koberstein
    double       relative_primal_feasibility_tolerance; // page 71 of the PhD thesis of Achim Koberstein
    // end of dual section
    bool                   m_bound_propagation;
    bool                   presolve_with_double_solver_for_lar;
    simplex_strategy_enum  m_simplex_strategy;
    
    int              report_frequency;
    bool             print_statistics;
    unsigned         column_norms_update_frequency;
    bool             scale_with_ratio;
    double           density_threshold;
    bool             use_breakpoints_in_feasibility_search;
    unsigned         max_row_length_for_bound_propagation;
    bool             backup_costs;
    unsigned         column_number_threshold_for_using_lu_in_lar_solver;
    unsigned         m_int_gomory_cut_period;
    unsigned         m_int_find_cube_period;
private:
    unsigned         m_hnf_cut_period;
public:
    bool             m_int_run_gcd_test;
    bool             m_int_pivot_fixed_vars_from_basis;
    bool             m_int_patch_only_integer_values;
    unsigned         limit_on_rows_for_hnf_cutter;
    unsigned         limit_on_columns_for_hnf_cutter;
    bool             m_enable_hnf;


    unsigned hnf_cut_period() const { return m_hnf_cut_period; }
    void set_hnf_cut_period(unsigned period) { m_hnf_cut_period = period;  }
    unsigned random_next() { return m_rand(); }
    void set_random_seed(unsigned s) { m_rand.set_seed(s); }

    bool bound_progation() const {
        return m_bound_propagation;
    }

    bool& bound_propagation() {
        return m_bound_propagation;
    }
    
    lp_settings() : m_default_resource_limit(*this),
                    m_resource_limit(&m_default_resource_limit),
                    m_debug_out(&std::cout),
                    m_message_out(&std::cout),
                    reps_in_scaler(20),
                    pivot_epsilon(0.00000001),
                    positive_price_epsilon(1e-7),
                    entering_diag_epsilon (1e-8),
                    c_partial_pivoting (10), // this is the constant c from page 410
                    depth_of_rook_search (4),
                    using_partial_pivoting (true),
                    // dissertation of Achim Koberstein
                    // if Bx - b is different at any component more that refactor_epsilon then we refactor
                    refactor_tolerance ( 1e-4),
                    pivot_tolerance ( 1e-6),
                    zero_tolerance ( 1e-12),
                    drop_tolerance ( 1e-14),
                    tolerance_for_artificials ( 1e-4),
                    can_be_taken_to_basis_tolerance ( 0.00001),
                    percent_of_entering_to_check ( 5),// we try to find a profitable column in a percentage of the columns
                    use_scaling ( true),
                    scaling_maximum ( 1),
                    scaling_minimum ( 0.5),
                    harris_feasibility_tolerance ( 1e-7), // page 179 of Istvan Maros
                    ignore_epsilon_of_harris ( 10e-5),
                    max_number_of_iterations_with_no_improvements ( 2000000),
                    max_total_number_of_iterations ( 20000000),
                    time_limit ( std::numeric_limits<double>::max()), // the maximum time limit of the total run time in seconds
                    // dual section
                    dual_feasibility_tolerance ( 1e-7), // // page 71 of the PhD thesis of Achim Koberstein
                    primal_feasibility_tolerance ( 1e-7), // page 71 of the PhD thesis of Achim Koberstein
                    relative_primal_feasibility_tolerance ( 1e-9), // page 71 of the PhD thesis of Achim Koberstein
                    m_bound_propagation ( true),
                    presolve_with_double_solver_for_lar(true),
                    m_simplex_strategy(simplex_strategy_enum::tableau_rows),
                    report_frequency(1000),
                    print_statistics(false),
                    column_norms_update_frequency(12000),
                    scale_with_ratio(true),
                    density_threshold(0.7),
                    use_breakpoints_in_feasibility_search(false),
                    max_row_length_for_bound_propagation(300),
                    backup_costs(true),
                    column_number_threshold_for_using_lu_in_lar_solver(4000),
                    m_int_gomory_cut_period(4),
                    m_int_find_cube_period(4),
                    m_hnf_cut_period(4),
                    m_int_run_gcd_test(true),
                    m_int_pivot_fixed_vars_from_basis(false),
                    m_int_patch_only_integer_values(true),
                    limit_on_rows_for_hnf_cutter(75),
                    limit_on_columns_for_hnf_cutter(150),
                    m_enable_hnf(true)
    {}

    void set_resource_limit(lp_resource_limit& lim) { m_resource_limit = &lim; }
    bool get_cancel_flag() const { return m_resource_limit->get_cancel_flag(); }

    void set_debug_ostream(std::ostream* out) { m_debug_out = out; }
    void set_message_ostream(std::ostream* out) { m_message_out = out; }
    
    std::ostream* get_debug_ostream() { return m_debug_out; }
    std::ostream* get_message_ostream() { return m_message_out; }
    stats& st() { return m_stats; }
    stats const& st() const { return m_stats; }

    template <typename T> static bool is_eps_small_general(const T & t, const double & eps) {
        return (!numeric_traits<T>::precise())? is_epsilon_small<T>(t, eps) : numeric_traits<T>::is_zero(t);
    }

    template <typename T>
    bool abs_val_is_smaller_than_dual_feasibility_tolerance(T const & t) {
        return is_eps_small_general<T>(t, dual_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_primal_feasibility_tolerance(T const & t) {
        return is_eps_small_general<T>(t, primal_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_can_be_taken_to_basis_tolerance(T const & t) {
        return is_eps_small_general<T>(t, can_be_taken_to_basis_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_drop_tolerance(T const & t) const {
        return is_eps_small_general<T>(t, drop_tolerance);
    }


    template <typename T>
    bool abs_val_is_smaller_than_zero_tolerance(T const & t) {
        return is_eps_small_general<T>(t, zero_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_refactor_tolerance(T const & t) {
        return is_eps_small_general<T>(t, refactor_tolerance);
    }


    template <typename T>
    bool abs_val_is_smaller_than_pivot_tolerance(T const & t) {
        return is_eps_small_general<T>(t, pivot_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_harris_tolerance(T const & t) {
        return is_eps_small_general<T>(t, harris_feasibility_tolerance);
    }

    template <typename T>
    bool abs_val_is_smaller_than_ignore_epslilon_for_harris(T const & t) {
        return is_eps_small_general<T>(t, ignore_epsilon_of_harris);
    }

    template <typename T>
    bool abs_val_is_smaller_than_artificial_tolerance(T const & t) {
        return is_eps_small_general<T>(t, tolerance_for_artificials);
    }
    // the method of lar solver to use
    simplex_strategy_enum simplex_strategy() const {
        return m_simplex_strategy;
    }

    simplex_strategy_enum & simplex_strategy() {
        return m_simplex_strategy;
    }

    bool use_lu() const {
        return m_simplex_strategy == simplex_strategy_enum::lu;
    }

    bool use_tableau() const {
        return m_simplex_strategy == simplex_strategy_enum::tableau_rows ||
            m_simplex_strategy == simplex_strategy_enum::tableau_costs;
    }

    bool use_tableau_rows() const {
        return m_simplex_strategy == simplex_strategy_enum::tableau_rows;
    }
    
#ifdef Z3DEBUG
static unsigned ddd; // used for debugging    
#endif
}; // end of lp_settings class


#define LP_OUT(_settings_, _msg_) { if (_settings_.get_debug_ostream()) { *_settings_.get_debug_ostream() << _msg_; } }

template <typename T>
std::string T_to_string(const T & t) {
    std::ostringstream strs;
    strs << t;
    return strs.str();
}

inline std::string T_to_string(const numeric_pair<mpq> & t) {
    std::ostringstream strs;
    double r = (t.x + t.y / mpq(1000)).get_double();
    strs << r;
    return strs.str();
}


inline std::string T_to_string(const mpq & t) {
    std::ostringstream strs;
    strs << t;
    return strs.str();
}

template <typename T>
bool val_is_smaller_than_eps(T const & t, double const & eps) {
    if (!numeric_traits<T>::precise()) {
        return numeric_traits<T>::get_double(t) < eps;
    }
    return t <= numeric_traits<T>::zero();
}

template <typename T>
bool vectors_are_equal(T * a, vector<T>  &b, unsigned n);

template <typename T>
bool vectors_are_equal(const vector<T> & a, const buffer<T>  &b);

template <typename T>
bool vectors_are_equal(const vector<T> & a, const vector<T> &b);

template <typename T>
T abs (T const & v) { return v >= zero_of_type<T>() ? v : -v; }

template <typename X>
X max_abs_in_vector(vector<X>& t){
    X r(zero_of_type<X>());
    for (auto & v : t)
        r = std::max(abs(v) , r);
    return r;
}
inline void print_blanks(int n, std::ostream & out) {
    while (n--) {out << ' '; }
}


// after a push of the last element we ensure that the vector increases
// we also suppose that before the last push the vector was increasing
inline void ensure_increasing(vector<unsigned> & v) {
    lp_assert(v.size() > 0);
    unsigned j = v.size() - 1;
    for (; j > 0; j-- )
        if (v[j] <= v[j - 1]) {
            // swap
            unsigned t = v[j];
            v[j] = v[j-1];
            v[j-1] = t;
        } else {
            break;
        }
}

inline static bool is_rational(const impq & n) { return is_zero(n.y); }

inline static mpq fractional_part(const impq & n) {
    lp_assert(is_rational(n));
    return n.x - floor(n.x);
}
inline static mpq fractional_part(const mpq & n) {
    return n - floor(n);
}

#if Z3DEBUG
bool D();
#endif
}

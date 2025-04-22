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
#include <iostream>
#include <cstring>
#include "util/stopwatch.h"
#include "util/statistics.h"
#include "util/params.h"
#include "math/lp/lp_utils.h"
#include "math/lp/lp_types.h"

namespace lp {

enum class column_type  {
    free_column = 0,
    lower_bound = 1,
    upper_bound = 2,
    boxed = 3,
    fixed = 4
};

inline std::ostream& operator<<(std::ostream& out, column_type const& t) {
    switch (t) {
    case column_type::free_column: return out << "free";
    case column_type::lower_bound: return out << "lower";
    case column_type::upper_bound: return out << "upper";
    case column_type::boxed: return out << "boxed";
    case column_type::fixed: return out << "fixed";
    }
}

enum class simplex_strategy_enum {
    tableau_rows,
    tableau_costs
};

std::string column_type_to_string(column_type t);

enum class lp_status {
    UNKNOWN,
    INFEASIBLE,
    TENTATIVE_UNBOUNDED,
    UNBOUNDED,
    TENTATIVE_DUAL_UNBOUNDED,
    DUAL_UNBOUNDED,
    TIME_EXHAUSTED,
    EMPTY,
    UNSTABLE,
    CANCELLED,
    FEASIBLE,
    OPTIMAL
};

inline bool is_sat(lp_status st) {
    return st == lp_status::FEASIBLE || st == lp_status::OPTIMAL;
}

// when the ratio of the vector length to domain size to is greater than the return value we switch to solve_By_for_T_indexed_only
template <typename X>
unsigned ratio_of_index_size_to_all_size() {
    return 10;
}

const char* lp_status_to_string(lp_status status);

inline std::ostream& operator<<(std::ostream& out, lp_status status) {
    return out << lp_status_to_string(status);
}

lp_status lp_status_from_string(std::string status);


class lp_resource_limit {
public:
    virtual ~lp_resource_limit() = default;
    virtual bool get_cancel_flag() = 0;
};

struct statistics {
    unsigned m_make_feasible = 0;
    unsigned m_total_iterations = 0;
    unsigned m_iters_with_no_cost_growing = 0;
    unsigned m_num_factorizations = 0;
    unsigned m_num_of_implied_bounds = 0;
    unsigned m_need_to_solve_inf = 0;
    unsigned m_max_cols = 0;
    unsigned m_max_rows = 0;
    unsigned m_gcd_calls = 0;
    unsigned m_gcd_conflicts = 0;
    unsigned m_cube_calls = 0;
    unsigned m_cube_success = 0;
    unsigned m_patches = 0;
    unsigned m_patches_success = 0;
    unsigned m_hnf_cutter_calls = 0;
    unsigned m_hnf_cuts = 0;
    unsigned m_nla_calls = 0;
    unsigned m_gomory_cuts = 0;
    unsigned m_nla_add_bounds = 0;
    unsigned m_nla_propagate_bounds = 0;
    unsigned m_nla_propagate_eq = 0;
    unsigned m_nla_lemmas = 0;
    unsigned m_nra_calls = 0;
    unsigned m_nla_bounds_improvements = 0;
    unsigned m_horner_calls = 0;
    unsigned m_horner_conflicts = 0;
    unsigned m_cross_nested_forms = 0;
    unsigned m_grobner_calls = 0;
    unsigned m_grobner_conflicts = 0;
    unsigned m_offset_eqs = 0;
    unsigned m_fixed_eqs = 0;
    unsigned m_dio_calls = 0;
    unsigned m_dio_tighten_conflicts = 0;
    unsigned m_dio_rewrite_conflicts = 0;
    unsigned m_bounds_tightening_conflicts = 0;
    unsigned m_bounds_tightenings = 0;
    ::statistics m_st = {};

    void reset() {
        *this = statistics{};
    }
    void collect_statistics(::statistics& st) const {
        st.update("arith-factorizations", m_num_factorizations);
        st.update("arith-make-feasible", m_make_feasible);
        st.update("arith-max-columns", m_max_cols);
        st.update("arith-max-rows", m_max_rows);
        st.update("arith-gcd-calls", m_gcd_calls);
        st.update("arith-gcd-conflict", m_gcd_conflicts);
        st.update("arith-cube-calls", m_cube_calls);
        st.update("arith-cube-success", m_cube_success);
        st.update("arith-patches", m_patches);
        st.update("arith-patches-success", m_patches_success);
        st.update("arith-hnf-calls", m_hnf_cutter_calls);
        st.update("arith-hnf-cuts", m_hnf_cuts);
        st.update("arith-gomory-cuts", m_gomory_cuts);
        st.update("arith-horner-calls", m_horner_calls);
        st.update("arith-horner-conflicts", m_horner_conflicts);
        st.update("arith-horner-cross-nested-forms", m_cross_nested_forms);
        st.update("arith-grobner-calls", m_grobner_calls);
        st.update("arith-grobner-conflicts", m_grobner_conflicts);
        st.update("arith-offset-eqs", m_offset_eqs);
        st.update("arith-fixed-eqs", m_fixed_eqs);
        st.update("arith-nla-add-bounds", m_nla_add_bounds);
        st.update("arith-nla-propagate-bounds", m_nla_propagate_bounds);
        st.update("arith-nla-propagate-eq", m_nla_propagate_eq);
        st.update("arith-nla-lemmas", m_nla_lemmas);
        st.update("arith-nra-calls", m_nra_calls);   
        st.update("arith-bounds-improvements", m_nla_bounds_improvements);
        st.update("arith-dio-calls", m_dio_calls);
        st.update("arith-dio-tighten-conflicts", m_dio_tighten_conflicts);
        st.update("arith-dio-rewrite-conflicts", m_dio_rewrite_conflicts);
        st.update("arith-bounds-tightening-conflicts", m_bounds_tightening_conflicts);
        st.update("arith-bounds-tightenings", m_bounds_tightenings);
        st.copy(m_st);
    }
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
    lp_resource_limit*        m_resource_limit = nullptr;
    // used for debug output
    std::ostream*             m_debug_out = nullptr;
    // used for messages, for example, the computation progress messages
    std::ostream*             m_message_out = nullptr;

    statistics                m_stats;
    random_gen                m_rand;

public:
    void updt_params(params_ref const& p);
    bool enable_hnf() const { return m_enable_hnf; }
    unsigned nlsat_delay() const { return m_nlsat_delay; }
    bool int_run_gcd_test() const {
        if (!m_dio)
            return m_int_run_gcd_test;
        return m_dio_run_gcd;
    }
    void set_run_gcd_test(bool v) { m_int_run_gcd_test = v; }
    unsigned      reps_in_scaler = 20;
    int           c_partial_pivoting = 10; // this is the constant c from page 410
    unsigned      depth_of_rook_search = 4;
    bool          using_partial_pivoting = true;
    
    unsigned     percent_of_entering_to_check = 5; // we try to find a profitable column in a percentage of the columns
    bool         use_scaling = true;
    unsigned     max_number_of_iterations_with_no_improvements = 2000000;
 double       time_limit; // the maximum time limit of the total run time in seconds
    // end of dual section
    bool                   m_bound_propagation = true;
    bool                   presolve_with_double_solver_for_lar = true;
    simplex_strategy_enum  m_simplex_strategy;
    
    int              report_frequency = 1000;
    bool             print_statistics = false;
    unsigned         column_norms_update_frequency = 12000;
    bool             scale_with_ratio = true;
    unsigned         max_row_length_for_bound_propagation = 300;
    bool             backup_costs = true;
    unsigned         column_number_threshold_for_using_lu_in_lar_solver = 4000;
    unsigned         m_int_gomory_cut_period = 4;
    unsigned         m_int_find_cube_period = 4;
private:
    unsigned         m_hnf_cut_period = 4;
    bool             m_int_run_gcd_test = true;
public:
    unsigned         limit_on_rows_for_hnf_cutter = 75;
    unsigned         limit_on_columns_for_hnf_cutter = 150;
private:
    unsigned         m_nlsat_delay = 0;
    bool             m_enable_hnf = true;
    bool             m_print_external_var_name = false;
    bool             m_propagate_eqs = false;
    bool             m_dio = false;
    bool             m_dio_enable_gomory_cuts = false;
    bool             m_dio_enable_hnf_cuts = true;
    bool             m_dump_bound_lemmas = false;
    bool             m_dio_ignore_big_nums = false;
    unsigned         m_dio_calls_period = 4;
    bool             m_dio_run_gcd = true;
public:
    unsigned dio_calls_period() const { return m_dio_calls_period; }
    unsigned & dio_calls_period() { return m_dio_calls_period; }
    bool print_external_var_name() const { return m_print_external_var_name; }
    bool propagate_eqs() const { return m_propagate_eqs;}
    unsigned hnf_cut_period() const { return m_hnf_cut_period; }
    void set_hnf_cut_period(unsigned period) { m_hnf_cut_period = period;  }
    unsigned random_next() { return m_rand(); }
    unsigned random_next(unsigned u ) { return m_rand(u); }
    bool dio() { return m_dio; }
    bool & dio_enable_gomory_cuts() { return m_dio_enable_gomory_cuts; }
    bool dio_enable_gomory_cuts() const { return m_dio && m_dio_enable_gomory_cuts; }
    bool dio_run_gcd() const { return m_dio && m_dio_run_gcd; }
    bool dio_enable_hnf_cuts() const { return m_dio && m_dio_enable_hnf_cuts; }
    bool dio_ignore_big_nums() const { return m_dio_ignore_big_nums; }
    void set_random_seed(unsigned s) { m_rand.set_seed(s); }
    bool bound_progation() const { 
        return m_bound_propagation;
    }

    bool dump_bound_lemmas() { return m_dump_bound_lemmas; }
    
    bool& bound_propagation() { return m_bound_propagation; }
    
    lp_settings() : m_default_resource_limit(*this),
                    m_resource_limit(&m_default_resource_limit),
                    m_debug_out(&std::cout),
                    m_message_out(&std::cout),
                    time_limit ( std::numeric_limits<double>::max()), // the maximum time limit of the total run time in seconds
                    // dual section
                    m_simplex_strategy(simplex_strategy_enum::tableau_rows)                    
    {}

    void set_resource_limit(lp_resource_limit& lim) { m_resource_limit = &lim; }
    bool get_cancel_flag() const { return m_resource_limit->get_cancel_flag(); }

    void set_debug_ostream(std::ostream* out) { m_debug_out = out; }
    void set_message_ostream(std::ostream* out) { m_message_out = out; }
    
    std::ostream* get_debug_ostream() { return m_debug_out; }
    std::ostream* get_message_ostream() { return m_message_out; }
    statistics& stats() { return m_stats; }
    statistics const& stats() const { return m_stats; }    
    
    // the method of lar solver to use
    simplex_strategy_enum simplex_strategy() const { return m_simplex_strategy; }
    simplex_strategy_enum & simplex_strategy()  { return m_simplex_strategy; }
    bool use_tableau_rows() const { return m_simplex_strategy == simplex_strategy_enum::tableau_rows; }
    
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
bool vectors_are_equal(T * a, vector<T>  &b, unsigned n);

template <typename T>
bool vectors_are_equal(const vector<T> & a, const buffer<T>  &b);

template <typename T>
bool vectors_are_equal(const vector<T> & a, const vector<T> &b);

template <typename T, typename K >
bool vectors_are_equal_(const T & a, const K &b) {
    if (a.size() != b.size())
        return false;
    for (unsigned i = 0; i < a.size(); i++){
        if (a[i] != b[i]) {
            return false;
        }
    }
    return true;
}

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
    SASSERT(v.size() > 0);
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
    SASSERT(is_rational(n));
    return n.x - floor(n.x);
}
inline static mpq fractional_part(const mpq & n) {
    return n - floor(n);
}

#if Z3DEBUG
bool D();
#endif
}

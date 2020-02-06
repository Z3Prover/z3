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
#include <cmath>
#include <string>
#include "util/vector.h"
#include "math/lp/lp_settings.h"
namespace lp {
std::string column_type_to_string(column_type t) {
    switch (t) {
    case column_type::fixed:       return "fixed";
    case column_type::boxed:       return "boxed";
    case column_type::lower_bound:   return "lower_bound";
    case column_type::upper_bound: return "upper_bound";
    case column_type::free_column: return "free_column";
    default:  lp_unreachable();
    }
    return "unknown"; // it is unreachable
}

const char* lp_status_to_string(lp_status status) {
    switch (status) {
    case lp_status::UNKNOWN: return "UNKNOWN";
    case lp_status::INFEASIBLE: return "INFEASIBLE";
    case lp_status::UNBOUNDED: return "UNBOUNDED";
    case lp_status::TENTATIVE_DUAL_UNBOUNDED: return "TENTATIVE_DUAL_UNBOUNDED";
    case lp_status::DUAL_UNBOUNDED: return "DUAL_UNBOUNDED";
    case lp_status::OPTIMAL: return "OPTIMAL";
    case lp_status::FEASIBLE: return "FEASIBLE";
    case lp_status::FLOATING_POINT_ERROR: return "FLOATING_POINT_ERROR";
    case lp_status::TIME_EXHAUSTED: return "TIME_EXHAUSTED";
    case lp_status::ITERATIONS_EXHAUSTED: return "ITERATIONS_EXHAUSTED";
    case lp_status::EMPTY: return "EMPTY";
    case lp_status::UNSTABLE: return "UNSTABLE";
    default:
        lp_unreachable();
    }
    return "UNKNOWN";  // it is unreachable
}

lp_status lp_status_from_string(std::string status) {
    if (status == "UNKNOWN") return  lp_status::UNKNOWN;
    if (status == "INFEASIBLE") return lp_status::INFEASIBLE;
    if (status == "UNBOUNDED") return lp_status::UNBOUNDED;
    if (status == "OPTIMAL") return lp_status::OPTIMAL;
    if (status == "FEASIBLE") return lp_status::FEASIBLE;
    if (status == "FLOATING_POINT_ERROR") return lp_status::FLOATING_POINT_ERROR;
    if (status == "TIME_EXHAUSTED") return lp_status::TIME_EXHAUSTED;
    if (status == "ITERATIONS_EXHAUSTED") return lp_status::ITERATIONS_EXHAUSTED;
    if (status == "EMPTY") return lp_status::EMPTY;
    lp_unreachable();
    return lp_status::UNKNOWN; // it is unreachable
}


template <typename T>
bool vectors_are_equal(T * a, vector<T>  &b, unsigned n) {
    if (numeric_traits<T>::precise()) {
        for (unsigned i = 0; i < n; i ++){
            if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                return false;
            }
        }
    } else {
        for (unsigned i = 0; i < n; i ++){
            if (std::abs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                return false;
            }
        }
    }
    return true;
}


template <typename T>
bool vectors_are_equal(const vector<T> & a, const vector<T>  &b) {
    unsigned n = static_cast<unsigned>(a.size());
    if (n != b.size()) return false;
    if (numeric_traits<T>::precise()) {
        for (unsigned i = 0; i < n; i ++){
            if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                return false;
            }
        }
    } else {
        for (unsigned i = 0; i < n; i ++){
            double da = numeric_traits<T>::get_double(a[i]);
            double db = numeric_traits<T>::get_double(b[i]);
            double amax = std::max(fabs(da), fabs(db));
            if (amax > 1) {
                da /= amax;
                db /= amax;
            }
                
            if (fabs(da - db) > 0.000001) {
                return false;
            }
        }
    }
    return true;
}
#ifdef Z3DEBUG
unsigned lp_settings::ddd = 0;
#endif
}

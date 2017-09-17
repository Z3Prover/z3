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
#include <set>
#include "util/vector.h"
#include <unordered_map>
#include <string>
#include <algorithm>
#include "util/lp/lp_settings.h"
#include "util/lp/linear_combination_iterator.h"
// see http://research.microsoft.com/projects/z3/smt07.pdf
// The class searches for a feasible solution with as many different values of variables as it can find
namespace lp {
template <typename T> struct numeric_pair; // forward definition
class lar_core_solver; // forward definition
class random_updater {
    struct interval {
        bool upper_bound_is_set;
        numeric_pair<mpq> upper_bound;
        bool low_bound_is_set;
        numeric_pair<mpq> low_bound;
        interval() : upper_bound_is_set(false),
                     low_bound_is_set(false) {}
        
        void set_low_bound(const numeric_pair<mpq> & v) {
            if (low_bound_is_set) {
                low_bound = std::max(v, low_bound);
            } else {
                low_bound = v;
                low_bound_is_set = true;
            }
        }
        void set_upper_bound(const numeric_pair<mpq> & v) {
            if (upper_bound_is_set) {
                upper_bound = std::min(v, upper_bound);
            } else {
                upper_bound = v;
                upper_bound_is_set = true;
            }
        }
        bool is_empty() const {return
                upper_bound_is_set && low_bound_is_set && low_bound >= upper_bound;
        }

        bool low_bound_holds(const numeric_pair<mpq> & a) const {
            return low_bound_is_set == false || a >= low_bound;
        }
        bool upper_bound_holds(const numeric_pair<mpq> & a) const {
            return upper_bound_is_set == false || a <= upper_bound;
        }

        bool contains(const numeric_pair<mpq> & a) const {
            return low_bound_holds(a) && upper_bound_holds(a);
        }
        std::string lbs() { return low_bound_is_set ? T_to_string(low_bound):std::string("inf");}
        std::string rbs() { return upper_bound_is_set? T_to_string(upper_bound):std::string("inf");}
        std::string to_str() { return std::string("[")+ lbs() + ", " + rbs() + "]";}
    };
    std::set<var_index> m_var_set;
    lar_core_solver & m_core_solver;
    unsigned range;
    linear_combination_iterator<mpq>* m_column_j; // the actual column
    interval find_shift_interval(unsigned j);
    interval get_interval_of_non_basic_var(unsigned j);
    void add_column_to_sets(unsigned j);
    void random_shift_var(unsigned j);
    std::unordered_map<numeric_pair<mpq>, unsigned> m_values; // it maps a value to the number of time it occurs
    void diminish_interval_to_leave_basic_vars_feasible(numeric_pair<mpq> &nb_x, interval & inter);
    void shift_var(unsigned j, interval & r);
    void diminish_interval_for_basic_var(numeric_pair<mpq> &nb_x, unsigned j, mpq & a, interval & r);
    numeric_pair<mpq> get_random_from_interval(interval & r);
    void add_value(numeric_pair<mpq>& v);
    void remove_value(numeric_pair<mpq> & v);
  public:
    random_updater(lar_core_solver & core_solver, const vector<unsigned> & column_list);
    void update();
};
}

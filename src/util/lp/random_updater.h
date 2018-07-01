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
// see http://research.microsoft.com/projects/z3/smt07.pdf
// The class searches for a feasible solution with as many different values of variables as it can find
namespace lp {
template <typename T> struct numeric_pair; // forward definition
class lar_solver; // forward definition
class random_updater {
    std::set<var_index> m_var_set;
    lar_solver & m_lar_solver;
    unsigned m_range;
    void add_column_to_sets(unsigned j);
    bool random_shift_var(unsigned j);
    std::unordered_map<numeric_pair<mpq>, unsigned> m_values; // it maps a value to the number of time it occurs
    bool shift_var(unsigned j);
    void add_value(const numeric_pair<mpq>& v);
    void remove_value(const numeric_pair<mpq> & v);
  public:
    random_updater(lar_solver & solver, const vector<unsigned> & column_list);
    void update();
};
}

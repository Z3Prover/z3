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
#include "math/lp/lp_settings.h"
#include "math/lp/u_set.h"
// see http://research.microsoft.com/projects/z3/smt07.pdf
// The class searches for a feasible solution with as many different values of variables as it can find
namespace lp {
template <typename T> struct numeric_pair; // forward definition
class lar_solver; // forward definition
class random_updater {
    u_set           m_var_set;
    lar_solver &    m_lar_solver;
    unsigned        m_range;
    bool shift_var(unsigned j);
  public:
    random_updater(lar_solver & solver, const vector<unsigned> & column_list);
    void update();
};
}

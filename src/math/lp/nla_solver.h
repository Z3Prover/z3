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
#include "util/vector.h"
#include "math/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "nlsat/nlsat_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/monic.h"
#include "math/lp/nla_core.h"

namespace nla {

// nonlinear integer incremental linear solver
class solver {
    reslimit m_res_limit;
    core* m_core;
public:
    void add_monic(lpvar v, unsigned sz, lpvar const* vs);
    
    solver(lp::lar_solver& s);
    ~solver();
    inline core * get_core() { return m_core; } 
    void push();
    void pop(unsigned scopes);
    bool need_check();
    lbool check(vector<lemma>&);
    bool is_monic_var(lpvar) const;
    bool influences_nl_var(lpvar) const;
};
}

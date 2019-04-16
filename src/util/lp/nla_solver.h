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
#include "util/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "nlsat/nlsat_solver.h"
#include "util/lp/lar_solver.h"
#include "util/lp/monomial.h"
#include "util/lp/nla_core.h"
namespace nla {

// nonlinear integer incremental linear solver
class solver {
    core* m_core;
public:
    // returns the monomial index
    unsigned add_monomial(lp::var_index v, unsigned sz, lp::var_index const* vs);
    
    solver(lp::lar_solver& s, reslimit& lim, params_ref const& p);
    ~solver();
    inline core * get_core() { return m_core; } 
    void push();
    void pop(unsigned scopes);
    bool need_check();
    lbool check(vector<lemma>&);
};
}

/*++
Copyright (c) 2017 Microsoft Corporation

Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)

--*/
#pragma once
#include "util/vector.h"
#include "math/lp/lp_settings.h"
#include "util/rlimit.h"
#include "util/params.h"
#include "math/lp/lar_solver.h"
#include "math/lp/monic.h"
#include "math/lp/nla_settings.h"
#include "math/lp/nla_core.h"
namespace nra {
class solver;
}
namespace nla {
class core;
// nonlinear integer incremental linear solver
class solver {
    core* m_core;
public:
    void add_monic(lpvar v, unsigned sz, lpvar const* vs);    
    solver(lp::lar_solver& s, reslimit& limit);
    ~solver();
    nla_settings& settings();
    void push();
    void pop(unsigned scopes);
    bool need_check();
    lbool check(vector<lemma>&);
    bool is_monic_var(lpvar) const;
    bool influences_nl_var(lpvar) const;
    std::ostream& display(std::ostream& out) const;
    bool use_nra_model() const;
    core& get_core();
    nlsat::anum_manager& am();
    nlsat::anum const& am_value(lp::var_index v) const;
    void collect_statistics(::statistics & st);
};
}

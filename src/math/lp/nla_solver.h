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
    reslimit m_res_limit;
    core* m_core;
    nra::solver m_nra;
    bool m_use_nra_model;
    lbool run_nra(lp::explanation&);
    void set_use_nra_model(bool m) { m_use_nra_model = m; }
public:
    void add_monic(lpvar v, unsigned sz, lpvar const* vs);
    
    solver(lp::lar_solver& s);
    ~solver();
    nla_settings& settings();
    void push();
    void pop(unsigned scopes);
    bool need_check();
    lbool check(vector<lemma>&, lp::explanation& lp);
    bool is_monic_var(lpvar) const;
    bool influences_nl_var(lpvar) const;
    std::ostream& display(std::ostream& out) const;
    bool use_nra_model() const { return m_use_nra_model; }
    core& get_core() { return *m_core; }
    nlsat::anum_manager& am() { return m_nra.am(); }
    nlsat::anum const& am_value(lp::var_index v) const {
        SASSERT(use_nra_model());
        return m_nra.value(v);
    }
};
}

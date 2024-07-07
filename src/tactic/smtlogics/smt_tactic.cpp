/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_tactic.cpp

Abstract:

    Tactic that selects SMT backend.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-14


--*/
#include "params/sat_params.hpp"
#include "solver/solver2tactic.h"
#include "solver/solver.h"
#include "smt/tactic/smt_tactic_core.h"
#include "sat/tactic/sat_tactic.h"

tactic * mk_smt_tactic(ast_manager & m, params_ref const & p) {
    sat_params sp(p);
    if (sp.smt())
        return mk_solver2tactic(mk_smt2_solver(m, p));
    if (sp.euf())
        return mk_sat_tactic(m, p);
    return mk_smt_tactic_core(m, p);
}

tactic * mk_smt_tactic_using(ast_manager& m, bool auto_config, params_ref const& p) {
    sat_params sp(p);
    return sp.euf() ? mk_sat_tactic(m, p) : mk_smt_tactic_core_using(m, auto_config, p);
}

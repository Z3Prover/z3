/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_tactic_select.cpp

Abstract:

    Tactic that selects SMT backend.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-14


--*/
#include "smt/tactic/smt_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "sat/sat_params.hpp"

tactic * mk_smt_tactic_select(ast_manager & m, params_ref const & p) {
    sat_params sp(p);
    return sp.euf() ? mk_sat_tactic(m, p) : mk_smt_tactic(m, p);
}


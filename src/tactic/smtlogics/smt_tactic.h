/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_tactic.h

Abstract:

    Tactic that selects SMT backend.

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-14


--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_smt_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic * mk_smt_tactic_using(ast_manager& m, bool auto_config = true, params_ref const& p = params_ref());

Z3_ADD_TACTIC(smt, "smt", "apply a SAT based SMT solver.", mk_smt_tactic(m, p));



/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    sls_tactic.h

Abstract:

    A Stochastic Local Search (SLS) tactic 

Author:

    Christoph (cwinter) 2012-02-29

Notes:

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"
class ast_manager;
class tactic;

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_sls_smt_tactic(ast_manager & m, params_ref const & p = params_ref());

Z3_ADD_TACTIC(qfbv_sls, "qfbv-sls", "(try to) solve using stochastic local search for QF_BV.", mk_qfbv_sls_tactic(m, p));
Z3_ADD_TACTIC(sls_smt, "sls-smt", "(try to) solve SMT formulas using local search.", mk_sls_smt_tactic(m, p));


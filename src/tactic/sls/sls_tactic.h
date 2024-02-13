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
class ast_manager;
class tactic;

tactic * mk_qfbv_sls_tactic(ast_manager & m, params_ref const & p = params_ref());

tactic* mk_qfbv_new_sls_tactic(ast_manager& m, params_ref const& p = params_ref());

tactic* mk_bv_sls_tactic(ast_manager& m, params_ref const& p = params_ref());

/*
  ADD_TACTIC("qfbv-sls", "(try to) solve using stochastic local search for QF_BV.", "mk_qfbv_sls_tactic(m, p)")

  ADD_TACTIC("qfbv-new-sls", "(try to) solve using stochastic local search for QF_BV.", "mk_qfbv_new_sls_tactic(m, p)")

  ADD_TACTIC("qfbv-new-sls-core", "(try to) solve using stochastic local search for QF_BV.", "mk_bv_sls_tactic(m, p)")

*/


/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver_strategy.h

Abstract:

    Wraps a solver as an assertion_set strategy.
    **Temporary code**
    It should be deleted when we finish porting the assertion_set code to the tactic framework.

Author:

    Leonardo (leonardo) 2012-10-20

Notes:

--*/
#ifndef _SMT_SOLVER_STRATEGY_H_
#define _SMT_SOLVER_STRATEGY_H_

#include"assertion_set_strategy.h"

as_st * mk_smt_solver_core(bool candidate_models = false);
as_st * mk_smt_solver(bool auto_config = true, bool candidate_models = false);

MK_SIMPLE_ST_FACTORY(smt_solver_stf, mk_smt_solver());

#endif

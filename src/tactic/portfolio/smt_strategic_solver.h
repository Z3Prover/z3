/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_strategic_solver.h

Abstract:

    Create a strategic solver with tactic for all main logics
    used in SMT.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#ifndef _SMT_STRATEGIC_SOLVER_H_
#define _SMT_STRATEGIC_SOLVER_H_

class solver;
// Create a strategic solver for the Z3 API
solver * mk_smt_strategic_solver(bool force_tactic=false);

#endif

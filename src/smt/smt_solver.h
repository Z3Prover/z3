/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_solver.h

Abstract:

    Wraps smt::kernel as a solver for the external API and cmd_context.

Author:

    Leonardo (leonardo) 2012-10-21

Notes:
   
    This file was called default_solver.h. It was a bad name.

--*/
#ifndef _SMT_SOLVER_H_
#define _SMT_SOLVER_H_

class solver;

solver * mk_smt_solver();

#endif

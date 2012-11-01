/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    strategic_solver_cmd.h

Abstract:

    Specialization of the strategic solver that
    used cmd_context to access the assertion set.

Author:

    Leonardo (leonardo) 2012-11-01

Notes:

--*/
#ifndef _STRATEGIC_SOLVER_CMD_H_
#define _STRATEGIC_SOLVER_CMD_H_

#include"strategic_solver.h"

class cmd_context;

/**
   Specialization for the SMT 2.0 command language frontend.

   The strategic solver does not have to maintain a copy of the assertion set in the cmd_context.
*/
class strategic_solver_cmd : public strategic_solver_core {
    cmd_context &        m_ctx;
public:
    strategic_solver_cmd(cmd_context & ctx);
    virtual unsigned get_num_assertions() const;
    virtual expr * get_assertion(unsigned idx) const;
};

#endif 

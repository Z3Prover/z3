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
#include"strategic_solver_cmd.h"
#include"cmd_context.h"

strategic_solver_cmd::strategic_solver_cmd(cmd_context & ctx):
    m_ctx(ctx) {
}

unsigned strategic_solver_cmd::get_num_assertions() const {
    return static_cast<unsigned>(m_ctx.end_assertions() - m_ctx.begin_assertions());
}

expr * strategic_solver_cmd::get_assertion(unsigned idx) const {
    SASSERT(idx < get_num_assertions());
    return m_ctx.begin_assertions()[idx];
}

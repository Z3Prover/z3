/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    z3_solver_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-11.

Revision History:

--*/
#ifndef _Z3_SOLVER_PARAMS_H_
#define _Z3_SOLVER_PARAMS_H_

#include"ini_file.h"

struct z3_solver_params {
    bool     m_ast_ll_pp;
    bool     m_ast_smt_pp;
    bool     m_pre_simplify_expr;
    std::string m_smtlib_trace_path;
    std::string m_smtlib_source_info;
    std::string m_smtlib_category;

    z3_solver_params():
        m_ast_ll_pp(false),
        m_ast_smt_pp(false),
        m_pre_simplify_expr(false),
        m_smtlib_trace_path(""),
        m_smtlib_source_info(""),
        m_smtlib_category("")
    {}
    void register_params(ini_params & p);
};

#endif /* _Z3_SOLVER_PARAMS_H_ */


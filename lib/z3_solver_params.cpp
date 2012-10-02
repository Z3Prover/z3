/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    z3_solver_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-06-11.

Revision History:

--*/

#include"z3_solver_params.h"

void z3_solver_params::register_params(ini_params & p) {
    p.register_bool_param("Z3_SOLVER_LL_PP", m_ast_ll_pp, "pretty print asserted constraints using low-level printer (Z3 input format specific)");
    p.register_bool_param("Z3_SOLVER_SMT_PP", m_ast_smt_pp, "pretty print asserted constraints using SMT printer (Z3 input format specific)");
    p.register_bool_param("PRE_SIMPLIFY_EXPR", m_pre_simplify_expr, "pre-simplify expressions when created over the API (example: -x -> (* -1 x))");
    p.register_string_param("SMTLIB_TRACE_PATH", m_smtlib_trace_path, "path for converting Z3 formulas to SMTLIB benchmarks");
    p.register_string_param("SMTLIB_SOURCE_INFO", m_smtlib_source_info, "additional source info to add to SMTLIB benchmark");
    p.register_string_param("SMTLIB_CATEGORY", m_smtlib_category, "additional category info to add to SMTLIB benchmark");
}


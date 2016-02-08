/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    fpa_simplifier_plugin.cpp

Abstract:

    Simplifier for the floating-point theory

Author:

    Christoph (cwinter) 2015-01-14

--*/
#include"fpa_simplifier_plugin.h"

fpa_simplifier_plugin::fpa_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b) :
simplifier_plugin(symbol("fpa"), m),
m_util(m),
m_rw(m) {}

fpa_simplifier_plugin::~fpa_simplifier_plugin() {}

bool fpa_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();

    SASSERT(f->get_family_id() == get_family_id());

    return m_rw.mk_app_core(f, num_args, args, result) != BR_FAILED;
}

bool fpa_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    set_reduce_invoked();

    return m_rw.mk_eq_core(lhs, rhs, result) != BR_FAILED;
}


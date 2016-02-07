/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    seq_simplifier_plugin.cpp

Abstract:

    Simplifier for the theory of sequences

Author:

    Nikolaj Bjorner (nbjorner) 2016-02-05

--*/
#include"seq_simplifier_plugin.h"

seq_simplifier_plugin::seq_simplifier_plugin(ast_manager & m, basic_simplifier_plugin & b) :
simplifier_plugin(symbol("seq"), m),
m_util(m),
m_rw(m) {}

seq_simplifier_plugin::~seq_simplifier_plugin() {}

bool seq_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();

    SASSERT(f->get_family_id() == get_family_id());

    return m_rw.mk_app_core(f, num_args, args, result) != BR_FAILED;
}

bool seq_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    set_reduce_invoked();

    return m_rw.mk_eq_core(lhs, rhs, result) != BR_FAILED;
}


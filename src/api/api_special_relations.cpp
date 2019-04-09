/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    api_special_relations.cpp

Abstract:
    Basic API for Special relations

Author:

    Nikolaj Bjorner (nbjorner) 2019-03-25
    Ashutosh Gupta 2016

Revision History:

--*/

#include <iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/ast_pp.h"
#include "ast/special_relations_decl_plugin.h"

extern "C" {


#define MK_TERN(NAME, FID)                                              \
    Z3_ast Z3_API NAME(Z3_context c, unsigned index, Z3_ast a, Z3_ast b) { \
    LOG_ ##NAME(c, index, a, b);                                        \
    Z3_TRY;                                                             \
    expr* args[2] = { to_expr(a), to_expr(b) };                         \
    parameter p(index);                                                 \
    ast* a = mk_c(c)->m().mk_app(mk_c(c)->get_special_relations_fid(), FID, 1, &p, 2, args); \
    mk_c(c)->save_ast_trail(a);                                         \
    RETURN_Z3(of_ast(a));                                               \
    Z3_CATCH_RETURN(nullptr);                                           \
}

    MK_TERN(Z3_mk_linear_order, OP_SPECIAL_RELATION_LO);
    MK_TERN(Z3_mk_partial_order, OP_SPECIAL_RELATION_PO);
    MK_TERN(Z3_mk_piecewise_linear_order, OP_SPECIAL_RELATION_PLO);
    MK_TERN(Z3_mk_tree_order, OP_SPECIAL_RELATION_TO);


#define MK_DECL(NAME, FID)                                      \
    Z3_func_decl Z3_API NAME(Z3_context c,Z3_func_decl f) {     \
    Z3_TRY;                                                     \
    LOG_ ##NAME(c, f);                                          \
    RESET_ERROR_CODE();                                         \
    ast_manager & m = mk_c(c)->m();                             \
    func_decl* _f      = to_func_decl(f);                       \
    parameter param(_f);                                                \
    sort* domain[2] = { _f->get_domain(0), _f->get_domain(1) };         \
    func_decl * d = m.mk_func_decl(mk_c(c)->get_special_relations_fid(), FID, 1, &param, 2, domain); \
    mk_c(c)->save_ast_trail(d);                                         \
    RETURN_Z3(of_func_decl(d));                                         \
    Z3_CATCH_RETURN(nullptr);                                           \
}

    MK_DECL(Z3_mk_transitive_closure, OP_SPECIAL_RELATION_TC);
    MK_DECL(Z3_mk_transitive_reflexive_closure, OP_SPECIAL_RELATION_TRC);
};

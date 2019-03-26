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

#if 0
    bool Z3_API Z3_is_sr_lo(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_is_sr_lo(c, s);
        RESET_ERROR_CODE();
        RETURN_Z3(mk_c(c)->sr_util().is_lo( to_expr(s) ));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_is_sr_po(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_is_sr_po(c, s);
        RESET_ERROR_CODE();
        RETURN_Z3(mk_c(c)->sr_util().is_po( to_expr(s) ));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_is_sr_po_ao(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_is_sr_po_ao(c, s);
        RESET_ERROR_CODE();
        RETURN_Z3(mk_c(c)->sr_util().is_po_ao( to_expr(s) ));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_is_sr_plo(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_is_sr_plo(c, s);
        RESET_ERROR_CODE();
        RETURN_Z3(mk_c(c)->sr_util().is_plo( to_expr(s) ));
        Z3_CATCH_RETURN(false);
    }

    bool Z3_API Z3_is_sr_to(Z3_context c, Z3_ast s) {
        Z3_TRY;
        LOG_Z3_is_sr_to(c, s);
        RESET_ERROR_CODE();
        RETURN_Z3(mk_c(c)->sr_util().is_to( to_expr(s) ));
        Z3_CATCH_RETURN(false);
    }
#endif
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

};

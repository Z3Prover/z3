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

    MK_BINARY(Z3_mk_sr_lo , mk_c(c)->get_special_relations_fid(), OP_SPECIAL_RELATION_LO, SKIP);
    MK_BINARY(Z3_mk_sr_po , mk_c(c)->get_special_relations_fid(), OP_SPECIAL_RELATION_PO, SKIP);
    MK_BINARY(Z3_mk_sr_po_ao,mk_c(c)->get_special_relations_fid(), OP_SPECIAL_RELATION_PO_AO,SKIP);
    MK_BINARY(Z3_mk_sr_plo, mk_c(c)->get_special_relations_fid(), OP_SPECIAL_RELATION_PLO, SKIP);
    MK_BINARY(Z3_mk_sr_to , mk_c(c)->get_special_relations_fid(), OP_SPECIAL_RELATION_TO, SKIP);

};

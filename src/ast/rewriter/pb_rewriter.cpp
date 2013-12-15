/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    pb_rewriter.cpp

Abstract:

    Basic rewriting rules for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2013-14-12

Notes:

--*/

#include "pb_rewriter.h"

br_status pb_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    ast_manager& m = result.get_manager();
    rational sum(0), maxsum(0);
    for (unsigned i = 0; i < num_args; ++i) {
        if (m.is_true(args[i])) {
            sum += m_util.get_coeff(f, i);
            maxsum += m_util.get_coeff(f, i);
        }
        else if (!m.is_false(args[i])) {
            maxsum += m_util.get_coeff(f, i);            
        }
    }
    rational k = m_util.get_k(f);
    
    switch(f->get_decl_kind()) {
    case OP_AT_MOST_K:
    case OP_PB_LE:
        if (sum > k) {
            result = m.mk_false();
            return BR_DONE;
        }
        if (maxsum <= k) {
            result = m.mk_true();
            return BR_DONE;
        }
        return BR_FAILED;
    case OP_AT_LEAST_K:
    case OP_PB_GE:
        if (sum >= k) {
            result = m.mk_true();
            return BR_DONE;
        }
        if (maxsum < k) {
            result = m.mk_false();
            return BR_DONE;
        }
        return BR_FAILED;
    default:
        UNREACHABLE();
        return BR_FAILED;
    }    
}



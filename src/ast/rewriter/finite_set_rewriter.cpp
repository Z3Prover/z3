/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_rewriter.cpp

Abstract:

    Rewriting Simplification for finite sets

Author:

    GitHub Copilot Agent 2025

--*/

#include "ast/rewriter/finite_set_rewriter.h"

br_status finite_set_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == get_fid());
    
    switch (f->get_decl_kind()) {
    case OP_FINITE_SET_UNION:
        return mk_union(num_args, args, result);
    case OP_FINITE_SET_INTERSECT:
        return mk_intersect(num_args, args, result);
    case OP_FINITE_SET_DIFFERENCE:
        SASSERT(num_args == 2);
        return mk_difference(args[0], args[1], result);
    case OP_FINITE_SET_SUBSET:
        SASSERT(num_args == 2);
        return mk_subset(args[0], args[1], result);
    default:
        return BR_FAILED;
    }
}

br_status finite_set_rewriter::mk_union(unsigned num_args, expr * const * args, expr_ref & result) {
    // Handle binary case - check if both arguments are the same
    // set.union(x, x) -> x
    if (num_args == 2 && args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Additional simplifications can be added here
    // For example: set.union(x, empty) -> x
    // But for now, we keep it minimal as per requirements
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_intersect(unsigned num_args, expr * const * args, expr_ref & result) {
    // set.intersect(x, x) -> x
    if (num_args == 2 && args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_difference(expr * arg1, expr * arg2, expr_ref & result) {
    // set.difference(x, x) -> set.empty
    // Note: This simplification is currently disabled due to issues with mk_empty
    // in finite_set_decl_plugin. The mk_empty utility function expects an element_sort
    // but the plugin's mk_empty expects a finite_set_sort, causing conflicts.
    // TODO: Re-enable once finite_set_decl_plugin is fixed
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_subset(expr * arg1, expr * arg2, expr_ref & result) {
    // set.subset(x, y) -> set.intersect(x, y) = x
    expr_ref intersect(m());
    intersect = m_util.mk_intersect(arg1, arg2);
    result = m().mk_eq(intersect, arg1);
    return BR_REWRITE3;
}

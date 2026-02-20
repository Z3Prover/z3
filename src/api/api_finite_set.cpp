/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    api_finite_set.cpp

Abstract:

    API for finite sets.

Author:

    Copilot 2025-01-21

Revision History:

--*/
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_util.h"
#include "ast/ast_pp.h"

extern "C" {

    Z3_sort Z3_API Z3_mk_finite_set_sort(Z3_context c, Z3_sort elem_sort) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_sort(c, elem_sort);
        RESET_ERROR_CODE();
        parameter param(to_sort(elem_sort));
        sort* ty = mk_c(c)->m().mk_sort(mk_c(c)->fsutil().get_family_id(), FINITE_SET_SORT, 1, &param);
        mk_c(c)->save_ast_trail(ty);
        RETURN_Z3(of_sort(ty));
        Z3_CATCH_RETURN(nullptr);
    }

    bool Z3_API Z3_is_finite_set_sort(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_is_finite_set_sort(c, s);
        RESET_ERROR_CODE();
        return mk_c(c)->fsutil().is_finite_set(to_sort(s));
        Z3_CATCH_RETURN(false);
    }

    Z3_sort Z3_API Z3_get_finite_set_sort_basis(Z3_context c, Z3_sort s) {
        Z3_TRY;
        LOG_Z3_get_finite_set_sort_basis(c, s);
        RESET_ERROR_CODE();
        sort* elem_sort = nullptr;
        if (!mk_c(c)->fsutil().is_finite_set(to_sort(s), elem_sort)) {
            SET_ERROR_CODE(Z3_INVALID_ARG, "expected finite set sort");
            RETURN_Z3(nullptr);
        }
        RETURN_Z3(of_sort(elem_sort));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_empty(Z3_context c, Z3_sort set_sort) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_empty(c, set_sort);
        RESET_ERROR_CODE();
        app* a = mk_c(c)->fsutil().mk_empty(to_sort(set_sort));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_singleton(Z3_context c, Z3_ast elem) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_singleton(c, elem);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(elem, nullptr);
        app* a = mk_c(c)->fsutil().mk_singleton(to_expr(elem));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_union(Z3_context c, Z3_ast s1, Z3_ast s2) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_union(c, s1, s2);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(s1, nullptr);
        CHECK_IS_EXPR(s2, nullptr);
        app* a = mk_c(c)->fsutil().mk_union(to_expr(s1), to_expr(s2));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_intersect(Z3_context c, Z3_ast s1, Z3_ast s2) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_intersect(c, s1, s2);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(s1, nullptr);
        CHECK_IS_EXPR(s2, nullptr);
        app* a = mk_c(c)->fsutil().mk_intersect(to_expr(s1), to_expr(s2));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_difference(Z3_context c, Z3_ast s1, Z3_ast s2) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_difference(c, s1, s2);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(s1, nullptr);
        CHECK_IS_EXPR(s2, nullptr);
        app* a = mk_c(c)->fsutil().mk_difference(to_expr(s1), to_expr(s2));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_member(Z3_context c, Z3_ast elem, Z3_ast set) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_member(c, elem, set);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(elem, nullptr);
        CHECK_IS_EXPR(set, nullptr);
        app* a = mk_c(c)->fsutil().mk_in(to_expr(elem), to_expr(set));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_size(Z3_context c, Z3_ast set) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_size(c, set);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(set, nullptr);
        app* a = mk_c(c)->fsutil().mk_size(to_expr(set));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_subset(Z3_context c, Z3_ast s1, Z3_ast s2) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_subset(c, s1, s2);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(s1, nullptr);
        CHECK_IS_EXPR(s2, nullptr);
        app* a = mk_c(c)->fsutil().mk_subset(to_expr(s1), to_expr(s2));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_map(Z3_context c, Z3_ast f, Z3_ast set) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_map(c, f, set);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(f, nullptr);
        CHECK_IS_EXPR(set, nullptr);
        app* a = mk_c(c)->fsutil().mk_map(to_expr(f), to_expr(set));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_filter(Z3_context c, Z3_ast f, Z3_ast set) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_filter(c, f, set);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(f, nullptr);
        CHECK_IS_EXPR(set, nullptr);
        app* a = mk_c(c)->fsutil().mk_filter(to_expr(f), to_expr(set));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_ast Z3_API Z3_mk_finite_set_range(Z3_context c, Z3_ast low, Z3_ast high) {
        Z3_TRY;
        LOG_Z3_mk_finite_set_range(c, low, high);
        RESET_ERROR_CODE();
        CHECK_IS_EXPR(low, nullptr);
        CHECK_IS_EXPR(high, nullptr);
        app* a = mk_c(c)->fsutil().mk_range(to_expr(low), to_expr(high));
        mk_c(c)->save_ast_trail(a);
        RETURN_Z3(of_ast(a));
        Z3_CATCH_RETURN(nullptr);
    }

};

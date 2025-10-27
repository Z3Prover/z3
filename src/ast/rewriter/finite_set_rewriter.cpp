/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_rewriter.cpp

Abstract:

    Rewriting Simplification for finite sets

Author:

    Nikolaj Bjorner (nbjorner) - October 2025

--*/

#include "ast/rewriter/finite_set_rewriter.h"
#include "ast/arith_decl_plugin.h"

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
    case OP_FINITE_SET_SINGLETON:
        SASSERT(num_args == 1);
        return mk_singleton(args[0], result);
    case OP_FINITE_SET_IN:
        SASSERT(num_args == 2);
        return mk_in(args[0], args[1], result);
    case OP_FINITE_SET_SIZE:
        // Size is already in normal form, no simplifications
        return mk_size(args[0], result);
    default:
        return BR_FAILED;
    }
}

br_status finite_set_rewriter::mk_union(unsigned num_args, expr * const * args, expr_ref & result) {
    // Idempotency: set.union(x, x) -> x
    if (num_args == 2 && args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Identity: set.union(x, empty) -> x or set.union(empty, x) -> x
    if (num_args == 2) {
        if (m_util.is_empty(args[0])) {
            result = args[1];
            return BR_DONE;
        }
        if (m_util.is_empty(args[1])) {
            result = args[0];
            return BR_DONE;
        }
        
        // Absorption: set.union(x, set.intersect(x, y)) -> x
        expr* a1, *a2;
        if (m_util.is_intersect(args[1], a1, a2)) {
            if (args[0] == a1 || args[0] == a2) {
                result = args[0];
                return BR_DONE;
            }
        }
        
        // Absorption: set.union(set.intersect(x, y), x) -> x
        if (m_util.is_intersect(args[0], a1, a2)) {
            if (args[1] == a1 || args[1] == a2) {
                result = args[1];
                return BR_DONE;
            }
        }
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_intersect(unsigned num_args, expr * const * args, expr_ref & result) {
    // Idempotency: set.intersect(x, x) -> x
    if (num_args == 2 && args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Annihilation: set.intersect(x, empty) -> empty or set.intersect(empty, x) -> empty
    if (num_args == 2) {
        if (m_util.is_empty(args[0])) {
            result = args[0];
            return BR_DONE;
        }
        if (m_util.is_empty(args[1])) {
            result = args[1];
            return BR_DONE;
        }
        
        // Absorption: set.intersect(x, set.union(x, y)) -> x
        expr* a1, *a2;
        if (m_util.is_union(args[1], a1, a2)) {
            if (args[0] == a1 || args[0] == a2) {
                result = args[0];
                return BR_DONE;
            }
        }
        
        // Absorption: set.intersect(set.union(x, y), x) -> x
        if (m_util.is_union(args[0], a1, a2)) {
            if (args[1] == a1 || args[1] == a2) {
                result = args[1];
                return BR_DONE;
            }
        }
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_difference(expr * arg1, expr * arg2, expr_ref & result) {
    // set.difference(x, x) -> set.empty
    if (arg1 == arg2) {
        sort* set_sort = arg1->get_sort();
        SASSERT(m_util.is_finite_set(set_sort));
        result = m_util.mk_empty(set_sort);
        return BR_DONE;
    }
    
    // Identity: set.difference(x, empty) -> x
    if (m_util.is_empty(arg2)) {
        result = arg1;
        return BR_DONE;
    }
    
    // Annihilation: set.difference(empty, x) -> empty
    if (m_util.is_empty(arg1)) {
        result = arg1;
        return BR_DONE;
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_subset(expr * arg1, expr * arg2, expr_ref & result) {
    // set.subset(x, x) -> true
    if (arg1 == arg2) {
        result = m.mk_true();
        return BR_DONE;
    }
    
    // set.subset(empty, x) -> true
    if (m_util.is_empty(arg1)) {
        result = m.mk_true();
        return BR_DONE;
    }
    
    // set.subset(x, empty) -> x = empty
    if (m_util.is_empty(arg2)) {
        result = m.mk_eq(arg1, arg2);
        return BR_REWRITE1;
    }
    
    // General case: set.subset(x, y) -> set.intersect(x, y) = x
    expr_ref intersect(m);
    intersect = m_util.mk_intersect(arg1, arg2);
    result = m.mk_eq(intersect, arg1);
    return BR_REWRITE3;
}

br_status finite_set_rewriter::mk_singleton(expr * arg, expr_ref & result) {
    // Singleton is already in normal form, no simplifications
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_size(expr * arg, expr_ref & result) {
    arith_util a(m);
    if (m_util.is_empty(arg)) {
        // size(empty) -> 0
        result = a.mk_int(0);
        return BR_DONE;
    }
    if (m_util.is_singleton(arg)) {
        // size(singleton(x)) -> 1
        result = a.mk_int(1);
        return BR_DONE;
    }
    expr *lower, *upper;
    if (m_util.is_range(arg, lower, upper)) {
        // size(range(a, b)) -> b - a + 1
        expr_ref size_expr(m);
        size_expr = a.mk_add(a.mk_sub(upper, lower), a.mk_int(1));
        result = m.mk_ite(a.mk_gt(lower, upper), a.mk_int(0), size_expr);
        return BR_REWRITE3;
    }
    // Size is already in normal form, no simplifications
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_in(expr * elem, expr * set, expr_ref & result) {
    // set.in(x, empty) -> false
    if (m_util.is_empty(set)) {
        result = m.mk_false();
        return BR_DONE;
    }
    
    // set.in(x, singleton(y)) checks
    expr* singleton_elem;
    if (m_util.is_singleton(set, singleton_elem)) {
        // set.in(x, singleton(x)) -> true (when x is the same)
        if (elem == singleton_elem) {
            result = m.mk_true();
            return BR_DONE;
        }
        // set.in(x, singleton(y)) -> x = y (when x != y)
        result = m.mk_eq(elem, singleton_elem);
        return BR_REWRITE1;
    }
    // NB we don't rewrite (set.in x (set.union s t)) to (or (set.in x s) (set.in x t))
    // because it creates two new sub-expressions. The expression (set.union s t) could
    // be shared with other expressions so the net effect of this rewrite could be to create
    // a larger formula for the solver.
    return BR_FAILED;
}


/**
* if a, b are set expressions we can create an on-the-fly heap for their min-elements
* a, b are normalized to the form (set.union s t) or (set.empty) where 
* s is a singleton or range expression such that every element in t are above s.
* we distinguish numerical values from value expressions:
* - for numerical values we use the ordering over numerals to pick minimal ranges
* - for unique value expressions ranging over non-numerals use expression identifiers
* - for other expressions use identifiers to sort expressions, but make sure to be inconclusive
*   for set difference
* We want mk_eq_core to produce a result true/false if the arguments are both (unique) values.
* This allows to evaluate models for being well-formed conclusively.
* 
* A way to convert a set expression to a heap is as follows:
* 
* min({s}) = {s} u {}
* min({}) = {}
* min([l..u]) = [l..u] u {}
* min(s u t) = 
*   let range_s u s1 = min(s)
*   let range_t u t1 = min(t)
*   if range_s < range_t: 
*        range_s u (t u s1)
*   if range_t < range_t:
*        range_t u (s u t1)
*   if range_t n range_s != {}:
*        min(range_t, range_s) u the rest ...
*   etc.
*/

br_status finite_set_rewriter::mk_eq_core(expr* a, expr* b, expr_ref& result) {

    return BR_FAILED;
}
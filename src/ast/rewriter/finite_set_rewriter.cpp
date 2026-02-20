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
#include "ast/ast_pp.h"

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
        return mk_size(args[0], result);
    default:
        return BR_FAILED;
    }
}

br_status finite_set_rewriter::mk_union(unsigned num_args, expr * const * args, expr_ref & result) {
    VERIFY(num_args == 2);
    // Idempotency: set.union(x, x) -> x
    if (args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Identity: set.union(x, empty) -> x or set.union(empty, x) -> x
    if (u.is_empty(args[0])) {
        result = args[1];
        return BR_DONE;
    }
    if (u.is_empty(args[1])) {
        result = args[0];
        return BR_DONE;
    }

    // Absorption: set.union(x, set.intersect(x, y)) -> x
    expr *a1, *a2;
    if (u.is_intersect(args[1], a1, a2)) {
        if (args[0] == a1 || args[0] == a2) {
            result = args[0];
            return BR_DONE;
        }
    }

    // Absorption: set.union(set.intersect(x, y), x) -> x
    if (u.is_intersect(args[0], a1, a2)) {
        if (args[1] == a1 || args[1] == a2) {
            result = args[1];
            return BR_DONE;
        }
    }
    
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_intersect(unsigned num_args, expr * const * args, expr_ref & result) {
    if (num_args != 2)
        return BR_FAILED;

    // Idempotency: set.intersect(x, x) -> x
    if (args[0] == args[1]) {
        result = args[0];
        return BR_DONE;
    }
    
    // Annihilation: set.intersect(x, empty) -> empty or set.intersect(empty, x) -> empty
    if (u.is_empty(args[0])) {
        result = args[0];
        return BR_DONE;
    }
    if (u.is_empty(args[1])) {
        result = args[1];
        return BR_DONE;
    }

    // Absorption: set.intersect(x, set.union(x, y)) -> x
    expr *a1, *a2;
    if (u.is_union(args[1], a1, a2)) {
        if (args[0] == a1 || args[0] == a2) {
            result = args[0];
            return BR_DONE;
        }
    }

    // Absorption: set.intersect(set.union(x, y), x) -> x
    if (u.is_union(args[0], a1, a2)) {
        if (args[1] == a1 || args[1] == a2) {
            result = args[1];
            return BR_DONE;
        }
    }
    expr *l1, *l2, *u1, *u2;
    if (u.is_range(args[0], l1, u1) && u.is_range(args[1], l2, u2)) {
        arith_util a(m);
        auto max_l = m.mk_ite(a.mk_ge(l1, l2), l1, l2);
        auto min_u = m.mk_ite(a.mk_ge(u1, u2), u2, u1);
        result = u.mk_range(max_l, min_u);
        return BR_REWRITE_FULL;
    }
    
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_difference(expr * arg1, expr * arg2, expr_ref & result) {
    // set.difference(x, x) -> set.empty
    if (arg1 == arg2) {
        sort* set_sort = arg1->get_sort();
        SASSERT(u.is_finite_set(set_sort));
        result = u.mk_empty(set_sort);
        return BR_DONE;
    }
    
    // Identity: set.difference(x, empty) -> x
    if (u.is_empty(arg2)) {
        result = arg1;
        return BR_DONE;
    }
    
    // Annihilation: set.difference(empty, x) -> empty
    if (u.is_empty(arg1)) {
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
    if (u.is_empty(arg1)) {
        result = m.mk_true();
        return BR_DONE;
    }
    
    // set.subset(x, empty) -> x = empty
    if (u.is_empty(arg2)) {
        result = m.mk_eq(arg1, arg2);
        return BR_REWRITE1;
    }
    
    // General case: set.subset(x, y) -> set.intersect(x, y) = x
    expr_ref intersect(m);
    intersect = u.mk_intersect(arg1, arg2);
    result = m.mk_eq(intersect, arg1);
    return BR_REWRITE3;
}

br_status finite_set_rewriter::mk_singleton(expr * arg, expr_ref & result) {
    // Singleton is already in normal form, no simplifications
    return BR_FAILED;
}

br_status finite_set_rewriter::mk_size(expr * arg, expr_ref & result) {
    arith_util a(m);
    if (u.is_empty(arg)) {
        // size(empty) -> 0
        result = a.mk_int(0);
        return BR_DONE;
    }
    if (u.is_singleton(arg)) {
        // size(singleton(x)) -> 1
        result = a.mk_int(1);
        return BR_DONE;
    }
    expr *lower, *upper;
    if (u.is_range(arg, lower, upper)) {
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
    if (u.is_empty(set)) {
        result = m.mk_false();
        return BR_DONE;
    }
    
    // set.in(x, singleton(y)) checks
    expr* singleton_elem;
    if (u.is_singleton(set, singleton_elem)) {
        // set.in(x, singleton(x)) -> true (when x is the same)
        if (elem == singleton_elem) {
            result = m.mk_true();
            return BR_DONE;
        }
        // set.in(x, singleton(y)) -> x = y (when x != y)
        result = m.mk_eq(elem, singleton_elem);
        return BR_REWRITE1;
    }
    expr *lo = nullptr, *hi = nullptr;
    if (u.is_range(set, lo, hi)) {
        arith_util a(m);
        result = m.mk_and(a.mk_le(lo, elem), a.mk_le(elem, hi));
        return BR_REWRITE2;
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
*   let {x} u s1 = min(s)
*   let {y} u t1 = min(t)
*   if x = y then
*        { x } u (s1 u t1)
*   else  if x < y then 
*        {x} u (s1 u ({y} u t1)
*   else // x > y 
*        {y} u (t1 u ({x} u s1)
*   
*  Handling ranges is TBD
*  For proper range handling we have to change is_less on numeric singleton sets
*  to use the numerical value, not the expression identifier. Then the ordering
*  has to make all numeric values less than symbolic values.
*/

bool finite_set_rewriter::is_less(expr *a, expr *b) {
    return a->get_id() < b->get_id();
}

expr* finite_set_rewriter::mk_union(expr* a, expr* b) {
    if (u.is_empty(a))
        return b;
    if (u.is_empty(b))
        return a;
    if (a == b)
        return a;
    return u.mk_union(a, b);
}

expr* finite_set_rewriter::min(expr* e) {
    if (m_is_min.is_marked(e))
        return e;
    expr *a = nullptr, *b = nullptr;
    if (u.is_union(e, a, b)) {
        a = min(a);
        b = min(b);
        if (u.is_empty(a))
            return b;
        if (u.is_empty(b))
            return a;
        auto [x,a1] = get_min(a);
        auto [y,b1] = get_min(b);
        if (x == y)
            a = mk_union(x, mk_union(a1, b1));
        else if (is_less(x, y))
            a = mk_union(x, mk_union(a1, b));
        else
            a = mk_union(y, mk_union(a, b1));
        m_pinned.push_back(a);
        m_is_min.mark(a);
        return a;
    }
    if (u.is_intersect(e, a, b)) {
        if (!from_unique_values(a) || !from_unique_values(b)) {
            m_pinned.push_back(e);
            m_is_min.mark(e);
            return e;
        }
        while (true) {
            a = min(a);
            b = min(b);
            if (u.is_empty(a))
                return a;
            if (u.is_empty(b))
                return b;
            auto [x, a1] = get_min(a);
            auto [y, b1] = get_min(b);
            if (x == y) {
                a = mk_union(x, u.mk_intersect(a1, b1));
                m_pinned.push_back(a);
                m_is_min.mark(a);
                return a;
            }
            else if (is_less(x, y))
                a = a1;
            else
                b = b1;
        }
    }
    if (u.is_difference(e, a, b)) {
        if (!from_unique_values(a) || !from_unique_values(b)) {
            m_pinned.push_back(e);
            m_is_min.mark(e);
            return e;
        }
        while (true) {
            a = min(a);
            b = min(b);
            if (u.is_empty(a) || u.is_empty(b))
                return a;
            auto [x, a1] = get_min(a);
            auto [y, b1] = get_min(b);
            if (x == y) {
                a = a1;
                b = b1;
            }
            else if (is_less(x, y)) {
                a = mk_union(x, u.mk_difference(a1, b));
                m_pinned.push_back(a);
                m_is_min.mark(a);
                return a;
            }
            else {
                b = b1;
            }
        }
    }
    // set.filter, set.map don't have decompositions
    m_pinned.push_back(e);
    m_is_min.mark(e);
    return e;
}

std::pair<expr*, expr*> finite_set_rewriter::get_min(expr* a) {
    expr *x = nullptr, *y = nullptr;
    if (u.is_union(a, x, y))
        return {x, y};
    auto empty = u.mk_empty(a->get_sort());
    m_pinned.push_back(empty);
    return {a, empty};
}

br_status finite_set_rewriter::mk_eq_core(expr *a, expr *b, expr_ref &result) {
    m_is_min.reset();
    m_pinned.reset();
    bool are_unique = true;
    while (true) {
        if (a == b) {
            result = m.mk_true();
            return BR_DONE;
        }
        TRACE(finite_set, tout << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n");
        a = min(a);
        b = min(b);
        auto [x, a1] = get_min(a);
        auto [y, b1] = get_min(b);

        // only empty sets and singletons of unique values are unique.
        // ranges are not counted as unique.
        are_unique &= m.is_unique_value(x) && m.is_unique_value(y);
        a = a1;
        b = b1;
        if (x == y)
            continue;

        if (m.are_distinct(x, y) && are_unique) {
            are_unique &= from_unique_values(a);
            are_unique &= from_unique_values(b);
            if (are_unique) {
                result = m.mk_false();
                return BR_DONE;
            }
        }
        return BR_FAILED;
    }
}

bool finite_set_rewriter::from_unique_values(expr *a) {
    while (!u.is_empty(a)) {
        auto [x, a1] = get_min(min(a));
        if (!m.is_unique_value(x))
            return false;
        a = a1;
    }
    return true;
}

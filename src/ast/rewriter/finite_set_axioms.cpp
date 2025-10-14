/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_axioms.cpp

Abstract:

    This module implements axiom schemas that are invoked by saturating constraints
    with respect to the semantics of set operations.

Author:

    GitHub Copilot Agent 2025

Revision History:

--*/

#include "ast/ast.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"

// a ~ set.empty => not (x in a)
// x is an element, generate axiom that x is not in any empty set of x's type
void finite_set_axioms::in_empty_axiom(expr *x) {
    // Generate: not (x in empty_set)
    // where empty_set is the empty set of x's type
    sort* elem_sort = x->get_sort();
    expr_ref empty_set(u.mk_empty(elem_sort), m);
    expr_ref x_in_empty(u.mk_in(x, empty_set), m);
    
    expr_ref_vector clause(m);
    clause.push_back(m.mk_not(x_in_empty));
    m_add_clause(clause);
}

// a := set.union(b, c) 
// (x in a) <=> (x in b) or (x in c)
void finite_set_axioms::in_union_axiom(expr *x, expr *a) {
    expr* b = nullptr, *c = nullptr;
    if (!u.is_union(a, b, c))
        return;
    
    expr_ref_vector clause(m);
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_in_b(u.mk_in(x, b), m);
    expr_ref x_in_c(u.mk_in(x, c), m);
    
    // (x in a) => (x in b) or (x in c)
    expr_ref_vector clause1(m);
    clause1.push_back(m.mk_not(x_in_a));
    clause1.push_back(x_in_b);
    clause1.push_back(x_in_c);
    m_add_clause(clause1);
    
    // (x in b) => (x in a)
    expr_ref_vector clause2(m);
    clause2.push_back(m.mk_not(x_in_b));
    clause2.push_back(x_in_a);
    m_add_clause(clause2);
    
    // (x in c) => (x in a)
    expr_ref_vector clause3(m);
    clause3.push_back(m.mk_not(x_in_c));
    clause3.push_back(x_in_a);
    m_add_clause(clause3);
}

// a := set.intersect(b, c)
// (x in a) <=> (x in b) and (x in c)
void finite_set_axioms::in_intersect_axiom(expr *x, expr *a) {
    expr* b = nullptr, *c = nullptr;
    if (!u.is_intersect(a, b, c))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_in_b(u.mk_in(x, b), m);
    expr_ref x_in_c(u.mk_in(x, c), m);
    
    // (x in a) => (x in b)
    expr_ref_vector clause1(m);
    clause1.push_back(m.mk_not(x_in_a));
    clause1.push_back(x_in_b);
    m_add_clause(clause1);
    
    // (x in a) => (x in c)
    expr_ref_vector clause2(m);
    clause2.push_back(m.mk_not(x_in_a));
    clause2.push_back(x_in_c);
    m_add_clause(clause2);
    
    // (x in b) and (x in c) => (x in a)
    expr_ref_vector clause3(m);
    clause3.push_back(m.mk_not(x_in_b));
    clause3.push_back(m.mk_not(x_in_c));
    clause3.push_back(x_in_a);
    m_add_clause(clause3);
}

// a := set.difference(b, c)
// (x in a) <=> (x in b) and not (x in c)
void finite_set_axioms::in_difference_axiom(expr *x, expr *a) {
    expr* b = nullptr, *c = nullptr;
    if (!u.is_difference(a, b, c))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_in_b(u.mk_in(x, b), m);
    expr_ref x_in_c(u.mk_in(x, c), m);
    
    // (x in a) => (x in b)
    expr_ref_vector clause1(m);
    clause1.push_back(m.mk_not(x_in_a));
    clause1.push_back(x_in_b);
    m_add_clause(clause1);
    
    // (x in a) => not (x in c)
    expr_ref_vector clause2(m);
    clause2.push_back(m.mk_not(x_in_a));
    clause2.push_back(m.mk_not(x_in_c));
    m_add_clause(clause2);
    
    // (x in b) and not (x in c) => (x in a)
    expr_ref_vector clause3(m);
    clause3.push_back(m.mk_not(x_in_b));
    clause3.push_back(x_in_c);
    clause3.push_back(x_in_a);
    m_add_clause(clause3);
}

// a := set.singleton(b)
// (x in a) <=> (x == b)
void finite_set_axioms::in_singleton_axiom(expr *x, expr *a) {
    expr* b = nullptr;
    if (!u.is_singleton(a, b))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_eq_b(m.mk_eq(x, b), m);
    
    // (x in a) => (x == b)
    expr_ref_vector clause1(m);
    clause1.push_back(m.mk_not(x_in_a));
    clause1.push_back(x_eq_b);
    m_add_clause(clause1);
    
    // (x == b) => (x in a)
    expr_ref_vector clause2(m);
    clause2.push_back(m.mk_not(x_eq_b));
    clause2.push_back(x_in_a);
    m_add_clause(clause2);
}

// a := set.range(lo, hi)
// (x in a) <=> (lo <= x <= hi)
void finite_set_axioms::in_range_axiom(expr *x, expr *a) {
    expr* lo = nullptr, *hi = nullptr;
    if (!u.is_range(a, lo, hi))
        return;
    
    arith_util arith(m);
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref lo_le_x(arith.mk_le(lo, x), m);
    expr_ref x_le_hi(arith.mk_le(x, hi), m);
    
    // (x in a) => (lo <= x)
    expr_ref_vector clause1(m);
    clause1.push_back(m.mk_not(x_in_a));
    clause1.push_back(lo_le_x);
    m_add_clause(clause1);
    
    // (x in a) => (x <= hi)
    expr_ref_vector clause2(m);
    clause2.push_back(m.mk_not(x_in_a));
    clause2.push_back(x_le_hi);
    m_add_clause(clause2);
    
    // (lo <= x) and (x <= hi) => (x in a)
    expr_ref_vector clause3(m);
    clause3.push_back(m.mk_not(lo_le_x));
    clause3.push_back(m.mk_not(x_le_hi));
    clause3.push_back(x_in_a);
    m_add_clause(clause3);
}

// a := set.map(f, b)
// (x in a) <=> set.map_inverse(f, x, b) in b
void finite_set_axioms::in_map_axiom(expr *x, expr *a) {
    expr* f = nullptr, *b = nullptr;
    if (!u.is_map(a, f, b))
        return;
    
    // For now, we provide a placeholder implementation
    // The full implementation would require skolemization
    // to express the inverse relationship properly.
    // This would be: exists y. f(y) = x and y in b
}

// a := set.map(f, b)
// (x in b) => f(x) in a
void finite_set_axioms::in_map_image_axiom(expr *x, expr *a) {
    expr* f = nullptr, *b = nullptr;
    if (!u.is_map(a, f, b))
        return;
    
    expr_ref x_in_b(u.mk_in(x, b), m);
    
    // Apply function f to x using array select
    array_util autil(m);
    expr_ref fx(autil.mk_select(f, x), m);
    expr_ref fx_in_a(u.mk_in(fx, a), m);
    
    // (x in b) => f(x) in a
    expr_ref_vector clause(m);
    clause.push_back(m.mk_not(x_in_b));
    clause.push_back(fx_in_a);
    m_add_clause(clause);
}

// a := set.select(p, b)
// (x in a) <=> (x in b) and p(x)
void finite_set_axioms::in_select_axiom(expr *x, expr *a) {
    expr* p = nullptr, *b = nullptr;
    if (!u.is_select(a, p, b))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_in_b(u.mk_in(x, b), m);
    
    // Apply predicate p to x using array select
    array_util autil(m);
    expr_ref px(autil.mk_select(p, x), m);
    
    // (x in a) => (x in b)
    expr_ref_vector clause1(m);
    clause1.push_back(m.mk_not(x_in_a));
    clause1.push_back(x_in_b);
    m_add_clause(clause1);
    
    // (x in a) => p(x)
    expr_ref_vector clause2(m);
    clause2.push_back(m.mk_not(x_in_a));
    clause2.push_back(px);
    m_add_clause(clause2);
    
    // (x in b) and p(x) => (x in a)
    expr_ref_vector clause3(m);
    clause3.push_back(m.mk_not(x_in_b));
    clause3.push_back(m.mk_not(px));
    clause3.push_back(x_in_a);
    m_add_clause(clause3);
}

// a := set.singleton(b)
// set.size(a) = 1
void finite_set_axioms::size_singleton_axiom(expr *a) {
    expr* b = nullptr;
    if (!u.is_singleton(a, b))
        return;
    
    arith_util arith(m);
    expr_ref size_a(u.mk_size(a), m);
    expr_ref one(arith.mk_int(1), m);
    expr_ref eq(m.mk_eq(size_a, one), m);
    
    expr_ref_vector clause(m);
    clause.push_back(eq);
    m_add_clause(clause);
}

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
#include "ast/ast_pp.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"


std::ostream& operator<<(std::ostream& out, theory_axiom const& ax) {
    auto &m = ax.clause.get_manager();
    for (auto e : ax.clause)
        out << mk_pp(e, m) << " ";
    return out;
}

// a ~ set.empty => not (x in a)
// x is an element, generate axiom that x is not in any empty set of x's type
void finite_set_axioms::in_empty_axiom(expr *x) {
    // Generate: not (x in empty_set)
    // where empty_set is the empty set of x's type
    sort* elem_sort = x->get_sort();
    sort *set_sort = u.mk_finite_set_sort(elem_sort);
    expr_ref empty_set(u.mk_empty(set_sort), m);
    expr_ref x_in_empty(u.mk_in(x, empty_set), m);
    
    theory_axiom* ax = alloc(theory_axiom, m, "in-empty", x);
    ax->clause.push_back(m.mk_not(x_in_empty));
    m_add_clause(ax);
}

// a := set.union(b, c) 
// (x in a) <=> (x in b) or (x in c)
void finite_set_axioms::in_union_axiom(expr *x, expr *a) {
    expr* b = nullptr, *c = nullptr;
    if (!u.is_union(a, b, c))
        return;


    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_in_b(u.mk_in(x, b), m);
    expr_ref x_in_c(u.mk_in(x, c), m);
    
    // (x in a) => (x in b) or (x in c)
    theory_axiom *ax1 = alloc(theory_axiom, m, "in-union", x, a);
    ax1->clause.push_back(m.mk_not(x_in_a));
    ax1->clause.push_back(x_in_b);
    ax1->clause.push_back(x_in_c);
    m_add_clause(ax1);

    // (x in b) => (x in a)
    theory_axiom* ax2 = alloc(theory_axiom, m, "in-union", x, a);
    ax2->clause.push_back(m.mk_not(x_in_b));
    ax2->clause.push_back(x_in_a);
    m_add_clause(ax2);

    // (x in c) => (x in a)
    theory_axiom* ax3 = alloc(theory_axiom, m, "in-union", x, a);
    ax3->clause.push_back(m.mk_not(x_in_c));
    ax3->clause.push_back(x_in_a);
    m_add_clause(ax3);
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
    theory_axiom* ax1 = alloc(theory_axiom, m, "in-intersect", x, a);
    ax1->clause.push_back(m.mk_not(x_in_a));
    ax1->clause.push_back(x_in_b);
    m_add_clause(ax1);

    // (x in a) => (x in c)
    theory_axiom* ax2 = alloc(theory_axiom, m, "in-intersect", x, a);
    ax2->clause.push_back(m.mk_not(x_in_a));
    ax2->clause.push_back(x_in_c);
    m_add_clause(ax2);

    // (x in b) and (x in c) => (x in a)
    theory_axiom* ax3 = alloc(theory_axiom, m, "in-intersect", x, a);
    ax3->clause.push_back(m.mk_not(x_in_b));
    ax3->clause.push_back(m.mk_not(x_in_c));
    ax3->clause.push_back(x_in_a);
    m_add_clause(ax3);
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
    theory_axiom* ax1 = alloc(theory_axiom, m, "in-difference", x, a);
    ax1->clause.push_back(m.mk_not(x_in_a));
    ax1->clause.push_back(x_in_b);
    m_add_clause(ax1);
    
    // (x in a) => not (x in c)
    theory_axiom* ax2 = alloc(theory_axiom, m, "in-difference", x, a);
    ax2->clause.push_back(m.mk_not(x_in_a));
    ax2->clause.push_back(m.mk_not(x_in_c));
    m_add_clause(ax2);

    // (x in b) and not (x in c) => (x in a)
    theory_axiom* ax3 = alloc(theory_axiom, m, "in-difference", x, a);
    ax3->clause.push_back(m.mk_not(x_in_b));
    ax3->clause.push_back(x_in_c);
    ax3->clause.push_back(x_in_a);
    m_add_clause(ax3);
}

// a := set.singleton(b)
// (x in a) <=> (x == b)
void finite_set_axioms::in_singleton_axiom(expr *x, expr *a) {
    expr* b = nullptr;
    if (!u.is_singleton(a, b))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);

    theory_axiom* ax = alloc(theory_axiom, m, "in-singleton", x, a);
    if (x == b) {
        // If x and b are syntactically identical, then (x in a) is always true

        ax->clause.push_back(x_in_a);
        m_add_clause(ax);
        return;
    }

    expr_ref x_eq_b(m.mk_eq(x, b), m);
    
    // (x in a) => (x == b)
    ax->clause.push_back(m.mk_not(x_in_a));
    ax->clause.push_back(x_eq_b);
    m_add_clause(ax);
    ax = alloc(theory_axiom, m, "in-singleton", x, a);

    // (x == b) => (x in a)
    ax->clause.push_back(m.mk_not(x_eq_b));
    ax->clause.push_back(x_in_a);
    m_add_clause(ax);
}

void finite_set_axioms::in_singleton_axiom(expr* a) {
    expr *b = nullptr;
    if (!u.is_singleton(a, b))
        return;
    


    expr_ref b_in_a(u.mk_in(b, a), m);

    auto ax = alloc(theory_axiom, m, "in-singleton");
    ax->clause.push_back(b_in_a);
    m_add_clause(ax);
}



// a := set.range(lo, hi)
// (x in a) <=> (lo <= x <= hi)
void finite_set_axioms::in_range_axiom(expr *x, expr *a) {
    expr* lo = nullptr, *hi = nullptr;
    if (!u.is_range(a, lo, hi))
        return;
    
    arith_util arith(m);
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref lo_le_x(arith.mk_le(arith.mk_sub(lo, x), arith.mk_int(0)), m);
    expr_ref x_le_hi(arith.mk_le(arith.mk_sub(x, hi), arith.mk_int(0)), m);
    m_rewriter(lo_le_x);
    m_rewriter(x_le_hi);
    
    // (x in a) => (lo <= x)
    theory_axiom* ax1 = alloc(theory_axiom, m, "in-range", x, a);
    ax1->clause.push_back(m.mk_not(x_in_a));
    ax1->clause.push_back(lo_le_x);
    m_add_clause(ax1);

    // (x in a) => (x <= hi)
    theory_axiom* ax2 = alloc(theory_axiom, m, "in-range", x, a);
    ax2->clause.push_back(m.mk_not(x_in_a));
    ax2->clause.push_back(x_le_hi);
    m_add_clause(ax2);

    // (lo <= x) and (x <= hi) => (x in a)
    theory_axiom* ax3 = alloc(theory_axiom, m, "in-range", x, a);
    ax3->clause.push_back(m.mk_not(lo_le_x));
    ax3->clause.push_back(m.mk_not(x_le_hi));
    ax3->clause.push_back(x_in_a);
    m_add_clause(ax3);
}

// a := set.range(lo, hi)
// (not (set.in (- lo 1) r))
// (not (set.in (+ hi 1) r))
// (set.in lo r)
// (set.in hi r)
void finite_set_axioms::in_range_axiom(expr* r) {
    expr *lo = nullptr, *hi = nullptr;
    if (!u.is_range(r, lo, hi))
        return;
    theory_axiom* ax = alloc(theory_axiom, m, "range-bounds");
    arith_util a(m);
    expr_ref lo_le_hi(a.mk_le(a.mk_sub(lo, hi), a.mk_int(0)), m);
    m_rewriter(lo_le_hi);
    ax->clause.push_back(m.mk_not(lo_le_hi));
    ax->clause.push_back(u.mk_in(lo, r));
    m_add_clause(ax);

    ax = alloc(theory_axiom, m, "range-bounds", r);
    ax->clause.push_back(m.mk_not(lo_le_hi));
    ax->clause.push_back(u.mk_in(hi, r));
    m_add_clause(ax);

    ax = alloc(theory_axiom, m, "range-bounds", r);
    ax->clause.push_back(m.mk_not(u.mk_in(a.mk_add(hi, a.mk_int(1)), r)));
    m_add_clause(ax);

    ax = alloc(theory_axiom, m, "range-bounds", r);
    ax->clause.push_back(m.mk_not(u.mk_in(a.mk_add(lo, a.mk_int(-1)), r)));
    m_add_clause(ax);
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
    theory_axiom* ax = alloc(theory_axiom, m, "in-map-image", x, a);
    ax->clause.push_back(m.mk_not(x_in_b));
    ax->clause.push_back(fx_in_a);
    m_add_clause(ax);
}

// a := set.filter(p, b)
// (x in a) <=> (x in b) and p(x)
void finite_set_axioms::in_filter_axiom(expr *x, expr *a) {
    expr* p = nullptr, *b = nullptr;
    if (!u.is_filter(a, p, b))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);
    expr_ref x_in_b(u.mk_in(x, b), m);
    
    // Apply predicate p to x using array select
    array_util autil(m);
    expr_ref px(autil.mk_select(p, x), m);
    
    // (x in a) => (x in b)
    theory_axiom* ax1 = alloc(theory_axiom, m, "in-filter", x, a);
    ax1->clause.push_back(m.mk_not(x_in_a));
    ax1->clause.push_back(x_in_b);
    m_add_clause(ax1);

    // (x in a) => p(x)
    theory_axiom* ax2 = alloc(theory_axiom, m, "in-filter", x, a);
    ax2->clause.push_back(m.mk_not(x_in_a));
    ax2->clause.push_back(px);
    m_add_clause(ax2);

    // (x in b) and p(x) => (x in a)
    theory_axiom* ax3 = alloc(theory_axiom, m, "in-filter", x, a);
    ax3->clause.push_back(m.mk_not(x_in_b));
    ax3->clause.push_back(m.mk_not(px));
    ax3->clause.push_back(x_in_a);
    m_add_clause(ax3);
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

    theory_axiom* ax = alloc(theory_axiom, m, "size-singleton", a);
    ax->clause.push_back(eq);
    m_add_clause(ax);
}

void finite_set_axioms::subset_axiom(expr* a) {
    expr *b = nullptr, *c = nullptr;
    if (!u.is_subset(a, b, c))
        return;
    
    expr_ref intersect_bc(u.mk_intersect(b, c), m);
    expr_ref eq(m.mk_eq(intersect_bc, b), m);

    theory_axiom* ax1 = alloc(theory_axiom, m,  "subset", a);
    ax1->clause.push_back(m.mk_not(a));
    ax1->clause.push_back(eq);
    m_add_clause(ax1);

    theory_axiom* ax2 = alloc(theory_axiom, m,  "subset", a);
    ax2->clause.push_back(a);
    ax2->clause.push_back(m.mk_not(eq));
    m_add_clause(ax2);
}

void finite_set_axioms::extensionality_axiom(expr *a, expr* b) {
    // a != b => set.in (set.diff(a, b) a) != set.in (set.diff(a, b) b)
    expr_ref diff_ab(u.mk_ext(a, b), m);

    expr_ref a_eq_b(m.mk_eq(a, b), m);
    expr_ref diff_in_a(u.mk_in(diff_ab, a), m);
    expr_ref diff_in_b(u.mk_in(diff_ab, b), m);
    
    // (a != b) => (x in diff_ab != x in diff_ba)
    theory_axiom* ax = alloc(theory_axiom, m, "extensionality", a, b);
    ax->clause.push_back(a_eq_b);
    ax->clause.push_back(m.mk_not(diff_in_a));
    ax->clause.push_back(m.mk_not(diff_in_b));
    m_add_clause(ax);

    ax = alloc(theory_axiom, m, "extensionality", a, b);
    ax->clause.push_back(a_eq_b);
    ax->clause.push_back(diff_in_a);
    ax->clause.push_back(diff_in_b);
    m_add_clause(ax);
}
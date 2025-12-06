/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_axioms.cpp

Abstract:

    This module implements axiom schemas that are invoked by saturating constraints
    with respect to the semantics of set operations.

Author:

    nbjorner October 2025

--*/

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
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

void finite_set_axioms::add_unit(char const *name, expr *p1, expr *unit) {
    expr_ref _f1(unit, m);
    if (is_true(unit))
        return;
    theory_axiom *ax = alloc(theory_axiom, m, name, p1);
    ax->clause.push_back(unit);
    m_add_clause(ax);
}


bool finite_set_axioms::is_true(expr *f) {
    if (m.is_true(f))
        return true;
    if (m.is_not(f, f) && m.is_false(f))
        return true;
    return false;
}


bool finite_set_axioms::is_false(expr* f) {
    if (m.is_false(f))
        return true;
    if (m.is_not(f, f) && m.is_true(f))
        return true;
    return false;
}

void finite_set_axioms::add_binary(char const *name, expr *p1, expr *p2, expr *f1, expr *f2) {
    expr_ref _f1(f1, m), _f2(f2, m);
    if (is_true(f1) || is_true(f2))
        return;    
    theory_axiom *ax = alloc(theory_axiom, m, name, p1, p2);
    if (!is_false(f1))
        ax->clause.push_back(f1);
    if (!is_false(f2))
        ax->clause.push_back(f2);
    m_add_clause(ax);
}

void finite_set_axioms::add_ternary(char const *name, expr *p1, expr *p2, expr *f1, expr *f2, expr *f3) {
    expr_ref _f1(f1, m), _f2(f2, m), _f3(f3, m);
    if (is_true(f1) || is_true(f2) || is_true(f3))
        return;
    theory_axiom *ax = alloc(theory_axiom, m, name, p1, p2);
    if (!is_false(f1))
        ax->clause.push_back(f1);
    if (!is_false(f2))
        ax->clause.push_back(f2);
    if (!is_false(f3))
        ax->clause.push_back(f3);
    m_add_clause(ax);
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
    add_unit("in-empty", x, m.mk_not(x_in_empty));
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
    add_binary("in-union", x, a, m.mk_not(x_in_b), x_in_a);

    // (x in c) => (x in a)
    add_binary("in-union", x, a, m.mk_not(x_in_c), x_in_a);
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
    expr_ref nx_in_a(m.mk_not(x_in_a), m);
    expr_ref nx_in_b(m.mk_not(x_in_b), m);
    expr_ref nx_in_c(m.mk_not(x_in_c), m);
    
    // (x in a) => (x in b)
    add_binary("in-intersect", x, a, nx_in_a, x_in_b);

    // (x in a) => (x in c)
    add_binary("in-intersect", x, a, nx_in_a, x_in_c);

    // (x in b) and (x in c) => (x in a)
    add_ternary("in-intersect", x, a, nx_in_b, nx_in_c, x_in_a);
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
    expr_ref nx_in_a(m.mk_not(x_in_a), m);
    expr_ref nx_in_b(m.mk_not(x_in_b), m);
    expr_ref nx_in_c(m.mk_not(x_in_c), m);
    
    // (x in a) => (x in b)
    add_binary("in-difference", x, a, nx_in_a, x_in_b);
    
    // (x in a) => not (x in c)
    add_binary("in-difference", x, a, nx_in_a, nx_in_c);

    // (x in b) and not (x in c) => (x in a)
    add_ternary("in-difference", x, a, nx_in_b, x_in_c, x_in_a);
}

// a := set.singleton(b)
// (x in a) <=> (x == b)
void finite_set_axioms::in_singleton_axiom(expr *x, expr *a) {
    expr* b = nullptr;
    if (!u.is_singleton(a, b))
        return;
    
    expr_ref x_in_a(u.mk_in(x, a), m);

    if (x == b) {
        // If x and b are syntactically identical, then (x in a) is always true  
        theory_axiom* ax = alloc(theory_axiom, m, "in-singleton", x, a);     
        ax->clause.push_back(x_in_a);
        m_add_clause(ax);
        return;
    }

    expr_ref x_eq_b(m.mk_eq(x, b), m);
    
    // (x in a) => (x == b)
    add_binary("in-singleton", x, a, m.mk_not(x_in_a), x_eq_b);

    // (x == b) => (x in a)
    add_binary("in-singleton", x, a, m.mk_not(x_eq_b), x_in_a);
}

void finite_set_axioms::in_singleton_axiom(expr* a) {
    expr *b = nullptr;
    if (!u.is_singleton(a, b))
        return;    
    add_unit("in-singleton", a, u.mk_in(b, a));
}

// a := set.range(lo, hi)
// (x in a) <=> (lo <= x <= hi)
// we use the rewriter to simplify inequalitiess because the arithmetic solver
// makes some assumptions that inequalities are in normal form.
// this complicates proof checking. 
// Options are to include a proof of the rewrite within the justification
// fix the arithmetic solver to use the inequalities without rewriting (it really should)
// the same issue applies to everywhere we apply rewriting when adding theory axioms.

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
    expr_ref nx_le_hi(m.mk_not(x_le_hi), m);
    expr_ref nlo_le_x(m.mk_not(lo_le_x), m);
    
    // (x in a) => (lo <= x)
    add_binary("in-range", x, a, m.mk_not(x_in_a), lo_le_x);

    // (x in a) => (x <= hi)
    add_binary("in-range", x, a, m.mk_not(x_in_a), x_le_hi);

    // (lo <= x) and (x <= hi) => (x in a)
    add_ternary("in-range", x, a, nlo_le_x, nx_le_hi, x_in_a);
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

    arith_util a(m);
    expr_ref lo_le_hi(a.mk_le(a.mk_sub(lo, hi), a.mk_int(0)), m);
    m_rewriter(lo_le_hi);

    add_binary("range-bounds", r, nullptr, m.mk_not(lo_le_hi), u.mk_in(lo, r));
    add_binary("range-bounds", r, nullptr, m.mk_not(lo_le_hi), u.mk_in(hi, r));
    add_unit("range-bounds", r, m.mk_not(u.mk_in(a.mk_add(hi, a.mk_int(1)), r)));
    add_unit("range-bounds", r, m.mk_not(u.mk_in(a.mk_add(lo, a.mk_int(-1)), r)));
}

// a := set.map(f, b)
// (x in a) <=> set.map_inverse(f, x, b) in b
// 
void finite_set_axioms::in_map_axiom(expr *x, expr *a) {
    expr *f = nullptr, *b = nullptr;
    sort *elem_sort = nullptr;
    VERIFY(u.is_finite_set(a->get_sort(), elem_sort));
    if (x->get_sort() != elem_sort)
        return;
    if (!u.is_map(a, f, b))
        return;
    
    expr_ref inv(u.mk_map_inverse(f, x, b), m);
    expr_ref f1(u.mk_in(x, a), m);
    expr_ref f2(u.mk_in(inv, b), m);
    add_binary("map-inverse", x, a, m.mk_not(f1), f2);
    add_binary("map-inverse", x, b, f1, m.mk_not(f2));
}

// a := set.map(f, b)
// (x in b) => f(x) in a
void finite_set_axioms::in_map_image_axiom(expr *x, expr *a) {
    expr* f = nullptr, *b = nullptr;
    sort *elem_sort = nullptr;
    if (!u.is_map(a, f, b))
        return;
    VERIFY(u.is_finite_set(b->get_sort(), elem_sort));
    if (x->get_sort() != elem_sort)
        return;
    
    expr_ref x_in_b(u.mk_in(x, b), m);
    
    // Apply function f to x using array select
    array_util autil(m);
    expr_ref fx(autil.mk_select(f, x), m);
    expr_ref fx_in_a(u.mk_in(fx, a), m);
    m_rewriter(fx);
    
    // (x in b) => f(x) in a
    add_binary("in-map", x, a, m.mk_not(x_in_b), fx_in_a);
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
    m_rewriter(px);
    expr_ref npx(mk_not(m, px), m);
    
    // (x in a) => (x in b)
    add_binary("in-filter", x, a, m.mk_not(x_in_a), x_in_b);

    // (x in a) => p(x)
    add_binary("in-filter", x, a, m.mk_not(x_in_a), px);

    // (x in b) and p(x) => (x in a)
    add_ternary("in-filter", x, a, m.mk_not(x_in_b), npx, x_in_a);
}

// Auxiliary algebraic axioms to ease reasoning about set.size
// The axioms are not required for completenss for the base fragment
// as they are handled by creating semi-linear sets.
void finite_set_axioms::size_ub_axiom(expr *sz) {
    expr *b = nullptr, *e = nullptr, *x = nullptr, *y = nullptr;
    if (!u.is_size(sz, e))
        return;
    arith_util a(m);
    expr_ref ineq(m);

    if (u.is_singleton(e, b)) 
        add_unit("size", e, m.mk_eq(sz, a.mk_int(1)));    
    else if (u.is_empty(e)) 
        add_unit("size", e, m.mk_eq(sz, a.mk_int(0)));    
    else if (u.is_union(e, x, y)) {
        ineq = a.mk_le(sz, a.mk_add(u.mk_size(x), u.mk_size(y)));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
    }
    else if (u.is_intersect(e, x, y)) {        
        ineq = a.mk_le(sz, u.mk_size(x));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
        ineq = a.mk_le(sz, u.mk_size(y));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
    }
    else if (u.is_difference(e, x, y)) {
        ineq = a.mk_le(sz, u.mk_size(x));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
    }
    else if (u.is_filter(e, x, y)) {
        ineq = a.mk_le(sz, u.mk_size(y));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
    }
    else if (u.is_map(e, x, y)) {
        ineq = a.mk_le(sz, u.mk_size(y));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
    }
    else if (u.is_range(e, x, y)) {
        ineq = a.mk_eq(sz, m.mk_ite(a.mk_le(x, y), a.mk_add(a.mk_sub(y, x), a.mk_int(1)), a.mk_int(0)));
        m_rewriter(ineq);
        add_unit("size", e, ineq);
    }    
}

void finite_set_axioms::size_lb_axiom(expr* e) {
    VERIFY(u.is_size(e));
    arith_util a(m);
    expr_ref ineq(m);
    ineq = a.mk_le(a.mk_int(0), e);
    m_rewriter(ineq);
    add_unit("size", e, ineq);
}

void finite_set_axioms::subset_axiom(expr* a) {
    expr *b = nullptr, *c = nullptr;
    if (!u.is_subset(a, b, c))
        return;    
    expr_ref eq(m.mk_eq(u.mk_intersect(b, c), b), m);
    add_binary("subset", a, nullptr, m.mk_not(a), eq);
    add_binary("subset", a, nullptr, a, m.mk_not(eq));
}

void finite_set_axioms::extensionality_axiom(expr *a, expr* b) {
    // a != b => set.in (set.diff(a, b) a) != set.in (set.diff(a, b) b)
    expr_ref diff_ab(u.mk_ext(a, b), m);

    expr_ref a_eq_b(m.mk_eq(a, b), m);
    expr_ref diff_in_a(u.mk_in(diff_ab, a), m);
    expr_ref diff_in_b(u.mk_in(diff_ab, b), m);
    expr_ref ndiff_in_a(m.mk_not(diff_in_a), m);
    expr_ref ndiff_in_b(m.mk_not(diff_in_b), m);
    
    // (a != b) => (x in diff_ab != x in diff_ba) 
    add_ternary("extensionality", a, b, a_eq_b, ndiff_in_a, ndiff_in_b);
    add_ternary("extensionality", a, b, a_eq_b, diff_in_a, diff_in_b);
}
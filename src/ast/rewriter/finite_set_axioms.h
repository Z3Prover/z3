/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_axioms.h

Abstract:

    This module implements axiom schemas that are invoked by saturating constraints
    with respect to the semantics of set operations. 
       
--*/

#pragma once
#include "ast/rewriter/th_rewriter.h"

struct theory_axiom {
    expr_ref_vector   clause;
    vector<parameter> params;
    unsigned          weight = 0; // can be used to prioritize instantiation of axioms
    theory_axiom(ast_manager& m, symbol const& th): clause(m) {
        params.push_back(parameter(th));
    }
    theory_axiom(ast_manager &m, char const* rule) : clause(m) {
        params.push_back(parameter(symbol(rule)));
    }
    theory_axiom(ast_manager &m) : clause(m) {
    }

    theory_axiom(ast_manager &m, char const *rule, expr* x, expr* y = nullptr) : clause(m) {
        params.push_back(parameter(symbol(rule)));
        params.push_back(parameter(x));
        if (y)
            params.push_back(parameter(y));
    }
};

std::ostream &operator<<(std::ostream &out, theory_axiom const &ax);


class finite_set_axioms {
    ast_manager&    m;
    finite_set_util u;
    th_rewriter m_rewriter;

    std::function<void(theory_axiom *)> m_add_clause;

    void add_unit(char const* name, expr* p1, expr *e);

    void add_binary(char const *name, expr *p1, expr *p2, expr *f1, expr *f2);

    void add_ternary(char const *name, expr *p1, expr *p2, expr *f1, expr *f2, expr *f3);

    bool is_true(expr *f);

    bool is_false(expr *f);

public:

    finite_set_axioms(ast_manager &m) : m(m), u(m), m_rewriter(m) {}

    void set_add_clause(std::function<void(theory_axiom*)> &ac) {
        m_add_clause = ac;
    }

    // a ~ set.empty => not (x in a)
    void in_empty_axiom(expr *x);

    // a := set.union(b, c) 
    // (x in a) <=> (x in b) or (x in c)
    void in_union_axiom(expr *x, expr *a);

    // a := set.intersect(b, c)
    // (x in a) <=> (x in b) and (x in c)
    void in_intersect_axiom(expr *x, expr *a);
    
    // a := set.difference(b, c)
    // (x in a) <=> (x in b) and not (x in c)
    void in_difference_axiom(expr *x, expr *a);

    // a := set.singleton(b)
    // (x in a) <=> (x == b)
    void in_singleton_axiom(expr *x, expr *a);

    // a := set.singleton(b)
    // b in a
    // b-1 not in a
    // b+1 not in a
    void in_singleton_axiom(expr *a);

    // a := set.range(lo, hi)
    // (x in a) <=> (lo <= x <= hi)
    void in_range_axiom(expr *x, expr *a);

    // a := set.range(lo, hi)
    // (not (set.in (- lo 1) a))
    // (not (set.in (+ hi 1) a))
    // lo <= hi => (set.in lo a)
    // lo <= hi => (set.in hi a)
    void in_range_axiom(expr *a);

    // a := set.map(f, b)
    // (x in a) <=> set.map_inverse(f, x, b) in b
    void in_map_axiom(expr *x, expr *a);

    // a := set.map(f, b)
    // (x in b) => f(x) in a
    void in_map_image_axiom(expr *x, expr *a);

    // a := set.filter(p, b)
    // (x in a) <=> (x in b) and p(x)
    void in_filter_axiom(expr *x, expr *a);

    // a := set.subset(b, c)
    // (a) <=> (set.intersect(b, c) = b)
    void subset_axiom(expr *a);


    // set.size(empty) = 0
    // set.size(set.singleton(b)) = 1
    // set.size(a u b) <= set.size(a) + set.size(b)
    // set.size(a n b) <= min(set.size(a), set.size(b))
    // set.size(a \ b) <= set.size(a)
    // set.size(set.map(f, b)) <= set.size(b)
    // set.size(set.filter(p, b)) <= set.size(b)
    // set.size([l..u]) = if(l <= u, u - l + 1, 0)    
    void size_ub_axiom(expr *a);

    // 0 <= set.size(e)
    void size_lb_axiom(expr *e);


    // a != b => set.in (set.diff(a, b) a) != set.in (set.diff(a, b) b)
    void extensionality_axiom(expr *a, expr *b);

};
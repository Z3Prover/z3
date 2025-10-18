/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_axioms.h

Abstract:

    This module implements axiom schemas that are invoked by saturating constraints
    with respect to the semantics of set operations. 
       
--*/

struct theory_axiom {
    expr_ref_vector   clause;
    vector<parameter> params;
    unsigned          weight = 0; // can be used to prioritize instantiation of axioms
    theory_axiom(ast_manager& m, symbol const& th): clause(m) {
        params.push_back(parameter(th));
    }
    theory_axiom(ast_manager &m, symbol const &th, symbol const& rule) : clause(m) {
        params.push_back(parameter(th));
        params.push_back(parameter(rule));
    }
    theory_axiom(ast_manager &m, char const *th, char const *rule) : clause(m) {
        params.push_back(parameter(symbol(th)));
        params.push_back(parameter(symbol(rule)));
    }
    theory_axiom(ast_manager &m) : clause(m) {
    }
};

std::ostream &operator<<(std::ostream &out, theory_axiom const &ax);


class finite_set_axioms {
    ast_manager&    m;
    finite_set_util u;

    std::function<void(theory_axiom const &)> m_add_clause;

public:

    finite_set_axioms(ast_manager &m) : m(m), u(m) {}

    void set_add_clause(std::function<void(theory_axiom const &)> &ac) {
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

    // a := set.range(lo, hi)
    // (x in a) <=> (lo <= x <= hi)
    void in_range_axiom(expr *x, expr *a);

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

    // a := set.singleton(b)
    // set.size(a) = 1
    void size_singleton_axiom(expr *a);

    // a != b => set.in (set.diff(a, b) a) != set.in (set.diff(a, b) b)
    void extensionality_axiom(expr *a, expr *b);

};
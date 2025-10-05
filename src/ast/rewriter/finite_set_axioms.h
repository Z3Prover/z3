/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    finite_set_axioms.h

Abstract:
    Axiom schemas for finite sets.

    Axiom schemars for finite sets are instantiated based on the state of the
    congruence closure and existing assertions in for finite sets.
    This module implements axiom schemas that are invoked by saturating constraints
    with respect to the semantics of set operations. 

    Let v1 ~ v2 mean that v1 and v2 are congruent

    The set-based decision procedure relies on saturating with respect
    to rules of the form:
    
      x in v1 == v2, v1 ~ set.empty
    --------------------------------
       not (x in set.empty)


     x in v1 == v2, v1 ~ v3, v3 == (set.union v4 v5)
     -----------------------------------------------
           x in v1 <=> x in v4 or x in v5    
 
    set.size : (FiniteSet S) -> Int
    set.subset : (FiniteSet S) (FiniteSet S) -> Bool
       
--*/

class finite_set_axioms {
    ast_manager&    m;
    finite_set_util u;

    std::function<void(expr_ref_vector const &)> m_add_clause;

public:

    finite_set_axioms(ast_manager &m) : m(m), u(m) {}

    void set_add_clause(std::function<void(expr_ref_vector const &)> &ac) {
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

    // a := set.select(p, b)
    // (x in a) <=> (x in b) and p(x)
    void in_select_axiom(expr *x, expr *a);

    // a := set.singleton(b)
    // set.size(a) = 1
    void size_singleton_axiom(expr *a);

};
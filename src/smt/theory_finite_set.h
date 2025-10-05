/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_finite_set.h

Abstract:

    The theory solver relies on instantiating axiom schemas for finite sets.
    The instantation rules can be represented as implementing inference rules
    that encode the semantics of set operations.
    It reduces satisfiability into a combination of satisfiability of arithmetic and uninterpreted functions.

    This module implements axiom schemas that are invoked by saturating constraints
    with respect to the semantics of set operations.

    Let v1 ~ v2 mean that v1 and v2 are congruent

    The set-based decision procedure relies on saturating with respect
    to rules of the form:

       x in v1 == v2, v1 ~ set.empty
    -----------------------------------
       v1 = set.empty => not (x in v1)


     x in v1 == v2, v1 ~ v3, v3 == (set.union v4 v5)
     -----------------------------------------------
           x in v3 <=> x in v4 or x in v5

     x in v1 == v2, v1 ~ v3, v3 == (set.intersect v4 v5)
     ---------------------------------------------------
           x in v3 <=> x in v4 and x in v5

    x in v1 == v2, v1 ~ v3, v3 == (set.difference v4 v5)
    ---------------------------------------------------
         x in v3 <=> x in v4 and not (x in v5)

    x in v1 == v2, v1 ~ v3, v3 == (set.singleton v4)
    -----------------------------------------------
         x in v3 <=> x == v4

    x in v1 == v2, v1 ~ v3, v3 == (set.range lo hi)
    -----------------------------------------------
         x in v3 <=> (lo <= x <= hi)

    x in v1 == v2, v1 ~ v3, v3 == (set.map f v4)
    -----------------------------------------------
     x in v3 <=> set.map_inverse(f, x, v4) in v4

    x in v1 == v2, v1 ~ v3, v3 == (set.map f v4)
   -----------------------------------------------
        x in v4 => f(x) in v3

   x in v1 == v2, v1 ~ v3, v3 == (set.select p v4)
   -----------------------------------------------
        x in v3 <=> p(x) and x in v4

The central claim is that the above rules are sufficient to
decide satisfiability of finite set constraints.
Model construction proceeds by selecting every set.in(x_i, v) for a 
congruence root v. Then the set of elements { x_i | set.in(x_i, v) } 
is the interpretation.

This approach, however, does not work with ranges, or is impractical.
For ranges, we are going to extract an interpretation for set variable v
directly from a set of range expressions.
Inductively, the interpretation of a range expression is given by the
range itself. It proceeds by taking unions, intersections and differences of range
interpretations. 

For Boolean lattice constraints given by equality, subset, strict subset and union, intersections, 
the theory solver uses a stand-alone satisfiability checker for Boolean algebras to close branches.

--*/

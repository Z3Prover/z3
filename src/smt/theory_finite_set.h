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

Rules are encoded in src/ast/rewriter/finite_set_axioms.cpp as clauses.

The central claim is that the above rules are sufficient to
decide satisfiability of finite set constraints for a subset
of operations, namely union, intersection, difference, singleton, membership.
Model construction proceeds by selecting every set.in(x_i, v) for a 
congruence root v. Then the set of elements { x_i | set.in(x_i, v) } 
is the interpretation.

This approach for model-construction, however, does not work with ranges, or is impractical.
For ranges we can adapt a different model construction approach.

When introducing select and map, decidability can be lost.

For Boolean lattice constraints given by equality, subset, strict subset and union, intersections, 
the theory solver uses a stand-alone satisfiability checker for Boolean algebras to close branches.

Instructions for copilot:

1. Override relevant methods for smt::theory. Add them to the signature and add stubs or implementations in
theory_finite_set.cpp.
2. In final_check_eh add instantiation of theory axioms following the outline in the inference rules above.
   An example of how to instantiate axioms is in theory_arrays_base.cpp and theroy_datatypes.cpp and other theory files.
--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "util/obj_pair_hashtable.h"
#include "smt/smt_theory.h"

namespace smt {
    class theory_finite_set : public theory {
        friend class theory_finite_set_test;
        finite_set_util           u;
        finite_set_axioms         m_axioms;
        obj_hashtable<enode>      m_elements;             // set of all 'x' where there is an 'x in S' atom
        vector<expr_ref_vector>   m_lemmas;
        obj_pair_hashtable<expr, expr> m_lemma_exprs;
        
    protected:
        // Override relevant methods from smt::theory
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        final_check_status final_check_eh() override;
        
        theory * mk_fresh(context * new_ctx) override;
        char const * get_name() const override { return "finite_set"; }
        void display(std::ostream & out) const override;
        void init_model(model_generator & mg) override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;

        // Helper methods for axiom instantiation
        void instantiate_axioms(expr* elem, expr* set);
        void add_clause(expr_ref_vector const& clause);
        void assert_clause(expr_ref_vector const &clause);
        bool instantiate_false_lemma();
        bool instantiate_unit_propagation();
        bool instantiate_free_lemma();
        lbool truth_value(expr *e);
        
    public:
        theory_finite_set(context& ctx);
        ~theory_finite_set() override {}
    };

}  // namespace smt 

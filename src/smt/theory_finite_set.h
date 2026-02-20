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

       x in v1 a term, v1 ~ set.empty
    -----------------------------------
           not (x in set.empty)


     x in v1 a term , v1 ~ v3, v3 := (set.union v4 v5)
     -----------------------------------------------
           x in v3 <=> x in v4 or x in v5

     x in v1 a term, v1 ~ v3, v3 := (set.intersect v4 v5)
     ---------------------------------------------------
           x in v3 <=> x in v4 and x in v5

    x in v1 a term, v1 ~ v3, v3 := (set.difference v4 v5)
    ---------------------------------------------------
         x in v3 <=> x in v4 and not (x in v5)

    x in v1 a term, v1 ~ v3, v3 := (set.singleton v4)
    -----------------------------------------------
         x in v3 <=> x == v4

    x in v1 a term, v1 ~ v3, v3 := (set.range lo hi)
    -----------------------------------------------
         x in v3 <=> (lo <= x <= hi)

    x in v1 a term, v1 ~ v3, v3 := (set.map f v4)
    -----------------------------------------------
     x in v3 <=> set.map_inverse(f, x, v4) in v4

    x in v1 a term, v1 ~ v3, v3 := (set.map f v4)
   -----------------------------------------------
        x in v4 => f(x) in v3


   x in v1 is a term, v1 ~ v3, v3 == (set.filter p v4)
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


--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "util/obj_pair_hashtable.h"
#include "util/union_find.h"
#include "smt/smt_theory.h"
#include "smt/theory_finite_set_size.h"
#include "model/finite_set_factory.h"

namespace smt {
    class context;

    class theory_finite_set : public theory {
        using th_union_find = union_find<theory_finite_set>;
        friend class theory_finite_set_test;
        friend class theory_finite_set_size;
        friend struct finite_set_value_proc;

        struct var_data {
            ptr_vector<enode> m_setops;                // set operations equivalent to this
            ptr_vector<enode> m_parent_in;             // x in A expressions
            ptr_vector<enode> m_parent_setops;         // set of set expressions where this appears as sub-expression
            expr_ref_vector   m_range_local;           // set of range local variables associated with range
            var_data(ast_manager &m) : m_range_local(m) {}
        };

        struct theory_clauses {
            ptr_vector<theory_axiom>    axioms;            // vector of created theory axioms
            unsigned                aqhead = 0;        // queue head of created axioms
            unsigned_vector         squeue;            // propagation queue of axioms to be added to the solver
            unsigned                sqhead = 0;        // head into propagation queue axioms to be added to solver
            obj_pair_hashtable<expr, expr> members;    // set of membership axioms that were instantiated
            vector<unsigned_vector>  watch;            // watch list from expression index to clause occurrence

            bool can_propagate() const {
                return sqhead < squeue.size() || aqhead < axioms.size();
            }
        };

        struct stats {
            unsigned m_num_axioms_created = 0;
            unsigned m_num_axioms_conflicts = 0;
            unsigned m_num_axioms_propagated = 0;
            unsigned m_num_axioms_case_splits = 0;

            void collect_statistics(::statistics & st) const {
                st.update("finite-set-axioms-created", m_num_axioms_created);
                st.update("finite-set-axioms-propagated", m_num_axioms_propagated);
                st.update("finite-set-axioms-conflicts", m_num_axioms_conflicts);
                st.update("finite-set-axioms-case-splits", m_num_axioms_case_splits);
            }
        };

        finite_set_util           u;
        finite_set_axioms         m_axioms;
        th_rewriter               m_rw;
        th_union_find             m_find;
        theory_clauses            m_clauses;
        theory_finite_set_size m_cardinality_solver;
        finite_set_factory *m_factory = nullptr;
        obj_map<enode, obj_map<enode, bool> *> m_set_members;
        ptr_vector<func_decl> m_set_in_decls;
        ptr_vector<var_data> m_var_data;
        svector<std::pair<theory_var, theory_var>> m_diseqs, m_eqs;
        stats m_stats;
               
    protected:
        // Override relevant methods from smt::theory
        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        void apply_sort_cnstr(enode *n, sort *s) override; 
        final_check_status final_check_eh(unsigned) override;
        bool can_propagate() override;
        void propagate() override;
        void assign_eh(bool_var v, bool is_true) override;
        void relevant_eh(app *n) override;
        
        theory * mk_fresh(context * new_ctx) override;
        char const * get_name() const override { return "finite_set"; }
        void display(std::ostream & out) const override;
        void init_model(model_generator & mg) override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
        theory_var mk_var(enode *n) override;

        void collect_statistics(::statistics & st) const override {
            m_stats.collect_statistics(st);
        }

        void add_in_axioms(theory_var v1, theory_var v2);
        void add_in_axioms(enode *in, var_data *d);

        // Helper methods for axiom instantiation
        void add_membership_axioms(expr* elem, expr* set);
        void add_clause(theory_axiom * ax);
        bool assert_clause(theory_axiom const *ax);
        void activate_clause(unsigned index);
        bool activate_unasserted_clause();
        void add_immediate_axioms(app *atom);
        bool activate_range_local_axioms();
        bool activate_range_local_axioms(expr *elem, enode *range);
        bool assume_eqs();
        bool is_new_axiom(expr *a, expr *b);
        app *mk_union(unsigned num_elems, expr *const *elems, sort* set_sort);
        bool is_fully_solved();

        // model construction
        void collect_members();
        void reset_set_members();
        void add_range_interpretation(enode *s);

        // manage union-find of theory variables
        theory_var find(theory_var v) const { return m_find.find(v); }        
        bool is_root(theory_var v) const { return m_find.is_root(v); }

        std::ostream &display_var(std::ostream &out, theory_var v) const;

        bool are_forced_distinct(enode *a, enode *b);
        
    public:
        theory_finite_set(context& ctx);
        ~theory_finite_set() override;

        // for union-find
        trail_stack &get_trail_stack();
        void merge_eh(theory_var v1, theory_var v2, theory_var, theory_var);
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {}
        void unmerge_eh(theory_var v1, theory_var v2) {}
    };

}  // namespace smt 

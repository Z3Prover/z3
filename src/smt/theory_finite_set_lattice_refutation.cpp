#include "smt/theory_finite_set_lattice_refutation.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"
#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"

const int INITIAL_MAX_DIMENSION = 1000;

namespace smt {
    theory_finite_set_lattice_refutation::theory_finite_set_lattice_refutation(theory_finite_set& th): 
    m(th.m), ctx(th.ctx), th(th), u(m), bs(m), m_assumption(m), reachability(INITIAL_MAX_DIMENSION) {}

    // determines if the two enodes capture a subset relation:
    // checks, whether intersect_expr = intersect(subset, return_value) for some return value
    // otherwise return null
    enode* theory_finite_set_lattice_refutation::get_superset(enode* subset, enode* intersect_expr){
        expr* arg1 = nullptr, *arg2 = nullptr;
        if(u.is_intersect(intersect_expr->get_expr(), arg1, arg2)){
            if(arg1 == subset->get_expr()){
                return ctx.get_enode(arg2);
            }
            if(arg2 == subset->get_expr()){
                return ctx.get_enode(arg1);
            }
        }
        return nullptr;
    }

    void theory_finite_set_lattice_refutation::add_equality(theory_var v1, theory_var v2){
        auto n1 = th.get_enode(v1);
        auto n2 = th.get_enode(v2);

        enode* subset = n1;
        enode* superset = get_superset(n1, n2);
        if(superset == nullptr){
            subset = n2;
            superset = get_superset(n2, n1);
        }
        if(superset == nullptr){
            return;
        }
        relations.push_back({subset, superset});
        ctx.push_trail(push_back_trail(relations));
        TRACE(finite_set, tout << "new_eq_intersection: " << enode_pp(subset, ctx) << "\\subseteq " << enode_pp(superset, ctx));
        eq_propagation_justification(n1, n2);
    };

    void theory_finite_set_lattice_refutation::add_disequality(theory_var v1, theory_var v2){
        auto n1 = th.get_enode(v1);
        auto n2 = th.get_enode(v2);

        enode* subset = n1;
        enode* superset = get_superset(n1, n2);
        if(superset == nullptr){
            subset = n2;
            superset = get_superset(n2, n1);
        }
        if(superset == nullptr){
            return;
        }
        non_relations.push_back({subset, superset});
        ctx.push_trail(push_back_trail(non_relations));
        TRACE(finite_set, tout << "new_diseq_intersection: " << enode_pp(subset, ctx) << "\\not\\subseteq " << enode_pp(superset, ctx));

        auto eq_expr = m.mk_not(m.mk_eq(n1->get_expr(), n2->get_expr()));
        auto lit = ctx.get_literal(eq_expr);
        TRACE(finite_set, tout << "new_diseq_intersection_assignment: " << lit);
        ctx.display_assignment(tout);
    }

    void theory_finite_set_lattice_refutation::check_conflict(){
        for (size_t i = 0; i < non_relations.size(); i++)
        {
            auto rel = non_relations[i];
            vector<parameter> params;
            auto just = ctx.mk_justification(ext_theory_conflict_justification(th.get_id(), ctx, 0, nullptr, 0, nullptr, params.size(), params.data()));
        }
    }
}
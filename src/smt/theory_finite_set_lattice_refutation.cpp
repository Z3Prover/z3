#include "smt/theory_finite_set_lattice_refutation.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"
#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"

const int INITIAL_MAX_DIMENSION = 1000;

namespace smt {
    reachability_matrix::reachability_matrix(int max_dimensions, context& ctx):
    subset_relations(max_dimensions*max_dimensions, {null_theory_var, {nullptr, nullptr}}), 
    non_subset_relations(max_dimensions*max_dimensions, {nullptr, nullptr}), largest_var(0), max_size(max_dimensions), ctx(ctx) {}

    int reachability_matrix::get_max_var(){
        return largest_var;
    }

    bool reachability_matrix::is_reachability_forbidden(theory_var source, theory_var dest){
        if(non_subset_relations[source*max_size+dest].first!= nullptr){
            return true;
        }
        return false;
    }

    bool reachability_matrix::in_bounds(theory_var source, theory_var dest){
        return source >= 0 && dest >= 0 && source < max_size && dest<max_size;
    }

    bool reachability_matrix::is_reachable(theory_var source, theory_var dest){
        if(subset_relations[source*max_size+dest].second.first!=nullptr){
            return true;
        }
        return false;
    }

    std::pair<theory_var, enode_pair> reachability_matrix::get_reachability_reason(theory_var source, theory_var dest){
        return subset_relations[source*max_size+dest];
    }

    enode_pair reachability_matrix::get_non_reachability_reason(theory_var source, theory_var dest){
        return non_subset_relations[source*max_size+dest];
    }

    void reachability_matrix::set_reachability(theory_var source, theory_var dest, theory_var intermediate, enode_pair subset_relation){
        // TODO: could replace longer links by shorter links
        if(!is_reachable(source, dest)){
            ctx.push_trail(value_trail(largest_var));
            largest_var = std::max({largest_var, source, dest});
            std::pair<theory_var, enode_pair> new_value = {intermediate, subset_relation};
            ctx.push_trail(value_trail(subset_relations[source*max_size+dest]));
            subset_relations[source*max_size+dest] = new_value;
            TRACE(finite_set, tout << "new_reachability: " << source << "\\subseteq " << dest);
        }
    }

    void reachability_matrix::set_non_reachability(theory_var source, theory_var dest, enode_pair subset_relation){
        if(!is_reachability_forbidden(source, dest)){
            ctx.push_trail(value_trail(largest_var));
            largest_var = std::max({largest_var, source, dest});
            ctx.push_trail(value_trail(non_subset_relations[source*max_size+dest]));
            non_subset_relations[source*max_size+dest] = subset_relation;
            TRACE(finite_set, tout << "new_reachability_forbidden: " << source << "\\subseteq " << dest);
        }
    }

    theory_finite_set_lattice_refutation::theory_finite_set_lattice_refutation(theory_finite_set& th): 
    m(th.m), ctx(th.ctx), th(th), u(m), bs(m), m_assumption(m), reachability(INITIAL_MAX_DIMENSION, th.ctx) {}

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
        TRACE(finite_set, tout << "new_eq_intersection: " << enode_pp(subset, ctx) << "("<<th.get_th_var(subset)<<")" << "\\subseteq " << enode_pp(superset, ctx)<<"("<<th.get_th_var(superset)<<")");
        add_subset(subset, superset, {n1, n2});
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
        TRACE(finite_set, tout << "new_diseq_intersection: " << enode_pp(subset, ctx) << "("<<th.get_th_var(subset)<<")" << "\\not\\subseteq " << enode_pp(superset, ctx)<<"("<<th.get_th_var(superset)<<")");
        add_not_subset(subset, superset, {n1, n2});
    };

    void theory_finite_set_lattice_refutation::check_conflict(theory_var subset, theory_var superset){
        if(!reachability.is_reachable(subset, superset)){
            // if no reachability is asserted, no conflict can occur
            return;
        }
        if(!reachability.is_reachability_forbidden(subset, superset)){
            return;
        }
        // conflict found - build justification

        auto diseq_nodes = reachability.get_non_reachability_reason(subset, superset);
        auto eq_expr = m.mk_not(m.mk_eq(diseq_nodes.first->get_expr(), diseq_nodes.second->get_expr()));
        auto disequality_literal = ctx.get_literal(eq_expr);

        vector<enode_pair> equalities;
        auto reachability_just = reachability.get_reachability_reason(subset, superset);
        equalities.push_back(reachability_just.second);
        while(reachability_just.first!=null_theory_var){
            reachability_just = reachability.get_reachability_reason(reachability_just.first, superset);
            equalities.push_back(reachability_just.second);

        }

        auto j1 = ext_theory_conflict_justification(th.get_id(), ctx, 1, &disequality_literal, equalities.size(), equalities.data());
        auto justification = ctx.mk_justification(j1);

        ctx.set_conflict(justification);
    }

    void theory_finite_set_lattice_refutation::propagate_new_subset(theory_var subset, theory_var superset){
        // TODO: this function might be the bottleneck
        check_conflict(subset, superset);
        SASSERT(reachability.is_reachable(subset, superset));
        for (int i = 0; i <= reachability.get_max_var(); i++)
        {
            for(int j = 0; j <= reachability.get_max_var(); j++){
                // check whether there is a new connection from i to j

                if(reachability.is_reachable(i,j) || i == j || (i==subset && j == superset)){
                    continue;
                }
                if(i==subset && reachability.is_reachable(superset, j)){
                    reachability.set_reachability(i, j, superset, reachability.get_reachability_reason(subset,superset).second);
                    check_conflict(subset, j);
                }
                if(j==superset && reachability.is_reachable(i, subset)){
                    reachability.set_reachability(i, j, subset, reachability.get_reachability_reason(i,subset).second);
                    check_conflict(i, superset);
                }
                if(reachability.is_reachable(i, subset) && reachability.is_reachable(superset, j)){
                    reachability.set_reachability(subset, j, superset, reachability.get_reachability_reason(subset,superset).second);
                    reachability.set_reachability(i, j, subset, reachability.get_reachability_reason(i,subset).second);
                    check_conflict(i, j);
                }
            }
        }
    }

    void theory_finite_set_lattice_refutation::add_subset(enode* subset, enode* superset, enode_pair justifying_equality){
        // TODO: cycle detection here for equality propagation
        auto subset_t = subset->get_th_var(th.get_id());
        auto superset_t = superset->get_th_var(th.get_id());
        if (subset_t == null_theory_var || superset_t == null_theory_var){
            return;
        }
        reachability.set_reachability(subset_t, superset_t, null_theory_var, justifying_equality);
        SASSERT(reachability.is_reachable(subset_t, superset_t));
        propagate_new_subset(subset_t, superset_t);
    };

    void theory_finite_set_lattice_refutation::add_not_subset(enode* subset, enode* superset, enode_pair justifying_disequality){
        auto subset_t = subset->get_th_var(th.get_id());
        auto superset_t = superset->get_th_var(th.get_id());
        if (subset_t == null_theory_var || superset_t == null_theory_var){
            return;
        }
        reachability.set_non_reachability(subset_t, superset_t, justifying_disequality);
        check_conflict(subset_t, superset_t);
    }
}

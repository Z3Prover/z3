#include "smt/theory_finite_set_lattice_refutation.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"
#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"

const int NUM_WORDS = 5;

namespace smt {
    reachability_matrix::reachability_matrix(context& ctx):
    reachable(NUM_WORDS*NUM_WORDS*64, 0),
    links(NUM_WORDS*NUM_WORDS*64, 0),
    non_links(NUM_WORDS*NUM_WORDS*64, 0), largest_var(0), max_size(NUM_WORDS*64), ctx(ctx) {}

    int reachability_matrix::get_max_var(){
        return largest_var;
    }

    inline int reachability_matrix::get_word_index(int row, int col) const{
        return  (row * NUM_WORDS) + (col / 64);
    };

    inline uint64_t reachability_matrix::get_bitmask(int col) const{
        return  1ull << (col%64);
    };

    bool reachability_matrix::is_reachability_forbidden(theory_var source, theory_var dest){
        return non_links[get_word_index(source,dest)] & get_bitmask(dest);
    }

    bool reachability_matrix::in_bounds(theory_var source, theory_var dest){
        return source >= 0 && dest >= 0 && source < max_size && dest<max_size;
    }

    bool reachability_matrix::is_reachable(theory_var source, theory_var dest){
        return reachable[get_word_index(source,dest)] & get_bitmask(dest);
    }

    bool reachability_matrix::bitwise_or_rows(int source_dest, int source){
        bool changes = false;
        for (int i = 0; i < NUM_WORDS; i++)
        {
            uint64_t old_value = reachable[source_dest*NUM_WORDS+i];
            uint64_t new_value = reachable[source_dest*NUM_WORDS+i] | reachable[source*NUM_WORDS+i];
            if(old_value == new_value){
                continue;
            }
            ctx.push_trail(value_trail(reachable[source_dest*NUM_WORDS+i]));
            reachable[source_dest*NUM_WORDS+i] = new_value;
            changes = true;
            TRACE(finite_set, tout << "bitwise_or_rows(" << source_dest << "," << source <<"), i:"<<i);
            TRACE(finite_set, tout << "old_value: " << old_value << ", new_value:" << new_value <<")");
        }
        return changes;
    }

    bool reachability_matrix::set_reachability(theory_var source, theory_var dest){
        TRACE(finite_set, tout << "set_reachability(" << source << "," << dest <<")");
        if (is_reachable(source, dest)){
            TRACE(finite_set, tout << "already_reachable(" << source << "," << dest <<")");
            return false;
        }
        int word_idx = get_word_index(source, dest);
        TRACE(finite_set, tout << "reachable_nodes[first word](" << reachable[source*NUM_WORDS] << "," << reachable[dest*NUM_WORDS] <<")");
        ctx.push_trail(value_trail(reachable[word_idx]));
        reachable[word_idx] |= get_bitmask(dest);
        ctx.push_trail(value_trail(links[word_idx]));
        links[word_idx] |= get_bitmask(dest);
        // update reachability of source
        bitwise_or_rows(source, dest);
        

        for (int i = 0; i < largest_var; i++)
        { //update reachability of i to the nodes reachable from dest
            if(!is_reachable(i, source) || i == source){
                continue;
            }
            bitwise_or_rows(i, source);
        }
        return true;
    }

    bool reachability_matrix::set_non_reachability(theory_var source, theory_var dest){
        if(is_reachability_forbidden(source, dest)){
            return false;
        }
        int word_idx = get_word_index(source, dest);
        ctx.push_trail(value_trail(non_links[word_idx]));
        non_links[word_idx] |= get_bitmask(dest);
        return true;
    }

    theory_finite_set_lattice_refutation::theory_finite_set_lattice_refutation(theory_finite_set& th): 
    m(th.m), ctx(th.ctx), th(th), u(m), bs(m), m_assumption(m), reachability(th.ctx) {}

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

    }

    void theory_finite_set_lattice_refutation::add_subset(enode* subset, enode* superset, enode_pair justifying_equality){
        // TODO: cycle detection here for equality propagation
        auto subset_t = subset->get_th_var(th.get_id());
        auto superset_t = superset->get_th_var(th.get_id());
        if (subset_t == null_theory_var || superset_t == null_theory_var){
            return;
        }
        reachability.set_reachability(subset_t, superset_t);
        SASSERT(reachability.is_reachable(subset_t, superset_t));
    };

    void theory_finite_set_lattice_refutation::add_not_subset(enode* subset, enode* superset, enode_pair justifying_disequality){
        auto subset_t = subset->get_th_var(th.get_id());
        auto superset_t = superset->get_th_var(th.get_id());
        if (subset_t == null_theory_var || superset_t == null_theory_var){
            return;
        }
        reachability.set_non_reachability(subset_t, superset_t);
        SASSERT(reachability.is_reachability_forbidden(subset_t, superset_t));
    }
}

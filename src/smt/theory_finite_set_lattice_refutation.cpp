#include "smt/theory_finite_set_lattice_refutation.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"
#include "smt/theory_finite_set.h"
#include "smt/smt_context.h"

const int NUM_WORDS = 5;

namespace smt {
    reachability_matrix::reachability_matrix(context& ctx, theory_finite_set_lattice_refutation& t_lattice):
    reachable(NUM_WORDS*NUM_WORDS*64, 0),
    links(NUM_WORDS*NUM_WORDS*64*64, {nullptr, nullptr}),
    non_links(NUM_WORDS*NUM_WORDS*64),
    non_link_justifications(NUM_WORDS*NUM_WORDS*64*64, {nullptr, nullptr}), largest_var(0), max_size(NUM_WORDS*64), ctx(ctx), t_lattice_refutation(t_lattice) {}

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
        return non_links[get_word_index(source, dest)] & get_bitmask(dest);
    }

    bool reachability_matrix::in_bounds(theory_var source, theory_var dest){
        return source >= 0 && dest >= 0 && source < max_size && dest<max_size;
    }

    bool reachability_matrix::is_reachable(theory_var source, theory_var dest){
        return reachable[get_word_index(source,dest)] & get_bitmask(dest);
    }

    bool reachability_matrix::is_linked(theory_var source, theory_var dest){
        return links[source*max_size+dest].first != nullptr;
    }

    bool reachability_matrix::bitwise_or_rows(int source_dest, int source){
        bool changes = false;
        // TODO: utilize largest_var
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
            check_reachability_conflict_word(source_dest, i);
        }
        return changes;
    }

    bool reachability_matrix::set_reachability(theory_var source, theory_var dest, enode_pair reachability_witness){
        TRACE(finite_set, tout << "set_reachability(" << source << "," << dest <<")");
        if (is_reachable(source, dest)){
            return false;
        }
        ctx.push_trail(value_trail(largest_var));
        largest_var = std::max({largest_var, source, dest});

        int word_idx = get_word_index(source, dest);
        ctx.push_trail(value_trail(reachable[word_idx]));
        reachable[word_idx] |= get_bitmask(dest);
        ctx.push_trail(value_trail(links[source*max_size + dest]));
        links[source*max_size+dest] = reachability_witness;
        check_reachability_conflict(source, dest);
        // update reachability of source
        bitwise_or_rows(source, dest);        

        for (int i = 0; i <= largest_var; i++)
        { //update reachability of i to the nodes reachable from dest
            if(!is_reachable(i, source) || i == source){
                continue;
            }
            bitwise_or_rows(i, source);
        }
        return true;
    }

    bool reachability_matrix::set_non_reachability(theory_var source, theory_var dest, enode_pair non_reachability_witness){
        if(is_reachability_forbidden(source, dest)){
            return false;
        }
        ctx.push_trail(value_trail(largest_var));
        largest_var = std::max({largest_var, source, dest});
        ctx.push_trail(value_trail(non_links[get_word_index(source, dest)]));
        non_links[get_word_index(source, dest)] |= get_bitmask(dest);
        ctx.push_trail(value_trail(non_link_justifications[source*max_size+dest]));
        non_link_justifications[source*max_size+dest] = non_reachability_witness;
        check_reachability_conflict(source, dest);
        return true;
    }

    theory_finite_set_lattice_refutation::theory_finite_set_lattice_refutation(theory_finite_set& th): 
    m(th.m), ctx(th.ctx), th(th), u(m), bs(m), m_assumption(m), reachability(th.ctx, *this) {}

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

    void reachability_matrix::get_path(theory_var source, theory_var dest, vector<enode_pair>& path){
        SASSERT(is_reachable(source, dest));
        vector<bool> visited(max_size, false);
        visited[source] = true;
        while(source != dest){
            bool success = false;
            for (int i = 0; i <= largest_var; i++)
            {
                if(!visited[i] && is_linked(source, i) && ((is_reachable(i, dest)) || i == dest)){
                    path.push_back(links[source*max_size+i]);
                    source = i;
                    visited[source] = true;
                    success = true;
                    break;
                }
            }
            SASSERT(success);
        }
    }

    bool reachability_matrix::check_reachability_conflict(theory_var source, theory_var dest){
        if(is_reachable(source,dest) && is_reachability_forbidden(source, dest)){
            TRACE(finite_set, tout << "found_conflict: "<<source<<" -> "<<dest);
            vector<enode_pair> path;
            get_path(source, dest, path);
            TRACE(finite_set, tout << "found path: "<<source<<" -> "<<dest<<" length: "<<path.size());
            enode_pair diseq = non_link_justifications[source*max_size+dest];
            t_lattice_refutation.trigger_conflict(path, diseq);
            return true;
        }
        return false;
    }

    bool reachability_matrix::check_reachability_conflict_word(int row, int word){
        if(reachable[row*NUM_WORDS+word] & non_links[row*NUM_WORDS+word]){

            TRACE(finite_set, tout << "found_conflict (row: "<<row<<",word: "<<word<<")");
            // somewhere in this word there is a conflict
            for (int i = word*64; i < word*64+64; i++)
            {
                if(check_reachability_conflict(row, i)){
                    return true;
                }
            }
            
        }
        return false;
    }

    void theory_finite_set_lattice_refutation::trigger_conflict(vector<enode_pair> equalities, enode_pair clashing_disequality){
        auto eq_expr = m.mk_not(m.mk_eq(clashing_disequality.first->get_expr(), clashing_disequality.second->get_expr()));
        auto disequality_literal = ctx.get_literal(eq_expr);
        auto j1 = ext_theory_conflict_justification(th.get_id(), ctx, 1, &disequality_literal, equalities.size(), equalities.data());
        auto justification = ctx.mk_justification(j1);
        
        TRACE(finite_set, tout << "setting_partial_order_conflict");
        ctx.set_conflict(justification);
    }

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

    void theory_finite_set_lattice_refutation::add_subset(enode* subset, enode* superset, enode_pair justifying_equality){
        // TODO: cycle detection here for equality propagation
        auto subset_t = subset->get_th_var(th.get_id());
        auto superset_t = superset->get_th_var(th.get_id());
        if (subset_t == null_theory_var || superset_t == null_theory_var){
            return;
        }
        reachability.set_reachability(subset_t, superset_t, justifying_equality);
        SASSERT(reachability.is_reachable(subset_t, superset_t));
    };

    void theory_finite_set_lattice_refutation::add_not_subset(enode* subset, enode* superset, enode_pair justifying_disequality){
        auto subset_t = subset->get_th_var(th.get_id());
        auto superset_t = superset->get_th_var(th.get_id());
        if (subset_t == null_theory_var || superset_t == null_theory_var){
            return;
        }
        reachability.set_non_reachability(subset_t, superset_t, justifying_disequality);
        SASSERT(reachability.is_reachability_forbidden(subset_t, superset_t));
    }
}

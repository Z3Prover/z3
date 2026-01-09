#pragma once

#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"

namespace smt {
    class context;
    class theory_finite_set;

    class reachability_matrix{

        // this stores the equalities (intersections), that justify the subset relations.
        std::vector<std::pair<theory_var, enode_pair>> subset_relations;
        std::vector<enode_pair> non_subset_relations;
        int largest_var;

        int max_size;

        context& ctx;

        public:
            reachability_matrix(int max_dim, context& ctx);
            bool in_bounds(theory_var source, theory_var dest);
            bool is_reachable(theory_var source, theory_var dest);
            bool is_reachability_forbidden(theory_var source, theory_var dest);
            // get_reachability_reason(i,j) returns:
            //   - {-1, equality} when equality covers the subset relation of i and j (represented as equality of term and intersection)
            //   - {intermediate, equality} when intermediate is a subset of j, and equality 
            //     covers the relation of i and intermediate (transitivity)
            std::pair<theory_var, enode_pair> get_reachability_reason(theory_var source, theory_var dest);
            enode_pair get_non_reachability_reason(theory_var source, theory_var dest);

            bool set_reachability(theory_var source, theory_var dest, theory_var intermediate, enode_pair subset_relation);
            bool set_non_reachability(theory_var source, theory_var dest, enode_pair subset_relation);
            int get_max_var();
    };

    class theory_finite_set_lattice_refutation {
        ast_manager          &m;
        context             &ctx;
        theory_finite_set   &th;
        finite_set_util u;
        expr_ref_vector bs;
        expr_ref m_assumption;
        reachability_matrix reachability;

        enode* get_superset(enode*, enode*);
        void add_subset(enode* subset, enode* superset, enode_pair justifying_equality);
        void add_not_subset(enode* subset, enode* superset, enode_pair justifying_disequality);
        void propagate_new_subset(theory_var v1, theory_var v2);
        void check_conflict(theory_var v1, theory_var v2);
        public:
            theory_finite_set_lattice_refutation(theory_finite_set &th);
            void add_equality(theory_var v1, theory_var v2);
            void add_disequality(theory_var v1, theory_var v2);
    };
}

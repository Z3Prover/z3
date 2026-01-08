#pragma once

#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"

namespace smt {
    class context;
    class theory_finite_set;

    class reachability_matrix{
        // this class is a 2d matrix with a fixed initial size (to avoid reallocation) which 
        std::vector<int> is_related;

        // this stores the equalities (intersections), that justify the subset relations.
        std::vector<std::pair<theory_var, enode_pair>*> subset_relations;
        unsigned m_max_cols;

        unsigned m_rows;
        unsigned m_cols;

        context& ctx;

        public:
            reachability_matrix(unsigned max_dim);
            bool is_reachable(theory_var source, theory_var dest);
            // get_reachability_reason(i,j) returns:
            //   - {-1, equality} when equality covers the subset relation of i and j
            //   - {intermediate, equality} when intermediate is a subset of j, and equality 
            //     covers the relation of i and intermediate (transitivity)
            std::pair<theory_var, enode_pair> get_reachability_reason(theory_var source, theory_var dest);
            int set(theory_var source, theory_var dest, int value, theory_var intermediate, enode_pair subset_relation);
    };

    class theory_finite_set_lattice_refutation {
        ast_manager          &m;
        context             &ctx;
        theory_finite_set   &th;
        finite_set_util u;
        expr_ref_vector bs;
        expr_ref m_assumption;
        reachability_matrix reachability;

        svector<std::pair<enode*, enode*>> relations;
        svector<std::pair<enode*, enode*>> non_relations;
        enode* get_superset(enode*, enode*);
        void check_conflict();
        public:
            theory_finite_set_lattice_refutation(theory_finite_set &th);
            void add_equality(theory_var v1, theory_var v2);
            void add_disequality(theory_var v1, theory_var v2);
    };
}

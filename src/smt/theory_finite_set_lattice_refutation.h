#pragma once

#include "ast/finite_set_decl_plugin.h"
#include "ast/rewriter/finite_set_axioms.h"
#include "smt/smt_theory.h"

namespace smt {
    class context;
    class theory_finite_set;

    class reachability_matrix{

        std::vector<uint64_t> reachable;
        std::vector<uint64_t> links;
        std::vector<uint64_t> non_links;

        int largest_var;

        int max_size;

        context& ctx;

        // sets source_dest |= dest, and pushing the changed words to the trail
        bool bitwise_or_rows(int source_dest, int source);
        inline int get_word_index(int row, int col) const;
        inline uint64_t get_bitmask(int col) const;
        public:
            reachability_matrix(context& ctx);
            bool in_bounds(theory_var source, theory_var dest);
            bool is_reachable(theory_var source, theory_var dest);
            bool is_reachability_forbidden(theory_var source, theory_var dest);

            bool set_reachability(theory_var source, theory_var dest);
            bool set_non_reachability(theory_var source, theory_var dest);
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

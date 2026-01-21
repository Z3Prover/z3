/*++
Copyright (c) 2025 Lorenz Winkler

Module Name:

    theory_finite_lattice_refutation.h

--*/

#pragma once

#include "ast/finite_set_decl_plugin.h"
#include "smt/smt_theory.h"

namespace smt {
    class context;
    class theory_finite_set;

    class theory_finite_set_lattice_refutation;
    class reachability_matrix {
        svector<uint64_t> reachable;    // V x V -> bitset of reachable nodes
        enode_pair_vector links;        // V x V -> enode_pair justifying the link
        svector<uint64_t> link_dls;     // V x V -> decision level when the link was added
        svector<uint64_t> non_links;    // V x V -> bitset of non-reachable nodes
        enode_pair_vector non_link_justifications;  // V x V -> enode_pair justifying the non-link

        int largest_var;

        int max_size;

        context &ctx;
        theory_finite_set_lattice_refutation &t_lattice_refutation;
        int conflict_row = -1;
        int conflict_word = -1;

        // sets source_dest |= dest, and pushing the changed words to the trail
        bool bitwise_or_rows(int source_dest, int source);
        inline int get_word_index(int row, int col) const;
        inline uint64_t get_bitmask(int col) const;

    public:
        std::pair<vector<enode_pair>, int> get_path(theory_var source, theory_var dest);
        reachability_matrix(context &ctx, theory_finite_set_lattice_refutation &t_lattice);
        bool in_bounds(theory_var source, theory_var dest);
        bool is_reachable(theory_var source, theory_var dest) const;
        bool is_reachability_forbidden(theory_var source, theory_var dest);
        bool is_linked(theory_var source, theory_var dest);

        bool check_reachability_conflict(theory_var source, theory_var dest);
        bool check_reachability_conflict_word(int row, int word);

        bool set_reachability(theory_var source, theory_var dest, enode_pair reachability_witness);
        bool set_non_reachability(theory_var source, theory_var dest, enode_pair non_reachability_witness);
        int get_max_var();
        void display_relations(std::ostream& out) const;
    };

    class theory_finite_set_lattice_refutation {
        ast_manager &m;
        context &ctx;
        theory_finite_set &th;
        finite_set_util u;
        expr_ref_vector bs;
        expr_ref m_assumption;
        reachability_matrix reachability;

        enode *get_superset(enode *, enode *);
        void add_subset(theory_var subset, theory_var superset, enode_pair justifying_equality);
        void add_not_subset(theory_var subset, theory_var superset, enode_pair justifying_disequality);
        void propagate_new_subset(theory_var v1, theory_var v2);
        void add_set_equality(enode *set1, enode *set2);

    public:
        void trigger_conflict(vector<enode_pair> equalities, enode_pair clashing_disequality);
        theory_finite_set_lattice_refutation(theory_finite_set &th);
        void add_equality(theory_var v1, theory_var v2);
        void add_disequality(theory_var v1, theory_var v2);
    };
}  // namespace smt

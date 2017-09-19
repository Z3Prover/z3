/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_min_cut.h

Abstract:
    min cut solver

Author:
    Bernhard Gleiss

Revision History:


--*/

#ifndef _SPACER_MIN_CUT_H_
#define _SPACER_MIN_CUT_H_

#include "ast/ast.h"
#include "util/vector.h"

namespace spacer {

    class spacer_min_cut {
    public:
        spacer_min_cut();

        unsigned new_node();
        void add_edge(unsigned i, unsigned j, unsigned capacity);
        void compute_min_cut(vector<unsigned>& cut_nodes);

    private:

        unsigned m_n; // number of vertices in the graph

        vector<vector<std::pair<unsigned, unsigned> > > m_edges; // map from node to all outgoing edges together with their weights (also contains "reverse edges")
        vector<unsigned> m_d; // approximation of distance from node to sink in residual graph
        vector<unsigned> m_pred; // predecessor-information for reconstruction of augmenting path
        vector<expr*> m_node_to_formula; // maps each node to the corresponding formula in the original proof

        void compute_initial_distances();
        unsigned get_admissible_edge(unsigned i);
        void augment_path();
        void compute_distance(unsigned i);
        void compute_reachable_nodes(vector<bool>& reachable);
        void compute_cut_and_add_lemmas(vector<bool>& reachable, vector<unsigned>& cut_nodes);
    };
}

#endif

/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    min_cut.h

Abstract:
    min cut solver

Author:
    Bernhard Gleiss

Revision History:


--*/

#ifndef MIN_CUT_H_
#define MIN_CUT_H_

#include "util/vector.h"


class min_cut {
public:
    min_cut();

    /*
      \brief create a node
    */
    unsigned new_node();

    /*
      \brief add an i -> j edge with (unit) capacity 
    */
    void add_edge(unsigned i, unsigned j, unsigned capacity = 1);

    /*
      \brief produce a min cut between source node = 0 and target node = 1.
      NB. the function changes capacities on edges.
    */
    void compute_min_cut(vector<unsigned>& cut_nodes);
    
private:

    struct edge { unsigned node; unsigned weight; edge(unsigned n, unsigned w): node(n), weight(w) {} edge(): node(0), weight(0) {} };
        
    vector<vector<edge>> m_edges; // map from node to all outgoing edges together with their weights (also contains "reverse edges")
    vector<unsigned> m_d;    // approximation of distance from node to sink in residual graph
    vector<unsigned> m_pred; // predecessor-information for reconstruction of augmenting path
    
    void compute_initial_distances();
    unsigned get_admissible_edge(unsigned i);
    void augment_path();
    void compute_distance(unsigned i);
    void compute_reachable_nodes(vector<bool>& reachable);
    void compute_cut_and_add_lemmas(vector<bool>& reachable, vector<unsigned>& cut_nodes);
};

#endif

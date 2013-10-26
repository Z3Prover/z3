/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    network_flow.h

Abstract:

    Implements Network Simplex algorithm for min cost flow problem

Author:

    Anh-Dung Phan (t-anphan) 2013-10-24

Notes:

    This will be used to solve the dual of min cost flow problem 
    i.e. optimization of difference constraint.

    We need a function to reduce DL constraints to min cost flow problem 
    and another function to convert from min cost flow solution to DL solution.

    It remains unclear how to convert DL assignment to a basic feasible solution of Network Simplex.
    A naive approach is to run an algorithm on max flow in order to get a spanning tree.

    The network_simplex class hasn't had multiple pivoting strategies yet.
   
--*/
#ifndef _NETWORK_FLOW_H_
#define _NETWORK_FLOW_H_

#include"inf_rational.h"
#include"diff_logic.h"

namespace smt {

    // Solve minimum cost flow problem using Network Simplex algorithm
    template<typename Ext>
    class network_flow : private Ext {
        typedef dl_var node;
        typedef dl_edge<Ext> edge;
        typedef dl_graph<Ext> graph;     
        typedef typename Ext::numeral numeral;
        graph m_graph;

        // Denote supply/demand b_i on node i
        vector<numeral> m_balances;

        // Duals of flows which are convenient to compute dual solutions
        vector<numeral> m_potentials;

        // Keep optimal solution of the min cost flow problem
        inf_rational m_objective;

        // Costs on edges
        vector<numeral> & m_costs;

        // Basic feasible flows
        vector<numeral> m_flows;

        // An element is true if the corresponding edge points upwards (compared to the root node)
        svector<bool> m_upwards;

        // Store the parent of a node in the spanning tree
        svector<node> m_pred;
        // Store the number of edge on the path to the root
        svector<int> m_depth;
        // Store the pointer to the next node in depth first search ordering
        svector<node> m_thread;

        bool m_is_optimal;

    public:

        network_flow(graph & g, vector<numeral> & costs);

        // Initialize the network with a feasible spanning tree
        void initialize();

        void compute_potentials();

        void compute_flows();
            
        // If all reduced costs are non-negative, the current flow is optimal
        // If not optimal, return a violating edge in the corresponding variable
        bool is_optimal(edge_id & violating_edge);

        // Send as much flow as possible around the cycle, the first basic edge with flow 0 will leave
        edge_id choose_leaving_edge(edge_id entering_edge);

        void update_spanning_tree(edge_id entering_edge, edge_id leaving_edge);
        
        bool is_unbounded();

        // Compute the optimal solution
        void get_optimal_solution(numeral & objective, vector<numeral> & flows);

        // Minimize cost flows
        // Return true if found an optimal solution, and return false if unbounded
        bool min_cost();
    };
}

#endif

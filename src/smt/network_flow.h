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

    template<typename T>
    std::string pp_vector(std::string const & label, svector<T> v, bool has_header = false);

    template<typename T>
    std::string pp_vector(std::string const & label, vector<T> v, bool has_header = false);

    // Solve minimum cost flow problem using Network Simplex algorithm
    template<typename Ext>
    class network_flow : private Ext {
        enum edge_state {
            NON_BASIS = 0,
            BASIS = 1
        };
        typedef dl_var node;
        typedef dl_edge<Ext> edge;
        typedef dl_graph<Ext> graph;     
        typedef typename Ext::numeral numeral;
        typedef typename Ext::fin_numeral fin_numeral;
        graph m_graph;

        // Denote supply/demand b_i on node i
        vector<fin_numeral> m_balances;

        // Duals of flows which are convenient to compute dual solutions
        vector<numeral> m_potentials;

        // Keep optimal solution of the min cost flow problem
        numeral m_objective_value;
        
        // Basic feasible flows
        vector<numeral> m_flows;
        
        svector<edge_state> m_states;

        // An element is true if the corresponding edge points upwards (compared to the root node)
        svector<bool> m_upwards;

        // Store the parent of a node i in the spanning tree
        svector<node> m_pred;
        // Store the number of edge on the path from node i to the root
        svector<int> m_depth;
        // Store the pointer from node i to the next node in depth first search ordering
        svector<node> m_thread;
        // Reverse orders of m_thread
        svector<node> m_rev_thread;
        // Store a final node of the sub tree rooted at node i
        svector<node> m_final;

        edge_id m_entering_edge;
        edge_id m_leaving_edge;
        node m_join_node;
        numeral m_delta;

        // Initialize the network with a feasible spanning tree
        void initialize();

        bool get_edge_id(dl_var source, dl_var target, edge_id & id);


        void update_potentials();

        void update_flows();
            
        // If all reduced costs are non-negative, return false since the current spanning tree is optimal
        // Otherwise return true and update m_entering_edge
        bool choose_entering_edge();

        // Send as much flow as possible around the cycle, the first basic edge with flow 0 will leave
        // Return false if the problem is unbounded
        bool choose_leaving_edge();

        void update_spanning_tree();

    public:

        network_flow(graph & g, vector<fin_numeral> const & balances);        
        
        // Minimize cost flows
        // Return true if found an optimal solution, and return false if unbounded
        bool min_cost();

        // Compute the optimal solution
        numeral get_optimal_solution(vector<numeral> & result, bool is_dual);

    };
}

#endif

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
#include"spanning_tree.h"

namespace smt {

    // Solve minimum cost flow problem using Network Simplex algorithm
    template<typename Ext>
    class network_flow : private Ext {
        enum edge_state {
            LOWER = 1,
            BASIS = 0,
            UPPER = -1
        };
        typedef dl_var node;
        typedef dl_edge<Ext> edge;
        typedef dl_graph<Ext> graph;     
        typedef typename Ext::numeral numeral;
        typedef typename Ext::fin_numeral fin_numeral;

        graph m_graph;
        thread_spanning_tree tree;

        // Denote supply/demand b_i on node i
        vector<fin_numeral> m_balances;

        // Duals of flows which are convenient to compute dual solutions
        vector<numeral> m_potentials;

        // Basic feasible flows
        vector<numeral> m_flows;
        
        svector<edge_state> m_states;

        unsigned m_step;

        edge_id m_entering_edge;
        edge_id m_leaving_edge;
        node m_join_node;
        optional<numeral> m_delta;
        bool m_in_edge_dir;

        // Initialize the network with a feasible spanning tree
        void initialize();

        edge_id get_edge_id(dl_var source, dl_var target) const;

        void update_potentials();

        void update_flows();
            
        // If all reduced costs are non-negative, return false since the current spanning tree is optimal
        // Otherwise return true and update m_entering_edge
        bool choose_entering_edge();

        // Send as much flow as possible around the cycle, the first basic edge with flow 0 will leave
        // Return false if the problem is unbounded
        bool choose_leaving_edge();

        void update_spanning_tree();

        std::string display_spanning_tree();

        bool edge_in_tree(edge_id id) const;
        bool edge_in_tree(node src, node dst) const;

        bool check_well_formed();
        bool check_optimal();

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

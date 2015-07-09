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
   
--*/
#ifndef NETWORK_FLOW_H_
#define NETWORK_FLOW_H_

#include"inf_rational.h"
#include"diff_logic.h"
#include"spanning_tree.h"

namespace smt {

    enum min_flow_result {
        // Min cost flow problem is infeasible.
        // Diff logic optimization could be unbounded or infeasible.
        INFEASIBLE,
        // Min cost flow and diff logic optimization are both optimal.
        OPTIMAL,
        // Min cost flow problem is unbounded.
        // Diff logic optimization has to be infeasible.
        UNBOUNDED,
    };

    enum pivot_rule {
        // First eligible edge pivot rule
        // Edges are traversed in a wraparound fashion
        FIRST_ELIGIBLE,
        // Best eligible edge pivot rule
        // The best edge is selected in every iteration
        BEST_ELIGIBLE,
        // Candidate list pivot rule
        // Major iterations: candidate list is built from eligible edges (in a wraparound way)
        // Minor iterations: the best edge is selected from the list
        CANDIDATE_LIST
    };

    // Solve minimum cost flow problem using Network Simplex algorithm
    template<typename Ext>
    class network_flow : private Ext {
    private:
        enum edge_state {
            LOWER = 1,
            BASIS = 0,
        };

        typedef dl_var node;
        typedef dl_edge<Ext> edge;
        typedef dl_graph<Ext> graph;     
        typedef typename Ext::numeral numeral;
        typedef typename Ext::fin_numeral fin_numeral;

        class pivot_rule_impl {
        protected:
            graph & m_graph;
            svector<edge_state> & m_states;
            vector<numeral> &     m_potentials;
            edge_id &             m_enter_id;
            bool edge_in_tree(edge_id id) const { return m_states[id] == BASIS; }
        public: 
            pivot_rule_impl(graph & g, vector<numeral> & potentials, 
                            svector<edge_state> & states, edge_id & enter_id) 
                : m_graph(g),
                  m_potentials(potentials),
                  m_states(states),
                  m_enter_id(enter_id) {
            }
            virtual ~pivot_rule_impl() {}
            virtual bool choose_entering_edge() = 0;
            virtual pivot_rule rule() const = 0;
        };
        
        class first_eligible_pivot : public pivot_rule_impl {
            edge_id m_next_edge;
        public:
            first_eligible_pivot(graph & g, vector<numeral> & potentials, 
                                 svector<edge_state> & states, edge_id & enter_id) : 
                pivot_rule_impl(g, potentials, states, enter_id),
                m_next_edge(0) {
            }
            virtual bool choose_entering_edge(); 
            virtual pivot_rule rule() const { return FIRST_ELIGIBLE; }
        };

        class best_eligible_pivot : public pivot_rule_impl {
        public:
            best_eligible_pivot(graph & g, vector<numeral> & potentials, 
                                 svector<edge_state> & states, edge_id & enter_id) : 
                pivot_rule_impl(g, potentials, states, enter_id) {
            }
            virtual pivot_rule rule() const { return BEST_ELIGIBLE; }
            virtual bool choose_entering_edge();
        };

        class candidate_list_pivot : public pivot_rule_impl {
        private:
            edge_id m_next_edge;
            svector<edge_id> m_candidates;
            unsigned m_num_candidates;
            unsigned m_minor_step;
            unsigned m_current_length;
            static const unsigned NUM_CANDIDATES = 10;
            static const unsigned MINOR_STEP_LIMIT = 5;

        public:
            candidate_list_pivot(graph & g, vector<numeral> & potentials, 
                                 svector<edge_state> & states, edge_id & enter_id) : 
                pivot_rule_impl(g, potentials, states, enter_id),
                m_next_edge(0),
                m_minor_step(0),
                m_current_length(0),
                m_num_candidates(NUM_CANDIDATES),
                m_candidates(m_num_candidates) {
            }

            virtual pivot_rule rule() const { return CANDIDATE_LIST; }

            virtual bool choose_entering_edge();
        };
        
        graph                m_graph;
        scoped_ptr<spanning_tree_base> m_tree;
        scoped_ptr<pivot_rule_impl>    m_pivot;
        vector<fin_numeral>  m_balances;     // nodes + 1 |-> [b -1b] Denote supply/demand b_i on node i
        vector<numeral>      m_potentials;   // nodes + 1 |-> initial: +/- 1  
                                             // Duals of flows which are convenient to compute dual solutions 
                                             // become solutions to Dual simplex.
        vector<numeral>      m_flows;        // edges + nodes |-> assignemnt Basic feasible flows
        svector<edge_state>  m_states;
        unsigned             m_step;
        edge_id              m_enter_id;
        edge_id              m_leave_id;
        optional<numeral>    m_delta;

        // Initialize the network with a feasible spanning tree
        void initialize();

        void update_potentials();

        void update_flows();
            
        bool choose_entering_edge(pivot_rule pr);

        // Send as much flow as possible around the cycle, the first basic edge with flow 0 will leave
        // Return false if the problem is unbounded
        bool choose_leaving_edge();

        void update_spanning_tree();

        numeral get_cost() const;

        bool edge_in_tree(edge_id id) const;

        bool is_infeasible();
        bool check_well_formed();
        bool check_optimal();

        void display_primal(std::ofstream & os);
        void display_dual(std::ofstream & os);
        void display_spanning_tree(std::ofstream & os);
        void display_system(std::ofstream & os);

    public:

        network_flow(graph & g, vector<fin_numeral> const & balances);        
        
        // Minimize cost flows
        // Return true if found an optimal solution, and return false if unbounded
        min_flow_result min_cost(pivot_rule pr = FIRST_ELIGIBLE);

        // Compute the optimal solution
        numeral get_optimal_solution(vector<numeral> & result, bool is_dual);

    };
}

#endif

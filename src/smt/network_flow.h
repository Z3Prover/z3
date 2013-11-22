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
#ifndef _NETWORK_FLOW_H_
#define _NETWORK_FLOW_H_

#include"inf_rational.h"
#include"diff_logic.h"
#include"spanning_tree_def.h"

namespace smt {

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
            UPPER = -1
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
            vector<numeral> & m_potentials;
            edge_id & m_enter_id;

        public: 
            pivot_rule_impl(graph & g, vector<numeral> & potentials, 
                            svector<edge_state> & states, edge_id & enter_id) 
                : m_graph(g),
                  m_potentials(potentials),
                  m_states(states),
                  m_enter_id(enter_id) {
            }
            virtual bool choose_entering_edge() = 0;
        };
        
        class first_eligible_pivot : public pivot_rule_impl {
        private:
            edge_id m_next_edge;

        public:
            first_eligible_pivot(graph & g, vector<numeral> & potentials, 
                                 svector<edge_state> & states, edge_id & enter_id) : 
                pivot_rule_impl(g, potentials, states, enter_id),
                m_next_edge(0) {
            }

            bool choose_entering_edge() {
                TRACE("network_flow", tout << "choose_entering_edge...\n";);        
                unsigned num_edges = m_graph.get_num_edges();
                for (unsigned i = m_next_edge; i < m_next_edge + num_edges; ++i) {
                    edge_id id = (i >= num_edges) ? (i - num_edges) : i;
                    node src = m_graph.get_source(id);
                    node tgt = m_graph.get_target(id);
                    if (m_states[id] != BASIS) {
                        numeral cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(id);
                        if (cost.is_pos()) {
                            m_enter_id = id;
                            TRACE("network_flow", {
                                tout << "Found entering edge " << id << " between node ";
                                tout << src << " and node " << tgt << " with reduced cost = " << cost << "...\n";
                            });
                            return true;
                        }
                    }
                }
                TRACE("network_flow", tout << "Found no entering edge...\n";);
                return false;
            };
        };

        class best_eligible_pivot : public pivot_rule_impl {
        public:
            best_eligible_pivot(graph & g, vector<numeral> & potentials, 
                                 svector<edge_state> & states, edge_id & enter_id) : 
                pivot_rule_impl(g, potentials, states, enter_id) {
            }

            bool choose_entering_edge() {
                TRACE("network_flow", tout << "choose_entering_edge...\n";);        
                unsigned num_edges = m_graph.get_num_edges();
                numeral max = numeral::zero();
                for (unsigned i = 0; i < num_edges; ++i) {
                    node src = m_graph.get_source(i);
                    node tgt = m_graph.get_target(i);
                    if (m_states[i] != BASIS) {
                        numeral cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(i);
                        if (cost > max) {
                            max = cost;
                            m_enter_id = i;
                        }
                    }
                }
                if (max.is_pos()) {
                    TRACE("network_flow", {
                        tout << "Found entering edge " << m_enter_id << " between node ";
                        tout << m_graph.get_source(m_enter_id) << " and node " << m_graph.get_target(m_enter_id);
                        tout << " with reduced cost = " << max << "...\n";
                    });
                    return true;
                }
                TRACE("network_flow", tout << "Found no entering edge...\n";);
                return false;
            };
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

            bool choose_entering_edge() {
                if (m_current_length == 0 || m_minor_step == MINOR_STEP_LIMIT) {
                    // Build the candidate list
                    unsigned num_edges = m_graph.get_num_edges();
                    numeral max = numeral::zero();
                    m_current_length = 0;
                    for (unsigned i = m_next_edge; i < m_next_edge + num_edges; ++i) {
                        edge_id id = (i >= num_edges) ? i - num_edges : i;
                        node src = m_graph.get_source(id);
                        node tgt = m_graph.get_target(id);
                        if (m_states[id] != BASIS) {
                            numeral cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(id);
                            if (cost.is_pos()) {
                                m_candidates[m_current_length] = id;
                                ++m_current_length;
                                if (cost > max) {
                                    max = cost;
                                    m_enter_id = id;
                                }
                            }
                            if (m_current_length >= m_num_candidates) break;
                        }
                    }
                    m_next_edge = m_enter_id;
                    m_minor_step = 1;
                    if (max.is_pos()) {
                        TRACE("network_flow", {
                            tout << "Found entering edge " << m_enter_id << " between node ";
                            tout << m_graph.get_source(m_enter_id) << " and node " << m_graph.get_target(m_enter_id);
                            tout << " with reduced cost = " << max << "...\n";
                        });
                        return true;
                    }
                    TRACE("network_flow", tout << "Found no entering edge...\n";);
                    return false;
                }

                ++m_minor_step;
                numeral max = numeral::zero();
                for (unsigned i = 0; i < m_current_length; ++i) {
                    edge_id id = m_candidates[i];
                    node src = m_graph.get_source(id);
                    node tgt = m_graph.get_target(id);
                    if (m_states[id] != BASIS) {
                        numeral cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(id);
                        if (cost > max) {
                            max = cost;
                            m_enter_id = id;
                        }
                        // Remove stale candidates
                        if (!cost.is_pos()) {
                            --m_current_length;
                            m_candidates[i] = m_candidates[m_current_length];
                            --i;
                        }
                    }
                }
                if (max.is_pos()) {
                    TRACE("network_flow", {
                        tout << "Found entering edge " << m_enter_id << " between node ";
                        tout << m_graph.get_source(m_enter_id) << " and node " << m_graph.get_target(m_enter_id);
                        tout << " with reduced cost = " << max << "...\n";
                    });
                    return true;
                }
                TRACE("network_flow", tout << "Found no entering edge...\n";);
                return false;
            };
        };
        
        graph m_graph;
        spanning_tree_base * m_tree;

        // Denote supply/demand b_i on node i
        vector<fin_numeral> m_balances;

        // Duals of flows which are convenient to compute dual solutions
        vector<numeral> m_potentials;

        // Basic feasible flows
        vector<numeral> m_flows;
        
        svector<edge_state> m_states;

        unsigned m_step;

        edge_id m_enter_id, m_leave_id;
        optional<numeral> m_delta;

        // Initialize the network with a feasible spanning tree
        void initialize();

        void update_potentials();

        void update_flows();
            
        bool choose_entering_edge(pivot_rule pr);

        // Send as much flow as possible around the cycle, the first basic edge with flow 0 will leave
        // Return false if the problem is unbounded
        bool choose_leaving_edge();

        void update_spanning_tree();

        std::string display_spanning_tree();

        bool edge_in_tree(edge_id id) const;

        bool check_well_formed();
        bool check_optimal();

    public:

        network_flow(graph & g, vector<fin_numeral> const & balances);        
        
        // Minimize cost flows
        // Return true if found an optimal solution, and return false if unbounded
        bool min_cost(pivot_rule pr = FIRST_ELIGIBLE);

        // Compute the optimal solution
        numeral get_optimal_solution(vector<numeral> & result, bool is_dual);

    };
}

#endif

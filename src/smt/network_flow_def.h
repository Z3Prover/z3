/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    network_flow_def.h

Abstract:

    Implements Network Simplex algorithm for min cost flow problem

Author:

    Anh-Dung Phan (t-anphan) 2013-10-24

Notes:
   
--*/

#ifndef _NETWORK_FLOW_DEF_H_
#define _NETWORK_FLOW_DEF_H_

#include"network_flow.h"

namespace smt {

    template<typename Ext>
    network_flow<Ext>::network_flow(graph & g, vector<fin_numeral> const& balances) :
        m_graph(g),
        m_balances(balances) {
        unsigned num_nodes = m_balances.size() + 1;
        unsigned num_edges = m_graph.get_num_edges();

        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < num_edges; ++i) {
            fin_numeral cost(es[i].get_weight().get_rational());
            m_costs.push_back(cost);
        }

        m_balances.resize(num_nodes);
        for (unsigned i = 0; i < balances.size(); ++i) {
            m_costs.push_back(balances[i]);
        }

        m_potentials.resize(num_nodes);
        m_costs.resize(num_edges);
        m_flows.resize(num_edges);
        m_states.resize(num_edges);

        m_upwards.resize(num_nodes);
        m_pred.resize(num_nodes);
        m_depth.resize(num_nodes);
        m_thread.resize(num_nodes);
        m_rev_thread.resize(num_nodes);
        m_final.resize(num_nodes);
        m_num_node.resize(num_nodes);
    }

    template<typename Ext>
    void network_flow<Ext>::initialize() {
        // Create an artificial root node to construct initial spanning tree
        unsigned num_nodes = m_balances.size();
        unsigned num_edges = m_graph.get_num_edges();
        node root = num_nodes;
        m_pred[root] = -1;
        m_thread[root] = 0;
        m_rev_thread[0] = root;
        m_num_node[root] = num_nodes + 1;
        m_final[root] = root - 1;
        m_potentials[root] = numeral::zero();

        fin_numeral sum_supply = fin_numeral::zero();
        for (unsigned i = 0; i < m_balances.size(); ++i) {
            sum_supply += m_balances[i];
        }        
        m_balances[root] = -sum_supply;

        m_states.resize(num_nodes + num_edges);
        m_states.fill(NON_BASIS);

        // Create artificial edges and initialize the spanning tree
        for (unsigned i = 0; i < num_nodes; ++i) {
            m_upwards[i] = m_balances[i] >= fin_numeral::zero();
            m_pred[i] = root;
            m_depth[i] = 1;
            m_thread[i] = i + 1;
            m_final[i] = i;
            m_rev_thread[i] = (i = 0) ? root : i - 1;
            m_num_node[i] = 1;
            m_states[num_edges + i] = BASIS;
        }
    }

    template<typename Ext>
    void network_flow<Ext>::update_potentials() {
        node src = m_graph.get_source(m_entering_edge);
        node tgt = m_graph.get_source(m_entering_edge);
        numeral cost = m_graph.get_weight(m_entering_edge);
        numeral change = m_upwards[src] ? (cost - m_potentials[src] + m_potentials[tgt]) : 
                            (-cost + m_potentials[src] - m_potentials[tgt]);
        node last = m_thread[m_final[src]];
        for (node u = src; u != last; u = m_thread[u]) {
            m_potentials[u] += change;
        }
    }

    template<typename Ext>
    void network_flow<Ext>::update_flows() {
        numeral val = m_state[m_entering_edge] == NON_BASIS ? numeral::zero() : m_delta;
        m_flows[m_entering_edge] += val;
        for (unsigned u = m_graph.get_source(m_entering_edge); u != m_join_node; u = m_pred[u]) {
            edge_id e_id;
            m_graph.get_edge_id(u, m_pred[u], e_id);
            m_flows[e_id] += m_upwards[u] ? -val : val;
        }
        for (unsigned u = m_graph.get_target(m_entering_edge); u != m_join_node; u = m_pred[u]) {
            edge_id e_id;
            m_graph.get_edge_id(u, m_pred[u], e_id);
            m_flows[e_id] += m_upwards[u] ? val : -val;
        }
    }
    
    template<typename Ext>
    bool network_flow<Ext>::choose_entering_edge() {
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned int i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            edge_id e_id;
            if (e.is_enabled() && m_graph.get_edge_id(e.get_source(), e.get_target(), e_id) && m_states[e_id] == BASIS) {
                node source   = e.get_source();
                node target   = e.get_target();
                numeral cost  = e.get_weight() - m_potentials[source] + m_potentials[target];
                // Choose the first negative-cost edge to be the violating edge
                // TODO: add multiple pivoting strategies
                if (cost < numeral::zero()) {
                    m_entering_edge = e_id;
                    return true;
                }
            }
        }
        return false;
    }

    template<typename Ext>
    bool network_flow<Ext>::choose_leaving_edge() {
        node source = m_graph.get_source(m_entering_edge);
        node target = m_graph.get_target(m_entering_edge);
        node u = source, v = target;
        while (u != v) {
            if (m_depth[u] > m_depth[v])
                u = m_pred[u];
            else if (m_depth[u] < m_depth[v])
                v = m_pred[v];
            else {
                u = m_pred[u];
                v = m_pred[v];
            }
        }
        // Found first common ancestor of source and target
        m_join_node = u;
        // FIXME: need to get truly finite value
        numeral infty = numeral(INT_MAX);
        m_delta = infty;
        node src, tgt;
        // Send flows along the path from source to the ancestor
        for (unsigned u = source; u != m_join_node; u = m_pred[u]) {
            edge_id e_id;
            m_graph.get_edge_id(u, m_pred[u], e_id);
            numeral d = m_upwards[u] ? m_flows[e_id] : infty;
            if (d < m_delta) {
                m_delta = d;
                src = u;
                tgt = m_pred[u];
            }
        }

        // Send flows along the path from target to the ancestor
        for (unsigned u = target; u != m_join_node; u = m_pred[u]) {
            edge_id e_id;
            m_graph.get_edge_id(u, m_pred[u], e_id);
            numeral d = m_upwards[u] ? infty : m_flows[e_id];
            if (d <= m_delta) {
                m_delta = d;
                src = u;
                tgt = m_pred[u];
            }
        }

        if (m_delta < infty) {
            m_graph.get_edge_id(src, tgt, m_leaving_edge);
            return true;
        }
        return false;
    }

    template<typename Ext>
    void network_flow<Ext>::update_spanning_tree() {

    }

    // Get the optimal solution
    template<typename Ext>
    typename network_flow<Ext>::numeral network_flow<Ext>::get_optimal_solution(vector<numeral> & result, bool is_dual) {
        m_objective_value = numeral::zero();
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            m_objective_value += m_costs[i] * m_flows[i];
        }
        result.reset();
        if (is_dual) {            
            result.append(m_potentials);                   
        }
        else {
            result.append(m_flows);     
        }
        return m_objective_value;
    }

    // Minimize cost flows
    // Return true if found an optimal solution, and return false if unbounded
    template<typename Ext>
    bool network_flow<Ext>::min_cost() {
        initialize();
        while (choose_entering_edge()) {
            bool bounded = choose_leaving_edge();
            if (!bounded) return false;
            if (m_entering_edge != m_leaving_edge) {
                m_states[m_entering_edge] = BASIS;
                m_states[m_leaving_edge] = NON_BASIS;
                update_spanning_tree();
                update_potentials();
            }
        }
        return true;
    }
}

#endif

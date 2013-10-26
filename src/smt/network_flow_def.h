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
    network_flow<Ext>::network_flow(graph & g, vector<fin_numeral> const& costs) :
        m_graph(g),
        m_costs(costs) {
    }

    template<typename Ext>
    void network_flow<Ext>::initialize() {
        // TODO: construct an initial spanning tree i.e. inializing m_pred, m_depth and m_thread.
        compute_potentials();
        compute_flows();
    }

    template<typename Ext>
    void network_flow<Ext>::compute_potentials() {
        SASSERT(!m_potentials.empty());
        SASSERT(!m_thread.empty());
        SASSERT(m_thread.size() == m_pred.size());
        
        m_potentials.set(0, numeral::zero());
        node target = m_thread[0];
        
        while (target != 0) {
            node source = m_pred[target];
            edge_id e_id;
            if (m_graph.get_edge_id(source, target, e_id)) {
                m_potentials.set(target, m_potentials[source] - m_graph.get_weight(e_id));
            }
            if (m_graph.get_edge_id(target, source, e_id)) {
                m_potentials.set(target, m_potentials[source] + m_graph.get_weight(e_id));
            }
            target = m_thread[target];
        }
    }

    template<typename Ext>
    void network_flow<Ext>::compute_flows() {
        vector<numeral> balances(m_balances);
        
        // OPTIMIZE: Need a set data structure for efficiently removing elements
        vector<edge_id> basics;
        while (!basics.empty()) {
            // Find a leaf node of a spanning tree
            node target;
            for (unsigned int i = 0; i < m_thread.size(); ++i) {
                if (m_depth[i] <= m_depth[m_thread[i]]) {
                    target = i;
                    break;
                }
            }
            node source = m_pred[target];
            edge_id e_id;
            if (m_graph.get_edge_id(source, target, e_id)) {
                m_flows.set(e_id, -m_graph.get_weight(basics[target]));
                basics[source] += basics[target];
                basics.erase(e_id);
            }
            else if (m_graph.get_edge_id(target, source, e_id)) {
                m_flows.set(e_id, m_graph.get_weight(basics[target]));
                basics[source] += basics[target];
                basics.erase(e_id);
            }
        }
    }
    
    template<typename Ext>
    bool network_flow<Ext>::is_optimal(edge_id & violating_edge) {    
        // TODO: how to get nonbasics vector?
        vector<edge> nonbasics;
        typename vector<edge>::iterator it  = nonbasics.begin();
        typename vector<edge>::iterator end = nonbasics.end();
        bool found = false;
        for (unsigned int i = 0; i < nonbasics.size(); ++i) {
            edge & e = nonbasics[i];
            if (e.is_enabled()) {
                node source   = e.get_source();
                node target   = e.get_target();
                numeral cost  = e.get_weight() - m_potentials[source] + m_potentials[target];
                // Choose the first negative-cost edge to be the violating edge
                // TODO: add multiple pivoting strategies
                numeral zero(0);
                if (cost < zero) {
                    edge_id e_id;
                    m_graph.get_edge_id(source, target, e_id);
                    violating_edge = e_id;
                    found = true;
                    break;
                }
            }
        }
        return !found;
    }

    template<typename Ext>
    edge_id network_flow<Ext>::choose_leaving_edge(edge_id entering_edge) {
        node source = m_graph.get_source(entering_edge);
        node target = m_graph.get_target(entering_edge);
        while (source != target) {
            if (m_depth[source] > m_depth[target])
                source = m_pred[source];
            else if (m_depth[source] < m_depth[target])
                target = m_pred[target];
            else {
                source = m_pred[source];
                target = m_pred[target];
            }
        }
        edge_id e_id;
        m_graph.get_edge_id(source, target, e_id);
        return e_id;
    }

    template<typename Ext>
    void network_flow<Ext>::update_spanning_tree(edge_id entering_edge, edge_id leaving_edge) {
        // Need special handling in case two edges are identical
        SASSERT(entering_edge != leaving_edge);
        
        // Update potentials
        node target = m_upwards[leaving_edge] ? m_graph.get_source(leaving_edge) : m_graph.get_target(leaving_edge);
        numeral src_pot = m_potentials[m_graph.get_source(entering_edge)];
        numeral tgt_pot = m_potentials[m_graph.get_target(entering_edge)];
        numeral weight = m_graph.get_weight(entering_edge);
        numeral change = m_upwards[entering_edge] ? (weight - src_pot + tgt_pot) : (-weight + src_pot - tgt_pot);
        m_potentials[target] += change;
        node start = m_thread[target];
        while (m_depth[start] > m_depth[target]) {
            m_potentials[start] += change;
            start = m_thread[start];
        }
    }

    template<typename Ext>
    bool network_flow<Ext>::is_unbounded() {
        return false;
    }

    // Get the optimal solution
    template<typename Ext>
    void network_flow<Ext>::get_optimal_solution(numeral & objective, vector<numeral> & flows) {
        SASSERT(m_is_optimal);
        flows.reset();
        flows.append(m_flows);
        numeral cost(0);
        for (unsigned int i = 0; i < m_flows.size(); ++i) {
            // FIXME: this * operator is not supported
            cost += m_costs[i] * m_flows[i];
        }
        objective = cost;
    }

    // Minimize cost flows
    // Return true if found an optimal solution, and return false if unbounded
    template<typename Ext>
    bool network_flow<Ext>::min_cost() {
        SASSERT(!m_graph.get_all_edges().empty());
        initialize();
        edge_id entering_edge;
        while (!is_optimal(entering_edge)) {
            edge_id leaving_edge = choose_leaving_edge(entering_edge);
            update_spanning_tree(entering_edge, leaving_edge);
            if (is_unbounded()) {
                m_is_optimal = false;
                return m_is_optimal;
            }
        }
        m_is_optimal = true;
        return m_is_optimal;
    }
}

#endif

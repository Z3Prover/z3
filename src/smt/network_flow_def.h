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

        array<rational, m_potentials.size()> potentials;
        std::copy(m_potentials.begin(), m_potentials.end(), potentials);
        rational zero(0);
        potentials[0] = zero;
        node next = m_thread[0];
        
        while (next != 0) {
            node current = m_pred[next];
            edge e;
            if (m_graph.get_edge(current, next, e)) {
                potentials[next] = potentials[current] - e.get_weight();
            }
            if (m_graph.get_edge(next, current, e)) {
                potentials[next] = potentials[current] + e.get_weight();
            }
            next = m_thread[next];
        }
        std::copy(potentials.begin(), potentials.end(), m_potentials);
    }

    template<typename Ext>
    void network_flow<Ext>::compute_flows() {
        vector<numeral> balances(m_balances);
        numeral zero;
        m_flows.fill(zero);
        vector<edge> basics(m_basics);
        // TODO: need a way to find a leaf node of a spanning tree
        while (!basics.empty()) {
            return;
        }
    }
    
    template<typename Ext>
    bool network_flow<Ext>::is_optimal(edge & violating_edge) {        
        typename vector<edge>::iterator it  = m_nonbasics.begin();
        typename vector<edge>::iterator end = m_nonbasics.end();
        bool found = false;
        for (unsigned int i = 0; i < m_nonbasics.size(); ++i) {
            edge & e = m_nonbasics[i];
            if (e.is_enabled()) {
                node source   = e.get_source();
                node target   = e.get_target();
                numeral cost  = e.get_weight() - m_potentials[source] + m_potentials[target];
                // Choose the first negative-cost edge to be the violating edge
                // TODO: add multiple pivoting strategies
                if (cost < 0) {
                    violating_edge = e;
                    found = true;
                    break;
                }
            }
        }
        return !found;
    }

    template<typename Ext>
    dl_edge<typename network_flow<Ext>::GExt> network_flow<Ext>::choose_leaving_edge(const edge & entering_edge) {
        node source = entering_edge.get_source();
        node target = entering_edge.get_target();
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
        edge e;
        m_graph.get_edge(source, target, e);
        return e;
    }

    template<typename Ext>
    void network_flow<Ext>::update_basics(const edge & entering_edge, const edge & leaving_edge) {

    }

    template<typename Ext>
    bool network_flow<Ext>::is_unbounded() {
        return false;
    }

    // Get the optimal solution
    template<typename Ext>
    void network_flow<Ext>::get_optimal_solution(numeral & objective, vector<numeral> & flows) {
        flows.reset();
        flows.append(m_flows);
        // TODO: calculate objective value
    }

    // Minimize cost flows
    // Return true if found an optimal solution, and return false if unbounded
    template<typename Ext>
    bool network_flow<Ext>::min_cost() {
        initialize();
        edge & entering_edge;
        while (!is_optimal(entering_edge)) {
            edge & leaving_edge = choose_leaving_edge();
            update_tree(entering_edge, leaving_edge);
            if (is_unbounded())
                return false;
        }
        return true;
    }
}

#endif

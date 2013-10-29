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
    network_flow<Ext>::network_flow(graph & g, vector<fin_numeral> const & balances) :
        m_graph(g),
        m_balances(balances) {
        unsigned num_nodes = m_graph.get_num_nodes() + 1;
        unsigned num_edges = m_graph.get_num_edges();

        m_balances.resize(num_nodes);

        m_potentials.resize(num_nodes);        
        m_flows.resize(num_edges);
        m_states.resize(num_edges);

        m_upwards.resize(num_nodes);
        m_pred.resize(num_nodes);
        m_depth.resize(num_nodes);
        m_thread.resize(num_nodes);
        m_rev_thread.resize(num_nodes);
        m_final.resize(num_nodes);
    }

    template<typename Ext>
    void network_flow<Ext>::initialize() {
        TRACE("network_flow", tout << "initialize...\n";);
        // Create an artificial root node to construct initial spanning tree
        unsigned num_nodes = m_graph.get_num_nodes();
        unsigned num_edges = m_graph.get_num_edges();
        node root = num_nodes;
        m_pred[root] = -1;
        m_thread[root] = 0;
        m_rev_thread[0] = root;
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
            m_rev_thread[i] = (i == 0) ? root : i - 1;
            m_states[num_edges + i] = BASIS;
        }

        TRACE("network_flow", tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread) 
                                   << pp_vector("Reverse Threads", m_rev_thread) << pp_vector("Last Successors", m_final) << pp_vector("Depths", m_depth););
    }

    template<typename Ext>
    void network_flow<Ext>::update_potentials() {
        TRACE("network_flow", tout << "update_potentials...\n";);
        node src = m_graph.get_source(m_entering_edge);
        node tgt = m_graph.get_source(m_entering_edge);
        numeral cost = m_graph.get_weight(m_entering_edge);
        numeral change = m_upwards[src] ? (cost - m_potentials[src] + m_potentials[tgt]) : 
                            (-cost + m_potentials[src] - m_potentials[tgt]);
        node last = m_thread[m_final[src]];
        for (node u = src; u != last; u = m_thread[u]) {
            m_potentials[u] += change;
        }
        TRACE("network_flow", tout << pp_vector("Potentials", m_potentials, true););
    }

    template<typename Ext>
    void network_flow<Ext>::update_flows() {
        TRACE("network_flow", tout << "update_flows...\n";);
        numeral val = m_state[m_entering_edge] == NON_BASIS ? numeral::zero() : m_delta;
        m_flows[m_entering_edge] += val;
        node source = m_graph.get_source(m_entering_edge);
        for (unsigned u = source; u != m_join_node; u = m_pred[u]) {
            edge_id e_id;
            m_graph.get_edge_id(u, m_pred[u], e_id);
            m_flows[e_id] += m_upwards[u] ? -val : val;
        }
        node target = m_graph.get_target(m_entering_edge);
        for (unsigned u = target; u != m_join_node; u = m_pred[u]) {
            edge_id e_id;
            m_graph.get_edge_id(u, m_pred[u], e_id);
            m_flows[e_id] += m_upwards[u] ? val : -val;
        }
        TRACE("network_flow", tout << pp_vector("Flows", m_flows, true););
    }
    
    template<typename Ext>
    bool network_flow<Ext>::choose_entering_edge() {
        TRACE("network_flow", tout << "choose_entering_edge...\n";);
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned int i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            edge_id e_id;
            if (e.is_enabled() && m_graph.get_edge_id(e.get_source(), e.get_target(), e_id) && m_states[e_id] == NON_BASIS) {
                node source   = e.get_source();
                node target   = e.get_target();
                numeral cost  = e.get_weight() - m_potentials[source] + m_potentials[target];
                // Choose the first negative-cost edge to be the violating edge
                // TODO: add multiple pivoting strategies
                if (cost < numeral::zero()) {
                    m_entering_edge = e_id;
                    TRACE("network_flow", tout << "Found entering edge " << e_id << " between node " << source << " and node " << target << "...\n";);
                    return true;
                }
            }
        }
        TRACE("network_flow", tout << "Found no entering edge... It's probably optimal.\n";);
        return false;
    }

    template<typename Ext>
    bool network_flow<Ext>::choose_leaving_edge() {
        TRACE("network_flow", tout << "choose_leaving_edge...\n";);
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
        // FIXME: need to get truly infinite value
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
            TRACE("network_flow", tout << "Found leaving edge" << m_leaving_edge << "between node " << src << " and node " << tgt << "...\n";);
            return true;
        }
        TRACE("network_flow", tout << "Can't find a leaving edge... The problem is unbounded.\n";);
        return false;
    }

    template<typename Ext>
    void network_flow<Ext>::update_spanning_tree() {        
        node src_in = m_graph.get_source(m_entering_edge);
        node tgt_in = m_graph.get_target(m_entering_edge);
        node src_out = m_graph.get_source(m_leaving_edge);
        node tgt_out = m_graph.get_target(m_leaving_edge);
        TRACE("network_flow", tout << "update_spanning_tree: (" << src_in << ", " << tgt_in << ") enters, (" 
                                   << src_out << ", " << tgt_out << ") leaves\n";);
        node root = m_graph.get_num_nodes();

        node rev_thread_out = m_rev_thread[src_out];
        
        node x = m_final[src_in];
        node y = m_thread[x];
        node z = m_final[src_out];

        // Update m_pred (for nodes in the stem from tgt_in to tgt_out)
        node u = tgt_in;
        node last = m_pred[tgt_out];
        node parent = src_in;
        while (u != last) {
            node next = m_pred[u];  
            m_pred[u] = parent;
            u = next;
        }

        // Graft T_q and T_r'
        m_thread[x] = src_out;
        m_thread[z] = y;
        u = src_out;
        while (u != m_final[src_out]) {
            m_depth[u] += 1 + m_depth[src_in];
            u = m_pred[u];
        }

        node gamma = m_thread[m_final[src_in]];
        last = m_pred[gamma] != 0 ? gamma : root;
        for (node u = src_in; u == last; u = m_pred[u]) {
            m_final[u] = z;
        }

        // Update T_r'
        node phi = m_thread[tgt_out];
        node theta = m_thread[m_final[tgt_out]];
        m_thread[phi] = theta;

        gamma = m_thread[m_final[tgt_out]];
        // REVIEW: check f(u) is not in T_v
        node delta = m_final[src_out] != m_final[tgt_out] ? m_final[src_out] : m_rev_thread[tgt_out];
        last = m_pred[gamma] != 0 ? gamma : root;
        for (node u = src_in; u == last; u = m_pred[u]) {
            m_final[u] = delta;
        }

        // Reroot T_v at q
        if (src_out != tgt_in) {
            node u = m_pred[src_out];
            m_thread[m_final[src_out]] = u;
            last = tgt_in;            
            node alpha1, alpha2;
            unsigned count = 0;
            while (u != last) {
                // Find all immediate successors of u
                node t1 = m_thread[u];
                node t2 = m_thread[m_final[t1]];
                node t3 = m_thread[m_final[t2]];
                if (t1 = m_pred[u]) {
                    alpha1 = t2;
                    alpha2 = t3;
                }
                else if (t2 = m_pred[u]) {
                    alpha1 = t1;
                    alpha2 = t3;
                }
                else {
                    alpha1 = t1;
                    alpha2 = t2;
                }                
                m_thread[u] = alpha1;
                m_thread[m_final[alpha1]] = alpha2;
                u = m_pred[u];
                m_thread[m_final[alpha2]] = u;
                // Decrease depth of all children in the subtree
                ++count;
                int d = m_depth[u] - count;
                for (node v = m_thread[u]; v == m_final[u]; v = m_thread[v]) {
                    m_depth[v] -= d;
                }
            }
            m_thread[m_final[alpha2]] = src_out;
        }

        TRACE("network_flow", tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread) 
                                   << pp_vector("Reverse Threads", m_rev_thread) << pp_vector("Last Successors", m_final) << pp_vector("Depths", m_depth););
    }     

    template<typename Ext>
    std::string network_flow<Ext>::pp_vector(std::string const & label, svector<int> v, bool has_header) {
        std::ostringstream oss;
        if (has_header) {
            oss << "Index ";
            for (unsigned i = 0; i < v.size(); ++i) {
                oss << i << " ";
            }
            oss << std::endl;
        }
        oss << label << " ";
        for (unsigned i = 0; i < v.size(); ++i) {
            oss << v[i] << " ";
        }
        oss << std::endl;
        return oss.str();
    }

    template<typename Ext>
    std::string network_flow<Ext>::pp_vector(std::string const & label, vector<numeral> v, bool has_header) {
        std::ostringstream oss;
        if (has_header) {
            oss << "Index ";
            for (unsigned i = 0; i < v.size(); ++i) {
                oss << i << " ";
            }
            oss << std::endl;
        }
        oss << label << " ";
        for (unsigned i = 0; i < v.size(); ++i) {
            oss << v[i] << " ";
        }
        oss << std::endl;
        return oss.str();
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

    // Get the optimal solution
    template<typename Ext>
    typename network_flow<Ext>::numeral network_flow<Ext>::get_optimal_solution(vector<numeral> & result, bool is_dual) {
        m_objective_value = numeral::zero();
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            fin_numeral cost = m_graph.get_weight(i).get_rational();
            m_objective_value += cost * m_flows[i];
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
}

#endif

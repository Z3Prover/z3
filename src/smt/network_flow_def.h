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

    template<typename TV>
    std::string pp_vector(std::string const & label, TV v, bool has_header) {
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
    network_flow<Ext>::network_flow(graph & g, vector<fin_numeral> const & balances) :
        m_graph(g),
        m_balances(balances) {
        unsigned num_nodes = m_graph.get_num_nodes() + 1;
        unsigned num_edges = m_graph.get_num_edges();

        m_balances.resize(num_nodes);
        m_potentials.resize(num_nodes);                        

        m_upwards.resize(num_nodes);
        m_pred.resize(num_nodes);
        m_depth.resize(num_nodes);
        m_thread.resize(num_nodes);
        m_rev_thread.resize(num_nodes);
        m_final.resize(num_nodes);

        m_step = 0;
    }

    template<typename Ext>
    void network_flow<Ext>::initialize() {
        TRACE("network_flow", tout << "initialize...\n";);
        // Create an artificial root node to construct initial spanning tree
        unsigned num_nodes = m_graph.get_num_nodes();
        unsigned num_edges = m_graph.get_num_edges();
        node root = num_nodes;
        m_pred[root] = -1;
        m_depth[root] = 0;
        m_thread[root] = 0;
        m_rev_thread[0] = root;
        m_final[root] = root - 1;
        m_potentials[root] = numeral::zero();

        m_graph.init_var(root);

        fin_numeral sum_supply = fin_numeral::zero();
        for (unsigned i = 0; i < m_balances.size(); ++i) {
            sum_supply += m_balances[i];
        }        
        m_balances[root] = -sum_supply;

        m_flows.resize(num_nodes + num_edges);
        m_states.resize(num_nodes + num_edges);
        m_states.fill(NON_BASIS);

        // Create artificial edges and initialize the spanning tree
        for (unsigned i = 0; i < num_nodes; ++i) {
            m_upwards[i] = !m_balances[i].is_neg();
            m_pred[i] = root;
            m_depth[i] = 1;
            m_thread[i] = i + 1;
            m_final[i] = i;
            m_rev_thread[i + 1] = i;
            m_states[num_edges + i] = BASIS;
            node src = m_upwards[i] ? i : root;
            node tgt = m_upwards[i] ? root : i;            
            m_flows[num_edges + i] = m_upwards[i] ? m_balances[i] : -m_balances[i];
            m_graph.enable_edge(m_graph.add_edge(src, tgt, numeral::one(), explanation()));
        }

        // Compute initial potentials
        node u = m_thread[root];
        while (u != root) {
            node v = m_pred[u];   
            edge_id e_id = get_edge_id(u, v);
            if (m_upwards[u]) {
                m_potentials[u] = m_potentials[v] - m_graph.get_weight(e_id);
            }
            else {
                m_potentials[u] = m_potentials[v] + m_graph.get_weight(e_id);
            }
            u = m_thread[u];
        }

        TRACE("network_flow", {
                tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
                tout << pp_vector("Reverse Threads", m_rev_thread) << pp_vector("Last Successors", m_final);
                tout << pp_vector("Depths", m_depth) << pp_vector("Upwards", m_upwards);
                tout << pp_vector("Potentials", m_potentials) << pp_vector("Flows", m_flows);
            });
        TRACE("network_flow", tout << "Spanning tree:\n" << display_spanning_tree(););
    }

    template<typename Ext>
    edge_id network_flow<Ext>::get_edge_id(dl_var source, dl_var target) {
        // m_upwards[source] decides which node is the real source
        edge_id id;
        VERIFY(m_upwards[source] ? m_graph.get_edge_id(source, target, id) : m_graph.get_edge_id(target, source, id));
        return id;
    }

    template<typename Ext>
    void network_flow<Ext>::update_potentials() {
        TRACE("network_flow", tout << "update_potentials...\n";);
        node src = m_graph.get_source(m_entering_edge);
        node tgt = m_graph.get_target(m_entering_edge); 
        numeral cost = m_graph.get_weight(m_entering_edge);
        numeral change = m_upwards[src] ? (-cost + m_potentials[src] - m_potentials[tgt]) : (cost - m_potentials[src] + m_potentials[tgt]);
        node last = m_thread[m_final[src]];
        for (node u = src; u != last; u = m_thread[u]) {
            m_potentials[u] += change;
        }
        TRACE("network_flow", tout << pp_vector("Potentials", m_potentials, true););
    }

    template<typename Ext>
    void network_flow<Ext>::update_flows() {
        TRACE("network_flow", tout << "update_flows...\n";);
        numeral val = m_states[m_entering_edge] == BASIS ? numeral::zero() : m_delta;
        m_flows[m_entering_edge] += val;
        node source = m_graph.get_source(m_entering_edge);
        for (unsigned u = source; u != m_join_node; u = m_pred[u]) {
            edge_id e_id = get_edge_id(u, m_pred[u]);
            m_flows[e_id] += m_upwards[u] ? -val : val;
        }
        node target = m_graph.get_target(m_entering_edge);
        for (unsigned u = target; u != m_join_node; u = m_pred[u]) {
            edge_id e_id = get_edge_id(u, m_pred[u]);
            m_flows[e_id] += m_upwards[u] ? val : -val;
            TRACE("network_flow", tout << u << ", " << m_pred[u] << ", " << e_id << ", " << m_upwards[u] << ", " << val;);
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
            node source   = e.get_source();
            node target   = e.get_target();
            if (e.is_enabled() && m_graph.get_edge_id(source, target, e_id) && m_states[e_id] == NON_BASIS) {
                numeral cost  = e.get_weight() - m_potentials[source] + m_potentials[target];
                // Choose the first negative-cost edge to be the violating edge
                // TODO: add multiple pivoting strategies
                if (cost.is_neg()) {
                    m_entering_edge = e_id;
                    TRACE("network_flow", {
                        tout << "Found entering edge " << e_id << " between node ";
                        tout << source << " and node " << target << "...\n";
                    });
                    return true;
                }
            }
        }
        TRACE("network_flow", tout << "Found no entering edge...\n";);
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
        TRACE("network_flow", tout << "Found join node " << m_join_node << std::endl;);
        // FIXME: need to get truly infinite value
        numeral infty = numeral(INT_MAX);
        m_delta = infty; 
        node src, tgt;
        // Send flows along the path from source to the ancestor
        for (unsigned u = source; u != m_join_node; u = m_pred[u]) {
            edge_id e_id = get_edge_id(u, m_pred[u]);
            numeral d = m_upwards[u] ? infty : m_flows[e_id];
            if (d < m_delta) {
                m_delta = d;
                src = u;
                tgt = m_pred[u];
            }
        }

        // Send flows along the path from target to the ancestor
        for (unsigned u = target; u != m_join_node; u = m_pred[u]) {
            edge_id e_id = get_edge_id(u, m_pred[u]);
            numeral d = m_upwards[u] ? m_flows[e_id] : infty;
            if (d <= m_delta) {
                m_delta = d;
                src = u;
                tgt = m_pred[u];
            }
        }

        if (m_delta < infty) {
            m_leaving_edge = get_edge_id(src, tgt);
            TRACE("network_flow", { 
                tout << "Found leaving edge " << m_leaving_edge;
                tout << " between node " << src << " and node " << tgt << "...\n";
                });
            return true;
        }
        TRACE("network_flow", tout << "Can't find a leaving edge... The problem is unbounded.\n";);
        return false;
    }

    template<typename Ext>
    void network_flow<Ext>::update_spanning_tree() {        
        node p = m_graph.get_source(m_entering_edge);
        node q = m_graph.get_target(m_entering_edge);
        node u = m_graph.get_source(m_leaving_edge);
        node v = m_graph.get_target(m_leaving_edge);

        TRACE("network_flow", { 
            tout << "update_spanning_tree: (" << p << ", " << q << ") enters, (";
            tout << u << ", " << v << ") leaves\n";
        });

        node x = m_final[p];
        node y = m_thread[x];
        node z = m_final[q];

        // Update m_pred (for nodes in the stem from q to v)
        node n = q;
        node last = m_pred[v];
        node parent = p;
        while (n != last) {
            node next = m_pred[n];  
            m_pred[n] = parent;
            m_upwards[n] = !m_upwards[n];
            parent = n;
            n = next;
        }

        TRACE("network_flow", tout << "Graft T_q and T_r'\n";);

        // Graft T_q and T_r'
        m_thread[x] = q;
        m_thread[z] = y;
        n = u;
        last = m_final[u];
        while (n != last) {
            m_depth[n] += 1 + m_depth[p];
            n = m_pred[n];
        }

        node gamma = m_thread[m_final[p]];        
        n = p;
        last = m_pred[gamma];
        while (n != last) {
            m_final[n] = z;
            n = m_pred[n];
        }

        TRACE("network_flow", tout << "Update T_r'\n";);

        // Update T_r'
        node phi = m_rev_thread[v];
        node theta = m_thread[m_final[v]];
        m_thread[phi] = theta;

        gamma = m_thread[m_final[v]];
        // REVIEW: check f(n) is not in T_v
        node delta = m_final[u] != m_final[v] ? m_final[u] : phi;
        n = u;
        last = m_pred[gamma];
        while (n != last) {
            m_final[n] = delta;
            n = m_pred[n];
        }

        // Reroot T_v at q
        if (u != q) {
            TRACE("network_flow", tout << "Reroot T_v at q\n";);

            node n = m_pred[q];
            m_thread[m_final[q]] = n;
            last = v;            
            node alpha1, alpha2;
            unsigned count = 0;
            while (n != last) {
                // Find all immediate successors of n
                node t1 = m_thread[n];
                node t2 = m_thread[m_final[t1]];
                node t3 = m_thread[m_final[t2]];
                if (t1 = m_pred[n]) {
                    alpha1 = t2;
                    alpha2 = t3;
                }
                else if (t2 == m_pred[n]) {
                    alpha1 = t1;
                    alpha2 = t3;
                }
                else {
                    alpha1 = t1;
                    alpha2 = t2;
                }                
                m_thread[n] = alpha1;
                m_thread[m_final[alpha1]] = alpha2;
                n = m_pred[n];
                m_thread[m_final[alpha2]] = n;
                // Decrease depth of all children in the subtree
                ++count;
                int d = m_depth[n] - count;
                for (node m = m_thread[n]; m != m_final[n]; m = m_thread[m]) {
                    m_depth[m] -= d;
                }
            }
            m_thread[m_final[alpha2]] = v;
        }

        TRACE("network_flow", {
            tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Reverse Threads", m_rev_thread) << pp_vector("Last Successors", m_final);
            tout << pp_vector("Depths", m_depth) << pp_vector("Upwards", m_upwards);
            });
    }

    template<typename Ext>
    std::string network_flow<Ext>::display_spanning_tree() {
        ++m_step;;
        std::ostringstream oss;
        std::string prefix = "T";
        prefix.append(std::to_string(m_step));
        prefix.append("_");
        unsigned root = m_graph.get_num_nodes() - 1;
        for (unsigned i = 0; i < root; ++i) {
            oss << prefix << i << "[shape=circle,label=\"" << prefix << i << " [" << m_potentials[i] << "]\"];\n";
        }
        oss << prefix << root << "[shape=doublecircle,label=\"" << prefix << root << " [" << m_potentials[root] << "]\"];\n";
        
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            if (e.is_enabled()) {
                oss << prefix << e.get_source() << " -> " << prefix << e.get_target();
                if (m_states[i] == BASIS) {
                    oss << "[color=red,penwidth=3.0,label=\"" << m_flows[i] << "\"];\n";
                }
                else {
                    oss << "[label=\"" << m_flows[i] << "\"];\n";
                }
            }
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
            update_flows();
            if (m_entering_edge != m_leaving_edge) {
                m_states[m_entering_edge] = BASIS;
                m_states[m_leaving_edge] = NON_BASIS;
                update_spanning_tree();
                update_potentials();                
                TRACE("network_flow", tout << "Spanning tree:\n" << display_spanning_tree(););
            }
        }
        TRACE("network_flow", tout << "Found optimal solution.\n";);
        return true;
    }

    // Get the optimal solution
    template<typename Ext>
    typename network_flow<Ext>::numeral network_flow<Ext>::get_optimal_solution(vector<numeral> & result, bool is_dual) {
        m_objective_value = numeral::zero();
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            if (e.is_enabled() && m_states[i] == BASIS) {
                m_objective_value += e.get_weight().get_rational() * m_flows[i];
            }
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

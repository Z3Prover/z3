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
        m_balances(balances) {
        // Network flow graph has the edges in the reversed order compared to constraint graph
        // We only take enabled edges from the original graph
        for (unsigned i = 0; i < g.get_num_nodes(); ++i) {
            m_graph.init_var(i);
        }
        vector<edge> const & es = g.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            if (e.is_enabled()) {
                m_graph.add_edge(e.get_target(), e.get_source(), e.get_weight(), explanation());
            }
        }
        
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
        m_flows.fill(numeral::zero());
        m_states.resize(num_nodes + num_edges);
        m_states.fill(LOWER);

        // Create artificial edges from/to root node to/from other nodes and initialize the spanning tree
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
            m_graph.add_edge(src, tgt, numeral::one(), explanation());
        }

        // Compute initial potentials
        node u = m_thread[root];
        while (u != root) {
            bool direction = m_upwards[u];
            node v = m_pred[u];   
            edge_id e_id = get_edge_id(u, v);            
            m_potentials[u] = m_potentials[v] + (m_upwards[u] ? - m_graph.get_weight(e_id) : m_graph.get_weight(e_id));
            u = m_thread[u];
        }

        TRACE("network_flow", {
                tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
                tout << pp_vector("Reverse Threads", m_rev_thread) << pp_vector("Last Successors", m_final);
                tout << pp_vector("Depths", m_depth) << pp_vector("Upwards", m_upwards);
                tout << pp_vector("Potentials", m_potentials) << pp_vector("Flows", m_flows);
            });
        TRACE("network_flow", tout << "Spanning tree:\n" << display_spanning_tree(););
        SASSERT(check_well_formed());
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
        numeral change = m_upwards[src] ? (-cost - m_potentials[src] + m_potentials[tgt]) : (cost + m_potentials[src] - m_potentials[tgt]);
        node last = m_thread[m_final[src]];
        for (node u = src; u != last; u = m_thread[u]) {
            m_potentials[u] += change;
        }
        TRACE("network_flow", tout << pp_vector("Potentials", m_potentials, true););
    }

    template<typename Ext>
    void network_flow<Ext>::update_flows() {
        TRACE("network_flow", tout << "update_flows...\n";);
        numeral val = fin_numeral(m_states[m_entering_edge]) * (*m_delta);
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
        }
        TRACE("network_flow", tout << pp_vector("Flows", m_flows, true););
    }
    
    template<typename Ext>
    bool network_flow<Ext>::choose_entering_edge() {
        TRACE("network_flow", tout << "choose_entering_edge...\n";);
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            node src = m_graph.get_source(i);
            node tgt = m_graph.get_target(i);
            if (m_states[i] != BASIS) {
                numeral change = fin_numeral(m_states[i]) * (m_graph.get_weight(i) + m_potentials[src] - m_potentials[tgt]);
                // Choose the first negative-cost edge to be the violating edge
                // TODO: add multiple pivoting strategies
                if (change.is_neg()) {
                    m_entering_edge = i;
                    TRACE("network_flow", {
                        tout << "Found entering edge " << i << " between node ";
                        tout << src << " and node " << tgt << "...\n";
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
        if (m_states[m_entering_edge] == UPPER) {
            node temp = source;
            source = target;
            target = temp;
        }
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
        m_delta.set_invalid();
        node src, tgt;
        // Send flows along the path from source to the ancestor
        for (unsigned u = source; u != m_join_node; u = m_pred[u]) {
            edge_id e_id = get_edge_id(u, m_pred[u]);            
            if (m_upwards[u] && (!m_delta || m_flows[e_id] < *m_delta)) {
                m_delta = m_flows[e_id];
                src = u;
                tgt = m_pred[u];
                m_in_edge_dir = true;
            }
        }

        // Send flows along the path from target to the ancestor
        for (unsigned u = target; u != m_join_node; u = m_pred[u]) {
            edge_id e_id = get_edge_id(u, m_pred[u]);
            if (!m_upwards[u] && (!m_delta || m_flows[e_id] <= *m_delta)) {
                m_delta = m_flows[e_id];
                src = u;
                tgt = m_pred[u];
                m_in_edge_dir = false;
            }
        }

        if (m_delta) {
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
        // v is parent of u so T_u does not contain root node
        if (m_pred[u] == v) {
            std::swap(u, v);
        }  

        for (node n = p; n != -1; n = m_pred[n]) {
            // q should be in T_v so swap p and q
            if (n == v) {
                std::swap(p, q);
                break;
            }
        }

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
        node prev = p;
        while (n != last && n != -1) {
            node next = m_pred[n];  
            m_pred[n] = prev;          
            m_upwards[n] = !m_upwards[prev];
            prev = n;
            n = next;
        }     

        TRACE("network_flow", tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Upwards", m_upwards););

        // Do this before updating data structures
        node gamma_p = m_pred[m_thread[m_final[p]]];
        node gamma_v = m_pred[m_thread[m_final[v]]];
        node theta = m_thread[m_final[v]];
       
        // Check that f(u) is not in T_v
        bool found_final_u = false;
        for (node n = v; n != theta; n = m_thread[n]) {
            if (n == m_final[u]) {
                found_final_u = true;
                break;
            }
        }
        node phi = m_rev_thread[v];
        node delta = found_final_u ? phi : m_final[u];

        TRACE("network_flow", tout << "Graft T_q and T_r'\n";);

        // Graft T_q and T_r'    
        for (node n = p; n != gamma_p && n != -1; n = m_pred[n]) {
            TRACE("network_flow", tout << "1: m_final[" << n << "] |-> " << z << "\n";);
            m_final[n] = z;
        }

        m_thread[x] = q;
        m_rev_thread[q] = x;
        m_thread[z] = y;
        m_rev_thread[y] = z;
        // Increase depths of all children in T_q
        last = m_thread[m_final[q]];
        for (node n = q; n != last; n = m_thread[n]) {
            m_depth[n] += 1 + m_depth[p] - m_depth[q];
        }

        TRACE("network_flow", tout << "Update T_r'\n";);

        // Update T_r'
        m_thread[phi] = theta;
        m_rev_thread[theta] = phi;

        for (node n = u; n != gamma_v && n != -1; n = m_pred[n]) {
            TRACE("network_flow", tout << "2: m_final[" << n << "] |-> " << delta << "\n";);
            m_final[n] = delta;
        }

        TRACE("network_flow", tout << pp_vector("Last Successors", m_final, true) << pp_vector("Depths", m_depth););

        // Reroot T_v at q
        if (v != q) {
            TRACE("network_flow", tout << "Reroot T_v at q\n";);
   
            node alpha1, alpha2;
            node prev = q;
            for (node n = v; n != q && n != -1; n = m_pred[n]) {
                // Find all immediate successors of n
                node t1 = m_thread[n];
                node t2 = m_thread[m_final[t1]];
                node t3 = m_thread[m_final[t2]];
                if (t1 == m_pred[n]) {
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
                m_thread[m_final[alpha2]] = prev;
                prev = n;           
            }
            m_thread[m_final[q]] = prev;
        }

        for (unsigned i = 0; i < m_thread.size(); ++i) {
            m_rev_thread[m_thread[i]] = i;
        }       

        TRACE("network_flow", {
            tout << pp_vector("Threads", m_thread, true) << pp_vector("Reverse Threads", m_rev_thread);
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
            oss << prefix << i << "[shape=circle,label=\"" << prefix << i << " [";
            oss << m_potentials[i] << "/" << m_balances[i] << "]\"];\n";
        }
        oss << prefix << root << "[shape=doublecircle,label=\"" << prefix << root << " [";
        oss << m_potentials[root] << "/" << m_balances[root] << "]\"];\n";
        
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            oss << prefix << e.get_source() << " -> " << prefix << e.get_target();
            if (m_states[i] == BASIS) {
                oss << "[color=red,penwidth=3.0,label=\"" << m_flows[i] << "/" << e.get_weight() << "\"];\n";
            }
            else {
                oss << "[label=\"" << m_flows[i] << "/" << e.get_weight() << "\"];\n";
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
                m_states[m_leaving_edge] = (m_flows[m_leaving_edge].is_zero()) ? LOWER : UPPER;
                update_spanning_tree();
                update_potentials();                
                TRACE("network_flow", tout << "Spanning tree:\n" << display_spanning_tree(););
                SASSERT(check_well_formed());
            } 
            else {
                m_states[m_leaving_edge] = m_states[m_leaving_edge] == LOWER ? UPPER : LOWER;
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
            if (m_states[i] == BASIS) {
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

    static unsigned find(svector<int>& roots, unsigned x) {
        unsigned old_x = x;
        while (roots[x] >= 0) {
            x = roots[x];
        }
        SASSERT(roots[x] < 0);
        if (old_x != x) {
            roots[old_x] = x;
        }
        return x;
    }

    static void merge(svector<int>& roots, unsigned x, unsigned y) {
        x = find(roots, x);
        y = find(roots, y);
        SASSERT(roots[x] < 0 && roots[y] < 0);
        if (x == y) {
            return;
        }
        if (roots[x] > roots[y]) {
            std::swap(x, y);
        }
        SASSERT(roots[x] <= roots[y]);
        roots[x] += roots[y];
        roots[y] = x;
    }

    static int get_final(int root, svector<int> const & thread, svector<int> const & depth) {
        int n = root;
        while (depth[thread[n]] > depth[root]) {
            n = thread[n];
        }
        return n;
    }

    template<typename Ext>
    bool network_flow<Ext>::check_well_formed() {
        node root = m_pred.size()-1;

        // m_upwards show correct direction
        for (unsigned i = 0; i < m_upwards.size(); ++i) {
            node p = m_pred[i];
            edge_id id;
            SASSERT(m_upwards[i] == m_graph.get_edge_id(i, p, id));            
        }

        // m_depth[x] denotes distance from x to the root node
        for (node x = m_thread[root]; x != root; x = m_thread[x]) {
            SASSERT(m_depth[x] == m_depth[m_pred[x]] + 1);
        }

        // m_final of a node denotes the last node with a bigger depth
        for (unsigned i = 0; i < m_final.size(); ++i) {
            SASSERT(m_final[i] == get_final(i, m_thread, m_depth));
        }

        // m_thread forms a spanning tree over [0..root]
        // Union-find structure
        svector<int> roots(m_pred.size(), -1);
                      
        for (node x = m_thread[root]; x != root; x = m_thread[x]) {
            node y = m_pred[x];
            // We are now going to check the edge between x and y
            SASSERT(find(roots, x) != find(roots, y));
            merge(roots, x, y);
        }

        std::cout << "roots" << std::endl;
        for (unsigned i = 0; i < roots.size(); ++i) {
            std::cout << i << " |-> " << roots[i] << std::endl;         
        }
        
        // All nodes belong to the same spanning tree
        for (unsigned i = 0; i < roots.size(); ++i) {            
            SASSERT(i == 0 ? roots[i] + roots.size() == 0 : roots[i] == 0);            
        }        

        // m_flows are zero on non-basic edges
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            SASSERT(m_states[i] == BASIS || m_flows[i].is_zero());
        }

        return true;
    }

}

#endif

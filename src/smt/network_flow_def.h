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
#include"uint_set.h"

namespace smt {

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

        tree = thread_spanning_tree();
        m_step = 0;
    }

    template<typename Ext>
    void network_flow<Ext>::initialize() {
        TRACE("network_flow", tout << "initialize...\n";);
        // Create an artificial root node to construct initial spanning tree
        unsigned num_nodes = m_graph.get_num_nodes();
        unsigned num_edges = m_graph.get_num_edges();
        
        node root = num_nodes;
        m_graph.init_var(root);
        m_potentials[root] = numeral::zero();

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
        svector<bool> upwards(num_nodes, false);
        for (unsigned i = 0; i < num_nodes; ++i) {
            upwards[i] = !m_balances[i].is_neg();
            m_states[num_edges + i] = BASIS;
            node src = upwards[i] ? i : root;
            node tgt = upwards[i] ? root : i;            
            m_flows[num_edges + i] = upwards[i] ? m_balances[i] : -m_balances[i];            
            m_graph.add_edge(src, tgt, numeral::one(), explanation());
        }

        tree.initialize(upwards, num_nodes);

        // Compute initial potentials
        svector<node> descendants;
        tree.get_descendants(root, descendants);
        // Skip root node
        for (unsigned i = 1; i < descendants.size(); ++i) {
            node u = descendants[i];
            node v = tree.get_parent(u);   
            edge_id e_id = get_edge_id(u, v);            
            m_potentials[u] = m_potentials[v] + (tree.get_arc_direction(u) ? - m_graph.get_weight(e_id) : m_graph.get_weight(e_id));
        }

        TRACE("network_flow", {
                tout << pp_vector("Potentials", m_potentials, true) << pp_vector("Flows", m_flows);
            });
        TRACE("network_flow", tout << "Spanning tree:\n" << display_spanning_tree(););
        SASSERT(check_well_formed());
    }

    template<typename Ext>
    edge_id network_flow<Ext>::get_edge_id(dl_var source, dl_var target) const {
        // tree.get_arc_direction(source) decides which node is the real source
        edge_id id;
        VERIFY(tree.get_arc_direction(source) ? m_graph.get_edge_id(source, target, id) : m_graph.get_edge_id(target, source, id));
        return id;
    }

    template<typename Ext>
    void network_flow<Ext>::update_potentials() {
        TRACE("network_flow", tout << "update_potentials...\n";);
        node src = m_graph.get_source(m_entering_edge);
        node tgt = m_graph.get_target(m_entering_edge); 
        numeral cost = m_graph.get_weight(m_entering_edge);
        numeral change = m_potentials[tgt] - m_potentials[src] + (tree.get_arc_direction(src) ? -cost : cost);
        svector<node> descendants;
        tree.get_descendants(src, descendants);
        for (unsigned i = 0; i < descendants.size(); ++i) {
            node u = descendants[i];
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
        svector<node> ancestors;
        tree.get_ancestors(source, ancestors);
        for (unsigned i = 0; i < ancestors.size() && ancestors[i] != m_join_node; ++i) {
            node u = ancestors[i];
            edge_id e_id = get_edge_id(u, tree.get_parent(u));
            m_flows[e_id] += tree.get_arc_direction(u) ? -val : val;
        }

        node target = m_graph.get_target(m_entering_edge);
        tree.get_ancestors(target, ancestors);
        for (unsigned i = 0; i < ancestors.size() && ancestors[i] != m_join_node; ++i) {
            node u = ancestors[i];
            edge_id e_id = get_edge_id(u, tree.get_parent(u));
            m_flows[e_id] += tree.get_arc_direction(u) ? val : -val;
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
            std::swap(source, target);
        }
        
        m_join_node = tree.get_common_ancestor(source, target);

        TRACE("network_flow", tout << "Found join node " << m_join_node << std::endl;);    
        m_delta.set_invalid();
        node src, tgt;

        // Send flows along the path from source to the ancestor
        svector<node> ancestors;
        tree.get_ancestors(source, ancestors);
        for (unsigned i = 0; i < ancestors.size() && ancestors[i] != m_join_node; ++i) {
            node u = ancestors[i];
            edge_id e_id = get_edge_id(u, tree.get_parent(u));            
            if (tree.get_arc_direction(u) && (!m_delta || m_flows[e_id] < *m_delta)) {
                m_delta = m_flows[e_id];
                src = u;
                tgt = tree.get_parent(u);
                SASSERT(edge_in_tree(src,tgt));
                m_in_edge_dir = true;
            }
        }

        // Send flows along the path from target to the ancestor
        tree.get_ancestors(target, ancestors);
        for (unsigned i = 0; i < ancestors.size() && ancestors[i] != m_join_node; ++i) {
            node u = ancestors[i];
            edge_id e_id = get_edge_id(u, tree.get_parent(u)); 
            if (!tree.get_arc_direction(u) && (!m_delta || m_flows[e_id] <= *m_delta)) {
                m_delta = m_flows[e_id];
                src = u;
                tgt = tree.get_parent(u);
                SASSERT(edge_in_tree(src,tgt));
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
       
        tree.update(p, q, u, v);
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
				SASSERT(edge_in_tree(m_leaving_edge));
				SASSERT(!edge_in_tree(m_entering_edge));
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
        SASSERT(check_optimal());
        return true;
    }

    // Get the optimal solution
    template<typename Ext>
    typename network_flow<Ext>::numeral network_flow<Ext>::get_optimal_solution(vector<numeral> & result, bool is_dual) {
        numeral objective_value = numeral::zero();
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            if (m_states[i] == BASIS) 
            {
                objective_value += e.get_weight().get_rational() * m_flows[i];
            }
        }
        result.reset();
        if (is_dual) {            
            result.append(m_potentials);                   
        }
        else {
            result.append(m_flows);     
        }
        return objective_value;
    }

    template<typename Ext>
    bool network_flow<Ext>::edge_in_tree(edge_id id) const {
        return m_states[id] == BASIS;
    }

    template<typename Ext>
    bool network_flow<Ext>::edge_in_tree(node src, node dst) const {
        return edge_in_tree(get_edge_id(src, dst));
    }

    
    template<typename Ext>
    bool network_flow<Ext>::check_well_formed() {
        SASSERT(tree.check_well_formed());

        // m_flows are zero on non-basic edges
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            SASSERT(m_states[i] == BASIS || m_flows[i].is_zero());
        }

        // m_upwards show correct direction
        for (unsigned i = 0; i < m_potentials.size(); ++i) {
            node p = tree.get_parent(i);
            edge_id id;
            SASSERT(!tree.get_arc_direction(i) || m_graph.get_edge_id(i, p, id));            
        }    

        return true;
    }

    template<typename Ext>
    bool network_flow<Ext>::check_optimal() {
        numeral total_cost = numeral::zero();
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < es.size(); ++i) {
            edge const & e = es[i];
            if (m_states[i] == BASIS) 
            {
                total_cost += e.get_weight().get_rational() * m_flows[i];
            }
        }

        // m_flows are zero on non-basic edges
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            SASSERT(m_states[i] == BASIS || m_flows[i].is_zero());
        }
        numeral total_balance = numeral::zero();
        for (unsigned i = 0; i < m_potentials.size(); ++i) {
            total_balance += m_balances[i] * m_potentials[i];
        }    
        std::cout << "Total balance: " << total_balance << ", total cost: " << total_cost << std::endl;
        return total_cost == total_balance;
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
}

#endif

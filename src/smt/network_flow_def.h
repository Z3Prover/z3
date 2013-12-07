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
#include"spanning_tree_def.h"

namespace smt {

    template<typename Ext>    
    bool network_flow<Ext>::first_eligible_pivot::choose_entering_edge() {
        numeral cost = numeral::zero();
        int num_edges = m_graph.get_num_edges();
        for (int i = m_next_edge; i < m_next_edge + num_edges; ++i) {
            edge_id id = i % num_edges;
            if (edge_in_tree(id)) {
                continue;
            }
            node src = m_graph.get_source(id);
            node tgt = m_graph.get_target(id);
            cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(id);
            if (cost.is_pos()) {
                m_next_edge = m_enter_id = id;
                return true;
            }
        }
        return false;
    };

    template<typename Ext>    
    bool network_flow<Ext>::best_eligible_pivot::choose_entering_edge() {
        unsigned num_edges = m_graph.get_num_edges();
        numeral cost = numeral::zero();
        for (unsigned i = 0; i < num_edges; ++i) {
            node src = m_graph.get_source(i);
            node tgt = m_graph.get_target(i);
            if (!edge_in_tree(i)) {
                numeral new_cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(i);
                if (new_cost > cost) {
                    cost = new_cost;
                    m_enter_id = i;
                }
            }
        }
        return cost.is_pos();
    };

    template<typename Ext>    
    bool network_flow<Ext>::candidate_list_pivot::choose_entering_edge() {
        numeral cost = numeral::zero();
        if (m_current_length == 0 || m_minor_step == MINOR_STEP_LIMIT) {
            // Build the candidate list
            unsigned num_edges = m_graph.get_num_edges();
            m_current_length = 0;
            for (unsigned i = m_next_edge; i < m_next_edge + num_edges; ++i) {
                edge_id id = (i >= num_edges) ? i - num_edges : i;
                node src = m_graph.get_source(id);
                node tgt = m_graph.get_target(id);
                if (!edge_in_tree(id)) {
                    numeral new_cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(id);
                    if (new_cost.is_pos()) {
                        m_candidates[m_current_length] = id;
                        ++m_current_length;
                        if (new_cost > cost) {
                            cost = new_cost;
                            m_enter_id = id;
                        }
                    }
                    if (m_current_length >= m_num_candidates) break;
                }
            }
            m_next_edge = m_enter_id;
            m_minor_step = 1;
            return cost.is_pos();
        }
        
        ++m_minor_step;
        for (unsigned i = 0; i < m_current_length; ++i) {
            edge_id id = m_candidates[i];
            node src = m_graph.get_source(id);
            node tgt = m_graph.get_target(id);
            if (!edge_in_tree(id)) {
                numeral new_cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(id);
                if (new_cost > cost) {
                    cost = new_cost;
                    m_enter_id = id;
                }
                // Remove stale candidates
                if (!new_cost.is_pos()) {
                    --m_current_length;
                    m_candidates[i] = m_candidates[m_current_length];
                    --i;
                }
            }
        }
        return cost.is_pos();
    };

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
        TRACE("network_flow", {
            tout << "Difference logic optimization:" << std::endl;
            display_dual(tout);
            tout << "Minimum cost flow:" << std::endl;
            display_primal(tout);
            };);

        m_step = 0;
        m_tree = alloc(basic_spanning_tree<Ext>, m_graph);
    }


    template<typename Ext>
    void network_flow<Ext>::initialize() {
        TRACE("network_flow", tout << "initialize...\n";);
        // Create an artificial root node to construct initial spanning tree
        unsigned num_nodes = m_graph.get_num_nodes();
        unsigned num_edges = m_graph.get_num_edges();
        
        node root = num_nodes;
        m_graph.init_var(root);

        m_potentials.resize(num_nodes + 1);     
        m_potentials[root] = numeral::zero();

        m_balances.resize(num_nodes + 1);
        fin_numeral sum_supply = fin_numeral::zero();
        for (unsigned i = 0; i < num_nodes; ++i) {
            sum_supply += m_balances[i];
        }        
        m_balances[root] = -sum_supply;

        m_flows.resize(num_nodes + num_edges);
        m_flows.fill(numeral::zero());
        m_states.resize(num_nodes + num_edges);
        m_states.fill(LOWER);

        // Create artificial edges from/to root node to/from other nodes and initialize the spanning tree
        svector<edge_id> tree;
        for (unsigned i = 0; i < num_nodes; ++i) {
            bool is_forward = !m_balances[i].is_neg();
            m_states[num_edges + i] = BASIS;
            node src = is_forward ? i : root;
            node tgt = is_forward ? root : i;            
            m_flows[num_edges + i] = is_forward ? m_balances[i] : -m_balances[i];
            m_potentials[i] = is_forward ? numeral::one() : -numeral::one();
            tree.push_back(m_graph.add_edge(src, tgt, numeral::one(), explanation()));
        }

        m_tree->initialize(tree);

        TRACE("network_flow", 
              tout << pp_vector("Potentials", m_potentials);
              tout << pp_vector("Flows", m_flows);
              tout << "Cost: " << get_cost() << "\n";
              tout << "Spanning tree:\n";               
              display_spanning_tree(tout);
              display_primal(tout););
        SASSERT(check_well_formed());
    }

    template<typename Ext>
    void network_flow<Ext>::update_potentials() {        
        node src = m_graph.get_source(m_enter_id);
        node tgt = m_graph.get_target(m_enter_id);      
        numeral cost = m_potentials[src] - m_potentials[tgt] - m_graph.get_weight(m_enter_id);
        numeral change;
        node start;
        if (m_tree->in_subtree_t2(tgt)) {
            change = cost;
            start = tgt;
        }
        else {
            change = -cost;
            start = src;
        }
        SASSERT(m_tree->in_subtree_t2(start));
        TRACE("network_flow", tout << "update_potentials of T_" << start << " with change = " << change << "...\n";);
        svector<node> descendants;
        m_tree->get_descendants(start, descendants);
        SASSERT(descendants.size() >= 1);
        for (unsigned i = 0; i < descendants.size(); ++i) {
            node u = descendants[i];           
            m_potentials[u] += change;
        }
        TRACE("network_flow", tout << pp_vector("Potentials", m_potentials););
    }

    template<typename Ext>
    void network_flow<Ext>::update_flows() {
        m_flows[m_enter_id] += *m_delta;
        node src = m_graph.get_source(m_enter_id);
        node tgt = m_graph.get_target(m_enter_id); 
        svector<edge_id> path;
        svector<bool> against;
        m_tree->get_path(src, tgt, path, against);
        SASSERT(path.size() >= 1);
        for (unsigned i = 0; i < path.size(); ++i) {
            edge_id e_id = path[i];
            m_flows[e_id] += against[i] ? - *m_delta : *m_delta;
        }
        TRACE("network_flow", tout << pp_vector("Flows", m_flows););
    }
    
    template<typename Ext>
    bool network_flow<Ext>::choose_leaving_edge() {        
        node src = m_graph.get_source(m_enter_id);
        node tgt = m_graph.get_target(m_enter_id); 
        m_delta.set_invalid();
        edge_id leave_id = null_edge_id;
        svector<edge_id> path;
        svector<bool> against;
        m_tree->get_path(src, tgt, path, against);
        SASSERT(path.size() >= 1);
        for (unsigned i = 0; i < path.size(); ++i) {
            edge_id e_id = path[i];
            if (against[i] && (!m_delta || m_flows[e_id] < *m_delta)) {
                m_delta = m_flows[e_id];
                leave_id = e_id;
            }
        }
        m_leave_id = leave_id;
       
        return m_delta;
    }

    template<typename Ext>
    void network_flow<Ext>::update_spanning_tree() {  
        m_tree->update(m_enter_id, m_leave_id);
    }

    template<typename Ext>
    bool network_flow<Ext>::choose_entering_edge(pivot_rule pr) {
        if (!m_pivot || pr != m_pivot->rule()) {
            switch (pr) {
            case FIRST_ELIGIBLE: 
                m_pivot = alloc(first_eligible_pivot, m_graph, m_potentials, m_states, m_enter_id);
                break;
            case BEST_ELIGIBLE:
                m_pivot = alloc(best_eligible_pivot, m_graph, m_potentials, m_states, m_enter_id);
                break;
            case CANDIDATE_LIST:
                m_pivot = alloc(candidate_list_pivot, m_graph, m_potentials, m_states, m_enter_id);
                break;
            default:
                UNREACHABLE();
            }
        }
        return m_pivot->choose_entering_edge();
    }

    // Minimize cost flows
    template<typename Ext>
    min_flow_result network_flow<Ext>::min_cost(pivot_rule pr) {
        initialize();
        while (choose_entering_edge(pr)) { 
            bool bounded = choose_leaving_edge();
            if (!bounded) return UNBOUNDED;
            vector<edge>const& es = m_graph.get_all_edges();
            TRACE("network_flow",
                  {
                      edge const& e_in = es[m_enter_id];
                      edge const& e_out = es[m_leave_id];
                      node src_in = e_in.get_source();
                      node tgt_in = e_in.get_target();
                      node src_out = e_out.get_source();
                      node tgt_out = e_out.get_target();
                      numeral c1 = m_potentials[src_in] - m_potentials[tgt_in] - m_graph.get_weight(m_enter_id);
                      numeral c2 = m_potentials[src_out] - m_potentials[tgt_out] - m_graph.get_weight(m_leave_id);
                      tout << "new base: y_" << src_in  << "_" << tgt_in  << " cost: " << c1 << " delta: " << *m_delta << "\n";
                      tout << "old base: y_" << src_out << "_" << tgt_out << " cost: " << c2 << "\n";                  
                  }
                  );
            update_flows();
            if (m_enter_id != m_leave_id) {
                SASSERT(edge_in_tree(m_leave_id));
                SASSERT(!edge_in_tree(m_enter_id));
                m_states[m_enter_id] = BASIS;
                m_states[m_leave_id] = LOWER;
                update_spanning_tree();
                update_potentials();                
                TRACE("network_flow", 
                      tout << "Spanning tree:\n"; 
                      display_spanning_tree(tout);
                      tout << "Cost: " << get_cost() << "\n";
                      display_primal(tout);
                      );
                SASSERT(check_well_formed());
            }
        }
        TRACE("network_flow", 
              tout << "Spanning tree:\n"; 
              display_spanning_tree(tout);
              tout << "Cost: " << get_cost() << "\n";
              display_primal(tout);
              );
        if (is_infeasible()) return INFEASIBLE;
        TRACE("network_flow", tout << "Found optimal solution.\n";);
        SASSERT(check_optimal());
        return OPTIMAL;
    }

    template<typename Ext>
    bool network_flow<Ext>::is_infeasible() {
        // Flows of artificial arcs should be zero
        unsigned num_nodes = m_graph.get_num_nodes();
        unsigned num_edges = m_graph.get_num_edges();
        SASSERT(m_flows.size() == num_edges);
        for (unsigned i = 1; i < num_nodes; ++i) {
            if (m_flows[num_edges - i].is_pos()) return true;
        }
        return false;
    }

    // Get the optimal solution
    template<typename Ext>
    typename network_flow<Ext>::numeral network_flow<Ext>::get_optimal_solution(vector<numeral> & result, bool is_dual) {
        numeral objective_value = get_cost();
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
    typename network_flow<Ext>::numeral network_flow<Ext>::get_cost() const {
        numeral objective_value = numeral::zero();
        unsigned num_edges = m_graph.get_num_edges();
        for (unsigned i = 0; i < num_edges; ++i) {
            if (edge_in_tree(i)) {
                objective_value += m_flows[i].get_rational() * m_graph.get_weight(i);
            }
        }
        return objective_value;
    }

    template<typename Ext>
    bool network_flow<Ext>::edge_in_tree(edge_id id) const {
        return m_states[id] == BASIS;
    }
    
    template<typename Ext>
    bool network_flow<Ext>::check_well_formed() {
        SASSERT(m_tree->check_well_formed());
        SASSERT(!m_delta || !(*m_delta).is_neg());

        // m_flows are zero on non-basic edges
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            SASSERT(!m_flows[i].is_neg());
            SASSERT(edge_in_tree(i) || m_flows[i].is_zero());
        }

        unsigned num_edges = m_graph.get_num_edges();
        for (unsigned i = 0; i < num_edges; ++i) {
            if (edge_in_tree(i)) {
                dl_var src = m_graph.get_source(i);
                dl_var tgt = m_graph.get_target(i);
                numeral weight = m_graph.get_weight(i);
                SASSERT(m_potentials[src] - m_potentials[tgt] == weight);
            }
        }

        return true;
    }

    template<typename Ext>
    bool network_flow<Ext>::check_optimal() {
        numeral total_cost = get_cost();
        unsigned num_edges = m_graph.get_num_edges();

        for (unsigned i = 0; i < num_edges; ++i) {
            dl_var src = m_graph.get_source(i);
            dl_var tgt = m_graph.get_target(i);
            numeral weight = m_graph.get_weight(i);
            SASSERT(m_potentials[src] - m_potentials[tgt] <= weight);
        }

        // m_flows are zero on non-basic edges
        for (unsigned i = 0; i < m_flows.size(); ++i) {
            SASSERT(edge_in_tree(i) || m_flows[i].is_zero());
        }
        numeral total_balance = numeral::zero();
        for (unsigned i = 0; i < m_potentials.size(); ++i) {
            total_balance += m_balances[i] * m_potentials[i];
        }    
        TRACE("network_flow", tout << "Total balance: " << total_balance << ", total cost: " << total_cost << std::endl;);
        return total_cost == total_balance;
    }

    // display methods

    template<typename Ext>
    void network_flow<Ext>::display_primal(std::ofstream & os) {
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < m_graph.get_num_edges(); ++i) {
            edge const & e = es[i];
            os << "(declare-fun y_" << e.get_source() << "_" << e.get_target() << " () Real)" << std::endl;
        };

        for (unsigned i = 0; i < m_graph.get_num_edges(); ++i) {
            edge const & e = es[i];
            os << "(assert (>= y_" << e.get_source() << "_" << e.get_target() << " 0))" << std::endl;
        };

        for (unsigned i = 0; i < m_graph.get_num_nodes(); ++i) {
            bool initialized = false;
            for (unsigned j = 0; j < m_graph.get_num_edges(); ++j) {
                edge const & e = es[j];
                if (e.get_target() == i || e.get_source() == i) {
                    if (!initialized) {
                        os << "(assert (= (+";
                    }
                    initialized = true;
                    if (e.get_target() == i) {
                        os << " y_" << e.get_source() << "_" << e.get_target();
                    }
                    else {
                        os << " (- y_" << e.get_source() << "_" << e.get_target() << ")";
                    }
                }
            }
            if(initialized) {
                os << " " << m_balances[i] << ") 0))" << std::endl;
            }
        }
        
        os << "(minimize (+";
        for (unsigned i = 0; i < m_graph.get_num_edges(); ++i) {
            edge const & e = es[i];
            os << " (* " << e.get_weight() << " y_" << e.get_source() << "_" << e.get_target() << ")";
        };
        os << "))" << std::endl;
        os << "(optimize)" << std::endl;
        if (!m_flows.empty()) {
            for (unsigned i = 0; i < m_graph.get_num_edges(); ++i) {
                edge const & e = es[i];
                os << "; y_" << e.get_source() << "_" << e.get_target() << " = " << m_flows[i] << "\n";
            }
        }
    }


    template<typename Ext>
    void network_flow<Ext>::display_dual(std::ofstream & os) {
        for (unsigned i = 0; i < m_graph.get_num_nodes(); ++i) {
            os << "(declare-fun v" << i << " () Real)" << std::endl;
        }
        vector<edge> const & es = m_graph.get_all_edges();
        for (unsigned i = 0; i < m_graph.get_num_edges(); ++i) {
            edge const & e = es[i];
            os << "(assert (<= (- v" << e.get_source() << " v" << e.get_target() << ") " << e.get_weight() << "))" << std::endl;
        };
        os << "(assert (= v0 0))" << std::endl;
        os << "(maximize (+";
        for (unsigned i = 0; i < m_balances.size(); ++i) {
            os << " (* " << m_balances[i] << " v" << i << ")";
        };
        os << "))" << std::endl;
        os << "(optimize)" << std::endl;
    }

    template<typename Ext>
    void network_flow<Ext>::display_spanning_tree(std::ofstream & os) {
        ++m_step;;
        std::string prefix = "T";
        prefix.append(std::to_string(m_step));
        prefix.append("_");
        unsigned root = m_graph.get_num_nodes() - 1;
        for (unsigned i = 0; i < root; ++i) {
            os << prefix << i << "[shape=circle,label=\"" << prefix << i << " [";
            os << m_potentials[i] << "/" << m_balances[i] << "]\"];\n";
        }
        os << prefix << root << "[shape=doublecircle,label=\"" << prefix << root << " [";
        os << m_potentials[root] << "/" << m_balances[root] << "]\"];\n";
        
        unsigned num_edges = m_graph.get_num_edges();
        for (unsigned i = 0; i < num_edges; ++i) {
            os << prefix << m_graph.get_source(i) << " -> " << prefix << m_graph.get_target(i);
            if (edge_in_tree(i)) {
                os << "[color=red,penwidth=3.0,label=\"" << m_flows[i] << "/" << m_graph.get_weight(i) << "\"];\n";
            }
            else {
                os << "[label=\"" << m_flows[i] << "/" << m_graph.get_weight(i) << "\"];\n";
            }
        }
        os << std::endl;
    }
}

#endif

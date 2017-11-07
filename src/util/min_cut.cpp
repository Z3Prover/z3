/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    min_cut.cpp

Abstract:
    min cut solver

Author:
    Bernhard Gleiss

Revision History:


--*/
#include "util/min_cut.h"
#include "util/trace.h"

min_cut::min_cut() {    
    // push back two empty vectors for source and sink
    m_edges.push_back(edge_vector());
    m_edges.push_back(edge_vector());
}

unsigned min_cut::new_node() {
    m_edges.push_back(edge_vector());
    return m_edges.size() - 1;
}

void min_cut::add_edge(unsigned int i, unsigned int j, unsigned capacity) {
    m_edges.reserve(i + 1);
    m_edges[i].push_back(edge(j, capacity));
    TRACE("spacer.mincut", tout << "adding edge (" << i << "," << j << ")\n";);    
}

void min_cut::compute_min_cut(unsigned_vector& cut_nodes) {
    if (m_edges.size() == 2) {
        return;
    }
    
    m_d.resize(m_edges.size());
    m_pred.resize(m_edges.size());
    
    // compute initial distances and number of nodes
    compute_initial_distances();
    
    unsigned i = 0;
    
    while (m_d[0] < m_edges.size()) {
        unsigned j = get_admissible_edge(i);
            
        if (j < m_edges.size()) {
            // advance(i)
            m_pred[j] = i;
            i = j;
            
            // if i is the sink, augment path
            if (i == 1) {
                augment_path();
                i = 0;
            }
        }
        else {
            // retreat
            compute_distance(i);
            if (i != 0) {
                i = m_pred[i];
            }
        }
    }

    // split nodes into reachable and unreachable ones
    bool_vector reachable(m_edges.size());
    compute_reachable_nodes(reachable);
    
    // find all edges between reachable and unreachable nodes and 
    // for each such edge, add corresponding lemma to unsat-core
    compute_cut_and_add_lemmas(reachable, cut_nodes);
}

void min_cut::compute_initial_distances() {
    unsigned_vector todo;
    bool_vector visited(m_edges.size());
    
    todo.push_back(0); // start at the source, since we do postorder traversel
    
    while (!todo.empty()) {
        unsigned current = todo.back();
        
        // if we haven't already visited current
        if (!visited[current]) {
            bool exists_unvisited_parent = false;
            
            // add unprocessed parents to stack for DFS. If there is at least 
            // one unprocessed parent, don't compute the result
            // for current now, but wait until those unprocessed parents are processed
            for (auto const& edge : m_edges[current]) {
                unsigned parent = edge.node;
                
                // if we haven't visited the current parent yet
                if (!visited[parent]) {
                    // add it to the stack
                    todo.push_back(parent);
                    exists_unvisited_parent = true;
                }
            }
            
            // if we already visited all parents, we can visit current too
            if (!exists_unvisited_parent) {
                visited[current] = true;
                todo.pop_back();
                
                compute_distance(current); // I.H. all parent distances are already computed
            }
        }
        else {
            todo.pop_back();
        }
    }
}

unsigned min_cut::get_admissible_edge(unsigned i) {
    for (const auto& edge : m_edges[i]) {
        if (edge.weight > 0 && m_d[i] == m_d[edge.node] + 1) {
            return edge.node;
        }
    }
    return m_edges.size(); // no element found
}

void min_cut::augment_path() {
    // find bottleneck capacity
    unsigned max = std::numeric_limits<unsigned int>::max();
    unsigned k = 1;
    while (k != 0) {
        unsigned l = m_pred[k];
        for (const auto& edge : m_edges[l]) {
            if (edge.node == k) {
                max = std::min(max, edge.weight);
            }
        }
        k = l;
    }

    k = 1;
    while (k != 0) {
        unsigned l = m_pred[k];
        
        // decrease capacity
        for (auto& edge : m_edges[l]) {
            if (edge.node == k) {
                edge.weight -= max;
            }
        }
        // increase reverse flow
        bool already_exists = false;
        for (auto& edge : m_edges[k]) {
            if (edge.node == l) {
                already_exists = true;
                edge.weight += max;
            }
        }
        if (!already_exists) {
            m_edges[k].push_back(edge(1, max));
        }
        k = l;
    }
}

void min_cut::compute_distance(unsigned i) {
    if (i == 1) { // sink node
        m_d[1] = 0;
    }
    else {
        unsigned min = std::numeric_limits<unsigned int>::max();
        
        // find edge (i,j) with positive residual capacity and smallest distance
        for (const auto& edge : m_edges[i]) {
            if (edge.weight > 0) {
                min = std::min(min, m_d[edge.node] + 1);
            }
        }
        m_d[i] = min;
    }
}

void min_cut::compute_reachable_nodes(bool_vector& reachable) {
    unsigned_vector todo;
    
    todo.push_back(0);
    while (!todo.empty()) {
        unsigned current = todo.back();
        todo.pop_back();
        
        if (!reachable[current]) {
            reachable[current] = true;
            
            for (const auto& edge : m_edges[current]) {
                if (edge.weight > 0) {
                    todo.push_back(edge.node);
                }
            }
        }
    }
}

void min_cut::compute_cut_and_add_lemmas(bool_vector& reachable, unsigned_vector& cut_nodes) {
    unsigned_vector todo;
    bool_vector visited(m_edges.size());
        
    todo.push_back(0);
    while (!todo.empty()) {
        unsigned current = todo.back();
        todo.pop_back();
        
        if (!visited[current]) {
            visited[current] = true;

            for (const auto& edge : m_edges[current]) {
                unsigned successor = edge.node;
                if (reachable[successor]) {
                    todo.push_back(successor);
                }
                else {
                    cut_nodes.push_back(successor);
                }
            }
        }
    }
}

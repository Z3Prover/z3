/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    spanning_tree.cpp

Abstract:


Author:

    Anh-Dung Phan (t-anphan) 2013-11-06

Notes:
   
--*/
#include <sstream>
#include "spanning_tree.h"
#include "debug.h"
#include "vector.h"
#include "uint_set.h"
#include "trace.h"

namespace smt {

    
    /**
        swap v and q in tree.
        - fixup m_thread
        - fixup m_pred

        Case 1: final(q) == final(v)
        -------
        Old thread: prev -> v -*-> alpha -> q -*-> final(q) -> next
        New thread: prev -> q -*-> final(q) -> v -*-> alpha -> next

        Case 2: final(q) != final(v)
        -------
        Old thread: prev -> v -*-> alpha -> q -*-> final(q) -> beta -*-> final(v) -> next
        New thread: prev -> q -*-> final(q) -> v -*-> alpha -> beta -*-> final(v) -> next
                 
    */
    void thread_spanning_tree::swap_order(node q, node v) {
        SASSERT(q != v);
        SASSERT(m_pred[q] == v);        
        SASSERT(is_preorder_traversal(v, get_final(v)));
        node prev = find_rev_thread(v);
        node final_q = get_final(q);
        node final_v = get_final(v);
        node next = m_thread[final_v];
        node alpha = find_rev_thread(q);

        if (final_q == final_v) {
            m_thread[final_q] = v;
            m_thread[alpha] = next;
        }
        else {
            node beta = m_thread[final_q];
            m_thread[final_q] = v;
            m_thread[alpha] = beta;
        }
        m_thread[prev] = q;
        m_pred[v] = q;
        SASSERT(is_preorder_traversal(q, get_final(q)));
    }
    
    /**
        \brief find node that points to 'n' in m_thread
    */
    node thread_spanning_tree::find_rev_thread(node n) const {     
        node ancestor = m_pred[n];
        SASSERT(ancestor != -1);
        while (m_thread[ancestor] != n) {
            ancestor = m_thread[ancestor];
        }
        return ancestor;
    }

    void thread_spanning_tree::fix_depth(node start, node end) {     
        SASSERT(m_pred[start] != -1);
        m_depth[start] = m_depth[m_pred[start]]+1;
        while (start != end) {
            start = m_thread[start]; 
            m_depth[start] = m_depth[m_pred[start]]+1;
        }
    }
        
    node thread_spanning_tree::get_final(int start) {
        int n = start;
        while (m_depth[m_thread[n]] > m_depth[start]) {
            n = m_thread[n];
        }
        return n;
    }

    bool thread_spanning_tree::is_preorder_traversal(node start, node end) {
        // get children of start
        uint_set children;
        children.insert(start);
        node root = m_pred.size()-1;
        for (int i = 0; i < root; ++i) {
            for (int j = 0; j < root; ++j) {
                if (children.contains(m_pred[j])) {
                    children.insert(j);
                }
            }
        }
        // visit children using m_thread
        children.remove(start);
        do {
            start = m_thread[start];
            SASSERT(children.contains(start));
            children.remove(start);
        }
        while (start != end);
        SASSERT(children.empty());
        return true;
    }

    bool thread_spanning_tree::is_ancestor_of(node ancestor, node child) {
        for (node n = child; n != -1; n = m_pred[n]) {
            if (n == ancestor) {
                return true;
            }
        }
        return false;
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

    void thread_spanning_tree::initialize(svector<bool> const & upwards, int num_nodes) {
        m_pred.resize(num_nodes + 1);
        m_depth.resize(num_nodes + 1);
        m_thread.resize(num_nodes + 1);
        m_upwards.resize(num_nodes + 1);

        node root = num_nodes;
        m_pred[root] = -1;
        m_depth[root] = 0;
        m_thread[root] = 0;
            
        // Create artificial edges from/to root node to/from other nodes and initialize the spanning tree
        for (int i = 0; i < num_nodes; ++i) {
            m_pred[i] = root;
            m_depth[i] = 1;
            m_thread[i] = i + 1;
            m_upwards[i] = upwards[i];
        }

        TRACE("network_flow", {
            tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Depths", m_depth) << pp_vector("Upwards", m_upwards);
        });
    }

    node thread_spanning_tree::get_common_ancestor(node u, node v) {
        while (u != v) {
            if (m_depth[u] > m_depth[v])
                u = m_pred[u];
            else 
                v = m_pred[v];                    
        }
        return u;
    }

    void thread_spanning_tree::get_descendants(node start, svector<node>& descendants) {
        descendants.reset();
        node u = start;
        while (m_depth[m_thread[u]] > m_depth[start]) {
            descendants.push_back(u);
            u = m_thread[u];
        }
    }

    void thread_spanning_tree::get_ancestors(node start, svector<node>& ancestors) {
        ancestors.reset();
        while (m_pred[start] != -1) {                        
            ancestors.push_back(start);
            start = m_pred[start];
        }
    }
        
    /**
        \brief add entering_edge, remove leaving_edge from spanning tree.

        Old tree:                    New tree:
                       root                      root
                     /      \                  /      \
                    x       y                  x       y
                  /   \    / \               /   \    / \
                       u     s                   u      s
                       |    /                          /
                       v    w                    v    w
                      / \    \                  / \    \
                         z   p                     z   p
                          \                         \ /
                           q                         q
        */
    void thread_spanning_tree::update(node p, node q, node u, node v) {
        bool q_upwards = false;

        // v is parent of u so T_u does not contain root node
        if (m_pred[u] == v) {
            std::swap(u, v);
        }  
        SASSERT(m_pred[v] == u);

        if (is_ancestor_of(v, p)) {
            std::swap(p, q);
            q_upwards = true;
        }
        SASSERT(is_ancestor_of(v, q));

        TRACE("network_flow", { 
            tout << "update_spanning_tree: (" << p << ", " << q << ") enters, (";
            tout << u << ", " << v << ") leaves\n";
        });

        // Update m_pred (for nodes in the stem from q to v)
        // Note: m_pred[v] == u
        // Initialize m_upwards[q] = q_upwards

        bool prev_upwards = q_upwards;   
        node old_pred = m_pred[q];        
        if (q != v) {
            for (node n = q; n != u; ) {
                SASSERT(old_pred != u || n == v); // the last processed node is v
                TRACE("network_flow", {
                    tout << pp_vector("Predecessors", m_pred, true);
                });
                SASSERT(-1 != m_pred[old_pred]);
                int next_old_pred = m_pred[old_pred];  
                swap_order(n, old_pred);
                std::swap(m_upwards[n], prev_upwards);
                prev_upwards = !prev_upwards; // flip previous version of upwards.
                n = old_pred;
                old_pred = next_old_pred;
            }     
        }
        m_pred[q] = p;

        // m_thread were updated.
        // update the depth.

        fix_depth(q, get_final(q));

        TRACE("network_flow", {
            tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Depths", m_depth) << pp_vector("Upwards", m_upwards);
            });
    }

    /**
        \brief Check invariants of main data-structures.

        Spanning tree of m_graph + root is represented using:
        
        svector<edge_state> m_states;      edge_id |-> edge_state
        svector<bool> m_upwards;           node |-> bool
        svector<node> m_pred;              node |-> node
        svector<int>  m_depth;             node |-> int
        svector<node> m_thread;            node |-> node

        Tree is determined by m_pred:
        - m_pred[root] == -1
        - m_pred[n] = m != n     for each node n, acyclic until reaching root.
        - m_depth[m_pred[n]] + 1 == m_depth[n] for each n != root        

        m_thread is a linked list traversing all nodes.
        Furthermore, the nodes linked in m_thread follows a 
        depth-first traversal order.

        m_upwards direction of edge from i to m_pred[i] m_graph
                
    */
    bool thread_spanning_tree::check_well_formed() {
        node root = m_pred.size()-1;

        // Check that m_thread traverses each node.
        // This gets checked using union-find as well.
        svector<bool> found(m_thread.size(), false);
        found[root] = true;
        for (node x = m_thread[root]; x != root; x = m_thread[x]) {
            SASSERT(x != m_thread[x]);
            found[x] = true;
        }
        for (unsigned i = 0; i < found.size(); ++i) {
            SASSERT(found[i]);
        }

        // m_pred is acyclic, and points to root.
        SASSERT(m_pred[root] == -1);
        SASSERT(m_depth[root] == 0);
        for (node i = 0; i < root; ++i) {
            SASSERT(m_depth[m_pred[i]] < m_depth[i]);
        }

        // m_depth[x] denotes distance from x to the root node
        for (node x = m_thread[root]; x != root; x = m_thread[x]) {
            SASSERT(m_depth[x] > 0);
            SASSERT(m_depth[x] == m_depth[m_pred[x]] + 1);
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

        // All nodes belong to the same spanning tree
        for (unsigned i = 0; i < roots.size(); ++i) {            
            SASSERT(roots[i] + roots.size() == 0 || roots[i] >= 0);            
        }        

        return true;
    }

    bool thread_spanning_tree::get_arc_direction(node start) const {
        return m_upwards[start];
    }

    node thread_spanning_tree::get_parent(node start) {
        return m_pred[start];
    }
}
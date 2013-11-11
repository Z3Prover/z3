/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    spanning_tree_def.h

Abstract:


Author:

    Anh-Dung Phan (t-anphan) 2013-11-06

Notes:
   
--*/

#ifndef _SPANNING_TREE_DEF_H_
#define _SPANNING_TREE_DEF_H_

#include "spanning_tree.h"

namespace smt {

    template<typename Ext>
    thread_spanning_tree<Ext>::thread_spanning_tree(graph & g) :
        m_graph(g) {
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::initialize(svector<edge_id> const & tree) {
        m_tree = tree;

        unsigned num_nodes = m_graph.get_num_nodes();
        m_pred.resize(num_nodes);
        m_depth.resize(num_nodes);
        m_thread.resize(num_nodes);
        
        node root = num_nodes - 1;
        m_pred[root] = -1;
        m_depth[root] = 0;
        m_thread[root] = 0;
            
        // Create artificial edges from/to root node to/from other nodes and initialize the spanning tree
        for (int i = 0; i < root; ++i) {
            m_pred[i] = root;
            m_depth[i] = 1;
            m_thread[i] = i + 1;
        }

        TRACE("network_flow", {
            tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Depths", m_depth) << pp_vector("Tree", m_tree);
        });
    }

    template<typename Ext>
    typename thread_spanning_tree<Ext>::node thread_spanning_tree<Ext>::get_common_ancestor(node u, node v) {
        while (u != v) {
            if (m_depth[u] > m_depth[v])
                u = m_pred[u];
            else 
                v = m_pred[v];                    
        }
        return u;
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::get_path(node start, node end, svector<edge_id> & path, svector<bool> & against) {
        node join = get_common_ancestor(start, end);
        path.reset();
        while (start != join) {
            edge_id e_id = m_tree[start];
            path.push_back(e_id);
            against.push_back(is_forward_edge(e_id));
            start = m_pred[start];
        }
        while (end != join) {
            edge_id e_id = m_tree[end];
            path.push_back(e_id);
            against.push_back(!is_forward_edge(e_id));
            end = m_pred[end];
        }
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::is_forward_edge(edge_id e_id) const {
        node start = m_graph.get_source(e_id);
        node end = m_graph.get_target(e_id);
        SASSERT(m_pred[start] == end || m_pred[end] == start);
        return m_pred[start] == end;
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::get_descendants(node start, svector<node> & descendants) {
        descendants.reset();        
        descendants.push_back(start);
        node u = m_thread[start];
        while (m_depth[u] > m_depth[start]) {         
            descendants.push_back(u);
            u = m_thread[u];
        }
        
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::in_subtree_t2(node child) {
        if (m_depth[child] < m_depth[m_root_t2]) {
            return false;
        }
        return is_ancestor_of(m_root_t2, child);
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::is_ancestor_of(node ancestor, node child) {
        for (node n = child; n != -1; n = m_pred[n]) {
            if (n == ancestor) {
                return true;
            }
        }
        return false;
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
    template<typename Ext>
    void thread_spanning_tree<Ext>::update(edge_id enter_id, edge_id leave_id) {    
        node p = m_graph.get_source(enter_id);
        node q = m_graph.get_target(enter_id);
        node u = m_graph.get_source(leave_id);
        node v = m_graph.get_target(leave_id);
        
        if (m_pred[u] == v) {
            std::swap(u, v);
        }

        SASSERT(m_pred[v] == u);         

        if (is_ancestor_of(v, p)) {
            std::swap(p, q);    
        }

        SASSERT(is_ancestor_of(v, q));
        
        TRACE("network_flow", { 
            tout << "update_spanning_tree: (" << p << ", " << q << ") enters, (";
            tout << u << ", " << v << ") leaves\n";
        });

        node old_pred = m_pred[q]; 
        // Update stem nodes from q to v
        if (q != v) {
            for (node n = q; n != u; ) {
                SASSERT(old_pred != u || n == v); // the last processed node is v
                SASSERT(-1 != m_pred[old_pred]);
                int next_old_pred = m_pred[old_pred];  
                swap_order(n, old_pred);
                m_tree[old_pred] = m_tree[n];
                n = old_pred;
                old_pred = next_old_pred;
            }     
        }

        // Old threads: alpha -> q -*-> f(q) -> beta | p -*-> f(p) -> gamma
        // New threads: alpha -> beta                | p -*-> f(p) -> q -*-> f(q) -> gamma

        node f_p = get_final(p);
        node f_q = get_final(q);
        node alpha = find_rev_thread(q);
        node beta = m_thread[f_q];
        node gamma = m_thread[f_p];

        if (q != gamma) {
            m_thread[alpha] = beta;
            m_thread[f_p] = q;
            m_thread[f_q] = gamma;
        }
       
        m_pred[q] = p; 
        m_tree[q] = enter_id;
        m_root_t2 = q;

        SASSERT(!in_subtree_t2(p));
        SASSERT(in_subtree_t2(q));
        SASSERT(!in_subtree_t2(u));
        SASSERT(in_subtree_t2(v));
        
        // Update the depth.

        fix_depth(q, get_final(q));

        TRACE("network_flow", {
            tout << pp_vector("Predecessors", m_pred, true) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Depths", m_depth) << pp_vector("Tree", m_tree);
            });
    }

    /**
        \brief Check invariants of main data-structures.

        Spanning tree of m_graph + root is represented using:
        
        svector<edge_state> m_states;      edge_id |-> edge_state
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
        
    */
    template<typename Ext>
    bool thread_spanning_tree<Ext>::check_well_formed() {
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

        for (unsigned i = 0; i < m_tree.size(); ++i) {           
            node src = m_graph.get_source(m_tree[i]);
            node tgt = m_graph.get_target(m_tree[i]);
            SASSERT(m_pred[src] == tgt || m_pred[tgt] == src);            
        }  

        return true;
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
    template<typename Ext>
    void thread_spanning_tree<Ext>::swap_order(node q, node v) {
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
    template<typename Ext>
    typename thread_spanning_tree<Ext>::node thread_spanning_tree<Ext>::find_rev_thread(node n) const {     
        node ancestor = m_pred[n];
        SASSERT(ancestor != -1);
        while (m_thread[ancestor] != n) {
            ancestor = m_thread[ancestor];
        }
        return ancestor;
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::fix_depth(node start, node end) {     
        SASSERT(m_pred[start] != -1);
        m_depth[start] = m_depth[m_pred[start]]+1;
        while (start != end) {
            start = m_thread[start]; 
            m_depth[start] = m_depth[m_pred[start]]+1;
        }
    }
        
    template<typename Ext>
    typename thread_spanning_tree<Ext>::node thread_spanning_tree<Ext>::get_final(int start) {
        int n = start;
        while (m_depth[m_thread[n]] > m_depth[start]) {
            n = m_thread[n];
        }
        return n;
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::is_preorder_traversal(node start, node end) {
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
}

#endif
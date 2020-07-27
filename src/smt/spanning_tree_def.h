/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    spanning_tree_def.h

Abstract:


Author:

    Anh-Dung Phan (t-anphan) 2013-11-06

Notes:
   
--*/

#pragma once

#include "smt/spanning_tree.h"

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
        
        node_id root = num_nodes - 1;
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
            tout << pp_vector("Predecessors", m_pred) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Depths", m_depth) << pp_vector("Tree", m_tree);
        });
    }

    template<typename Ext>
    typename thread_spanning_tree<Ext>::node_id thread_spanning_tree<Ext>::get_common_ancestor(node_id u, node_id v) {
        while (u != v) {
            if (m_depth[u] > m_depth[v])
                u = m_pred[u];
            else 
                v = m_pred[v];                    
        }
        return u;
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::get_path(node_id start, node_id end, svector<edge_id> & path, bool_vector & against) {
        node_id join = get_common_ancestor(start, end);
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
        node_id start = m_graph.get_source(e_id);
        node_id end = m_graph.get_target(e_id);
        SASSERT(m_pred[start] == end || m_pred[end] == start);
        return m_pred[start] == end;
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::get_descendants(node_id start, svector<node_id> & descendants) {
        descendants.reset();        
        descendants.push_back(start);
        node_id u = m_thread[start];
        while (m_depth[u] > m_depth[start]) {         
            descendants.push_back(u);
            u = m_thread[u];
        }
        
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::in_subtree_t2(node_id child) {
        if (m_depth[child] < m_depth[m_root_t2]) {
            return false;
        }
        return is_ancestor_of(m_root_t2, child);
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::is_ancestor_of(node_id ancestor, node_id child) {
        for (node_id n = child; n != -1; n = m_pred[n]) {
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
        node_id p = m_graph.get_source(enter_id);
        node_id q = m_graph.get_target(enter_id);
        node_id u = m_graph.get_source(leave_id);
        node_id v = m_graph.get_target(leave_id);
        
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

        // Old threads: alpha -> v -*-> f(v) -> beta | p -*-> f(p) -> gamma
        // New threads: alpha -> beta                | p -*-> f(p) -> v -*-> f(v) -> gamma

        node_id f_p = get_final(p);
        node_id f_v = get_final(v);
        node_id alpha = find_rev_thread(v);
        node_id beta = m_thread[f_v];
        node_id gamma = m_thread[f_p];

        if (v != gamma) {
            m_thread[alpha] = beta;
            m_thread[f_p] = v;
            m_thread[f_v] = gamma;
        }

        node_id old_pred = m_pred[q]; 
        // Update stem nodes from q to v
        if (q != v) {
            for (node_id n = q; n != v; ) {
                SASSERT(old_pred != u); // the last processed node_id is v
                SASSERT(-1 != m_pred[old_pred]);
                int next_old_pred = m_pred[old_pred];  
                swap_order(n, old_pred);
                m_tree[old_pred] = m_tree[n];
                n = old_pred;
                old_pred = next_old_pred;
            }     
        }
        
        m_pred[q] = p; 
        m_tree[q] = enter_id;
        m_root_t2 = q;

        node_id after_final_q = (v == gamma) ? beta : gamma;
        fix_depth(q, after_final_q);

        SASSERT(!in_subtree_t2(p));
        SASSERT(in_subtree_t2(q));
        SASSERT(!in_subtree_t2(u));
        SASSERT(in_subtree_t2(v));

        TRACE("network_flow", {
            tout << pp_vector("Predecessors", m_pred) << pp_vector("Threads", m_thread); 
            tout << pp_vector("Depths", m_depth) << pp_vector("Tree", m_tree);
            });
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
    void thread_spanning_tree<Ext>::swap_order(node_id q, node_id v) {
        SASSERT(q != v);
        SASSERT(m_pred[q] == v);        
        SASSERT(is_preorder_traversal(v, get_final(v)));
        node_id prev = find_rev_thread(v);
        node_id f_q = get_final(q);
        node_id f_v = get_final(v);
        node_id next = m_thread[f_v];
        node_id alpha = find_rev_thread(q);

        if (f_q == f_v) {
            SASSERT(f_q != v && alpha != next);
            m_thread[f_q] = v;
            m_thread[alpha] = next;
            f_q = alpha;
        }
        else {            
            node_id beta = m_thread[f_q];
            SASSERT(f_q != v && alpha != beta);
            m_thread[f_q] = v;
            m_thread[alpha] = beta;
            f_q = f_v;
        }
        SASSERT(prev != q);
        m_thread[prev] = q;
        m_pred[v] = q;
        // Notes: f_q has to be used since m_depth hasn't been updated yet.
        SASSERT(is_preorder_traversal(q, f_q));
    }

    /**
        \brief Check invariants of main data-structures.

        Spanning tree of m_graph + root is represented using:
        
        svector<edge_state> m_states;      edge_id |-> edge_state
        svector<node_id> m_pred;              node_id |-> node
        svector<int>     m_depth;             node_id |-> int
        svector<node_id> m_thread;            node_id |-> node

        Tree is determined by m_pred:
        - m_pred[root] == -1
        - m_pred[n] = m != n     for each node_id n, acyclic until reaching root.
        - m_depth[m_pred[n]] + 1 == m_depth[n] for each n != root        

        m_thread is a linked list traversing all nodes.
        Furthermore, the nodes linked in m_thread follows a 
        depth-first traversal order.
        
    */
    template<typename Ext>
    bool thread_spanning_tree<Ext>::check_well_formed() {
        node_id root = m_pred.size()-1;

        // Check that m_thread traverses each node.
        // This gets checked using union-find as well.
        bool_vector found(m_thread.size(), false);
        found[root] = true;
        for (node_id x = m_thread[root]; x != root; x = m_thread[x]) {
            SASSERT(x != m_thread[x]);
            found[x] = true;
        }
        for (unsigned i = 0; i < found.size(); ++i) {
            SASSERT(found[i]);
        }

        // m_pred is acyclic, and points to root.
        SASSERT(m_pred[root] == -1);
        SASSERT(m_depth[root] == 0);
        for (node_id i = 0; i < root; ++i) {
            SASSERT(m_depth[m_pred[i]] < m_depth[i]);
        }

        // m_depth[x] denotes distance from x to the root node
        for (node_id x = m_thread[root]; x != root; x = m_thread[x]) {
            SASSERT(m_depth[x] > 0);
            SASSERT(m_depth[x] == m_depth[m_pred[x]] + 1);
        }

        // m_thread forms a spanning tree over [0..root]
        // Union-find structure
        svector<int> roots(m_pred.size(), -1);
                      
        for (node_id x = m_thread[root]; x != root; x = m_thread[x]) {
            node_id y = m_pred[x];
            // We are now going to check the edge between x and y
            SASSERT(find(roots, x) != find(roots, y));
            merge(roots, x, y);
        }

        // All nodes belong to the same spanning tree
        for (unsigned i = 0; i < roots.size(); ++i) {            
            SASSERT(roots[i] + roots.size() == 0 || roots[i] >= 0);            
        }   

        for (unsigned i = 0; i < m_tree.size(); ++i) {           
            node_id src = m_graph.get_source(m_tree[i]);
            node_id tgt = m_graph.get_target(m_tree[i]);
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
        \brief find node_id that points to 'n' in m_thread
    */
    template<typename Ext>
    typename thread_spanning_tree<Ext>::node_id thread_spanning_tree<Ext>::find_rev_thread(node_id n) const {     
        node_id ancestor = m_pred[n];
        SASSERT(ancestor != -1);
        while (m_thread[ancestor] != n) {
            ancestor = m_thread[ancestor];
        }
        return ancestor;
    }

    template<typename Ext>
    void thread_spanning_tree<Ext>::fix_depth(node_id start, node_id after_end) {
        while (start != after_end) {
            SASSERT(m_pred[start] != -1);
            m_depth[start] = m_depth[m_pred[start]]+1;
            start = m_thread[start];
        }
    }
        
    template<typename Ext>
    typename thread_spanning_tree<Ext>::node_id thread_spanning_tree<Ext>::get_final(int start) {
        int n = start;
        while (m_depth[m_thread[n]] > m_depth[start]) {
            n = m_thread[n];
        }
        return n;
    }

    template<typename Ext>
    bool thread_spanning_tree<Ext>::is_preorder_traversal(node_id start, node_id end) {
        // get children of start
        uint_set children;
        children.insert(start);
        node_id root = m_pred.size()-1;
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

    // Basic spanning tree
    template<typename Ext>
    basic_spanning_tree<Ext>::basic_spanning_tree(graph & g) : thread_spanning_tree<Ext>(g) {        
    }

    template<typename Ext>
    void basic_spanning_tree<Ext>::initialize(svector<edge_id> const & tree) {        
        m_tree_graph = alloc(graph);
        m_tree = tree;
        unsigned num_nodes = m_graph.get_num_nodes();
        for (unsigned i = 0; i < num_nodes; ++i) {
            m_tree_graph->init_var(i);
        }

        vector<edge> const & es = m_graph.get_all_edges();
        svector<edge_id>::const_iterator it = m_tree.begin(), end = m_tree.end();
        for(; it != end; ++it) {
            edge const & e = es[*it];
            m_tree_graph->add_edge(e.get_source(), e.get_target(), e.get_weight(), explanation());
        }

        node_id root = num_nodes - 1;
        m_tree_graph->bfs_undirected(root, m_pred, m_depth);
        m_tree_graph->dfs_undirected(root, m_thread);
    }

    template<typename Ext>
    void basic_spanning_tree<Ext>::update(edge_id enter_id, edge_id leave_id) {
        if (m_tree_graph) dealloc(m_tree_graph);
        m_tree_graph = alloc(graph);
        unsigned num_nodes = m_graph.get_num_nodes();
        for (unsigned i = 0; i < num_nodes; ++i) {
            m_tree_graph->init_var(i);
        }

        vector<edge> const & es = m_graph.get_all_edges();
        svector<edge_id>::const_iterator it = m_tree.begin(), end = m_tree.end();
        for(; it != end; ++it) {
            edge const & e = es[*it];
            if (leave_id != *it) {
                m_tree_graph->add_edge(e.get_source(), e.get_target(), e.get_weight(), explanation());
            }
        }
        edge const & e = es[enter_id];
        m_tree_graph->add_edge(e.get_source(), e.get_target(), e.get_weight(), explanation());

        node_id root = num_nodes - 1;
        m_tree_graph->bfs_undirected(root, m_pred, m_depth);
        m_tree_graph->dfs_undirected(root, m_thread);

        vector<edge> const & tree_edges = m_tree_graph->get_all_edges();
        for (unsigned i = 0; i < tree_edges.size(); ++i) {
            edge const & e = tree_edges[i];
            dl_var src = e.get_source();
            dl_var tgt = e.get_target();
            edge_id id;
            VERIFY(m_graph.get_edge_id(src, tgt, id));
            SASSERT(tgt == m_pred[src] || src == m_pred[tgt]);
            if (tgt == m_pred[src]) {
                m_tree[src] = id;
            }
            else {
                m_tree[tgt] = id;
            }
        }

        node_id p = m_graph.get_source(enter_id);
        node_id q = m_graph.get_target(enter_id);
        m_root_t2 = p == m_pred[q] ? q : p;
    }

}


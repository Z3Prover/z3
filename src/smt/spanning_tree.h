/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    spanning_tree.h

Abstract:

    Represent spanning trees with needed operations for Network Simplex

Author:

    Anh-Dung Phan (t-anphan) 2013-11-06

Notes:
   
--*/
#ifndef _SPANNING_TREE_H_
#define _SPANNING_TREE_H_

#include "diff_logic.h"
#include "spanning_tree_base.h"

namespace smt {

    template<typename Ext>
    class thread_spanning_tree : public spanning_tree_base, protected Ext {
    protected:        
        typedef dl_var node;
        typedef dl_edge<Ext> edge;
        typedef dl_graph<Ext> graph;     
        typedef typename Ext::numeral numeral;
        typedef typename Ext::fin_numeral fin_numeral;

        // Store the parent of a node i in the spanning tree
        svector<node> m_pred;
        // Store the number of edge on the path from node i to the root
        svector<int> m_depth;
        // Store the pointer from node i to the next node in depth-first search order
        svector<node> m_thread;

        // i |-> edge between (i, m_pred[i])
        svector<edge_id> m_tree;

        node m_root_t2;

        graph & m_graph;

        void swap_order(node q, node v);
        node find_rev_thread(node n) const;
        void fix_depth(node start, node after_end);
        node get_final(int start);
        bool is_preorder_traversal(node start, node end);   
        node get_common_ancestor(node u, node v);
        bool is_forward_edge(edge_id e_id) const;
        bool is_ancestor_of(node ancestor, node child);

    public:      
        thread_spanning_tree(graph & g);

        virtual void initialize(svector<edge_id> const & tree);
        void get_descendants(node start, svector<node> & descendants);
        
        virtual void update(edge_id enter_id, edge_id leave_id);                
        void get_path(node start, node end, svector<edge_id> & path, svector<bool> & against);              
        bool in_subtree_t2(node child);

        bool check_well_formed();        
    };

    template<typename Ext>
    class basic_spanning_tree : public thread_spanning_tree<Ext> {
    private:
        graph * m_tree_graph;

    public:
        basic_spanning_tree(graph & g);
        void initialize(svector<edge_id> const & tree);
        void update(edge_id enter_id, edge_id leave_id);
    };

}

#endif

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

#include "spanning_tree_base.h"

namespace smt {


    class thread_spanning_tree : virtual public spanning_tree_base {
    private:        
        // Store the parent of a node i in the spanning tree
        svector<node> m_pred;
        // Store the number of edge on the path from node i to the root
        svector<int> m_depth;
        // Store the pointer from node i to the next node in depth-first search order
        svector<node> m_thread;

        // m_upwards[i] is true if the corresponding edge 
        // (i, m_pred[i]) points upwards (pointing toward the root node)
        svector<bool> m_upwards;

        void swap_order(node q, node v);
        node find_rev_thread(node n) const;
        void fix_depth(node start, node end);
        node get_final(int start);
        bool is_preorder_traversal(node start, node end);
        bool is_ancestor_of(node ancestor, node child);

    public:

        void initialize(svector<bool> const & upwards, int num_nodes);
        void get_descendants(node start, svector<node>& descendants);
        void get_ancestors(node start, svector<node>& ancestors);
        node get_common_ancestor(node u, node v);
        void update(node p, node q, node u, node v);
        bool check_well_formed();

        // TODO: remove these two unnatural functions
        bool get_arc_direction(node start) const;
        node get_parent(node start);
    };

}

#endif

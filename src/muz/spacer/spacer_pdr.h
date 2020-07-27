/**++
Copyright (c) 2018 Arie Gurfinkel

Module Name:

    spacer_pdr.h

Abstract:

    SPACER gPDR strategy implementation

Author:

    Arie Gurfinkel

    Based on muz/pdr

Notes:

--*/
#pragma once

#include "muz/spacer/spacer_context.h"

namespace spacer {
// structure for counter-example search.
class model_node {
    pob_ref                m_pob;            // proof obligation
    model_node*            m_parent;         // parent in the search tree
    ptr_vector<model_node> m_children;       // children in the search tree
    model_node*            m_next;           // next element of an in-place circular queue
    model_node*            m_prev;           // prev element of an in-place circular queue
    unsigned               m_orig_level;     // level at which this search node was created
    unsigned               m_depth;          //
    bool                   m_closed;         // whether the pob is derivable
public:
    model_node(model_node* parent, pob* pob);
    void add_child(model_node* kid);

    expr *post() const { return m_pob->post(); }
    unsigned level() const { return m_pob->level(); }
    unsigned orig_level() const { return m_orig_level; }
    unsigned depth() const { return m_depth; }
    void  increase_level() { m_pob->inc_level(); }
    pob_ref &pob() { return m_pob; }
    ptr_vector<model_node> const& children() { return m_children; }
    pred_transformer& pt() const { return m_pob->pt(); }
    model_node* parent() const { return m_parent; }
    // order in children of the parent
    unsigned index_in_parent() const;

    bool is_closed() const { return m_closed; }
    bool is_open() const { return !is_closed(); }

    // closed or has children and they are all closed
    bool is_1closed() {
        if (is_closed()) return true;
        if (m_children.empty()) return false;
        for (auto kid : m_children) 
            if (kid->is_open()) return false;
        return true;
    }

    void check_pre_closed();
    void set_pre_closed() { m_closed = true; }

    void set_closed() { m_closed = true; }
    void set_open();
    void reset_children() { m_children.reset(); }

    /// queue

    // remove this node from the given queue
    void detach(model_node*& qhead);
    void insert_after(model_node* n);
    model_node* next() const { return m_next; }
    bool in_queue() { return m_next && m_prev; }
};

class model_search {
    typedef ptr_vector<model_node> model_nodes;
    bool               m_bfs;
    model_node*        m_root;
    model_node*        m_qhead;
    vector<obj_map<expr, model_nodes > > m_cache;
    obj_map<expr, model_nodes>& cache(model_node const& n);
    void erase_children(model_node& n, bool backtrack);
    void remove_node(model_node* _n, bool backtrack);

public:
    model_search(bool bfs): m_bfs(bfs), m_root(nullptr), m_qhead(nullptr) {}
    ~model_search() {reset();}

    void set_root(model_node* n);

    void reset();
    model_node* pop_front();
    void add_leaf(model_node* n); // add fresh node.
    model_node& get_root() const { return *m_root; }
    void backtrack_level(bool uses_level, model_node& n);
    void remove_goal(model_node& n);

    void enqueue_leaf(model_node &n);
};
}

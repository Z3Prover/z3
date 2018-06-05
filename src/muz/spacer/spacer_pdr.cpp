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
#include "muz/spacer/spacer_pdr.h"

namespace spacer {
model_node::model_node(model_node* parent, pob_ref &pob):
    m_pob(pob), m_parent(parent), m_next(nullptr), m_prev(nullptr),
    m_orig_level(m_pob->level()), m_depth(0),
    m_closed(false) {
    SASSERT(m_pob);
    if (m_parent) m_parent->add_child(*this);
}

void model_node::add_child(model_node &kid) {
    m_children.push_back(this);
    SASSERT(level() == kid.level() + 1);
    SASSERT(level() > 0);
    kid.m_depth = m_depth + 1;
    if (is_closed()) set_open();
}

unsigned model_node::index_in_parent() const {
    if (!m_parent) return 0;
    for (unsigned i = 0, sz = m_parent->children().size(); i < sz; ++i) {
        if (this == m_parent->children().get(i)) return i;
    }
    UNREACHABLE();
    return 0;
}

void model_node::check_pre_closed() {
    for (auto *kid : m_children) {if (kid->is_open()) return;}

    set_pre_closed();
    model_node* p = m_parent;
    while (p && p->is_1closed()) {
        p->set_pre_closed();
        p = p->parent();
    }
}
void model_node::set_open() {
    SASSERT(m_closed);
    m_closed = false;
    model_node* p = parent();
    while (p && p->is_closed()) {
        p->m_closed = false;
        p = p->parent();
    }
}

void model_node::detach(model_node*& qhead) {
    if (!in_queue()) return;
    SASSERT(children().empty());
    if (this == m_next) {
        SASSERT(m_prev == this);
        SASSERT(this == qhead);
        qhead = nullptr;
    }
    else {
        m_next->m_prev = m_prev;
        m_prev->m_next = m_next;
        if (this == qhead) qhead = m_next;
    }

    // detach
    m_prev = nullptr;
    m_next = nullptr;
}


// insert node n after this in the queue
// requires: this is in a queue or this == n
void model_node::insert_after(model_node* n) {
    SASSERT(!in_queue());
    if (this == n) {
        m_next = n;
        m_prev = n;
    }
    else {
        n->m_next = m_next;
        m_next->m_prev = n;
        m_next = n;
        n->m_prev = this;
    }
}

void model_search::reset() {
    m_cache.reset();
    if (m_root) {
        erase_children(*m_root, false);
        remove_node(*m_root, false);
        dealloc(m_root);
        m_root = nullptr;
    }
}

model_node* model_search::pop_front() {
    if (!m_qhead) return nullptr;
    model_node *res = m_qhead;
    res->detach(m_qhead);
    return res;
}

void model_search::add_leaf(model_node& n) {
    SASSERT(n.children().empty());
    model_nodes ns;
    model_nodes& nodes = cache(n).insert_if_not_there2(n.post(), ns)->get_data().m_value;
    if (nodes.contains(&n)) return;

    nodes.push_back(&n);
    if (nodes.size() == 1) {
        SASSERT(n.is_open());
        enqueue_leaf(n);
    }
    else n.set_pre_closed();
}

void model_search::enqueue_leaf(model_node& n) {
    SASSERT(n.is_open());
    // queue is empty, initialize it with n
    if (!m_qhead) {
        m_qhead  = &n;
        m_qhead->insert_after(m_qhead);
    }
    // insert n after m_qhead
    else if (m_bfs) {
        m_qhead->insert_after(&n);
    }
    // insert n after m_qhead()->next()
    else {
        m_qhead->next()->insert_after(&n);
    }
}



void model_search::set_root(model_node* root) {
    reset();
    m_root = root;
    SASSERT(m_root);
    SASSERT(m_root->children().empty());
    SASSERT(cache(*root).empty());
    // XXX Don't get why 1 is legal here
    cache(*root).insert(root->post(), 1);
    enqueue_leaf(*root);
}

void model_search::backtrack_level(bool uses_level, model_node& n) {
    SASSERT(m_root);
    if (uses_level) {NOT_IMPLEMENTED_YET();}
    if (uses_level && m_root->level() > n.level()) {
        n.increase_level();
        enqueue_leaf(n);
    }
    else {
        model_node* p = n.parent();
        if (p) {
            erase_children(*p, true);
            enqueue_leaf(*p);
        }
    }
}

obj_map<expr, ptr_vector<model_node> >& model_search::cache(model_node const& n) {
    unsigned l = n.orig_level();
    if (l >= m_cache.size()) m_cache.resize(l + 1);
    return m_cache[l];
}

void model_search::erase_children(model_node& n, bool backtrack) {
    ptr_vector<model_node> todo, nodes;
    todo.append(n.children());
    // detach n from queue
    n.detach(m_qhead);
    n.reset();
    while (!todo.empty()) {
        model_node* m = todo.back();
        todo.pop_back();
        nodes.push_back(m);
        todo.append(m->children());
        remove_node(*m, backtrack);
    }
    std::for_each(nodes.begin(), nodes.end(), delete_proc<model_node>());
}

// removes node from the search tree and from the cache
void model_search::remove_node(model_node& n, bool backtrack) {
    model_nodes& nodes = cache(n).find(n.post());
    nodes.erase(&n);
    n.detach(m_qhead);
    // TBD: siblings would also fail if n is not a goal.
    if (!nodes.empty() && backtrack &&
        nodes[0]->children().empty() && nodes[0]->is_closed()) {
        model_node* n1 = nodes[0];
        n1->set_open();
        enqueue_leaf(*n1);
    }

    if (nodes.empty()) cache(n).remove(n.post());
}


}

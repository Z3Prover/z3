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
#include "muz/base/dl_context.h"
#include "muz/spacer/spacer_mbc.h"

namespace spacer {
model_node::model_node(model_node* parent, class pob *pob):
    m_pob(pob), m_parent(parent), m_next(nullptr), m_prev(nullptr),
    m_orig_level(m_pob->level()), m_depth(0),
    m_closed(false) {
    SASSERT(m_pob);
    if (m_parent) m_parent->add_child(this);
}

void model_node::add_child(model_node* kid) {
    m_children.push_back(kid);
    SASSERT(level() == kid->level() + 1);
    SASSERT(level() > 0);
    kid->m_depth = m_depth + 1;
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
    SASSERT(in_queue());
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
    SASSERT(this == n || in_queue());
    SASSERT(n);
    SASSERT(!n->in_queue());
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
    if (m_root) {
        erase_children(*m_root, false);
        remove_node(m_root, false);
        dealloc(m_root);
        m_root = nullptr;
    }
    m_cache.reset();
}

model_node* model_search::pop_front() {
    model_node *res = m_qhead;
    if (res) {
        res->detach(m_qhead);
    }
    return res;
}

void model_search::add_leaf(model_node* _n) {
    model_node& n = *_n;
    SASSERT(n.children().empty());
    model_nodes ns;
    model_nodes& nodes = cache(n).insert_if_not_there2(n.post(), ns)->get_data().m_value;
    if (nodes.contains(&n)) return;

    nodes.push_back(_n);
    if (nodes.size() == 1) {
        SASSERT(n.is_open());
        enqueue_leaf(n);
    }
    else {
        n.set_pre_closed();
    }
}

void model_search::enqueue_leaf(model_node& n) {
    SASSERT(n.is_open());
    SASSERT(!n.in_queue());
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
    add_leaf(root);
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
    if (n.in_queue()) n.detach(m_qhead);
    n.reset_children();
    while (!todo.empty()) {
        model_node* m = todo.back();
        todo.pop_back();
        nodes.push_back(m);
        todo.append(m->children());
        remove_node(m, backtrack);
    }
    std::for_each(nodes.begin(), nodes.end(), delete_proc<model_node>());
}

// removes node from the search tree and from the cache
void model_search::remove_node(model_node* _n, bool backtrack) {
    model_node& n = *_n;
    model_nodes& nodes = cache(n).find(n.post());
    nodes.erase(_n);
    if (n.in_queue()) n.detach(m_qhead);
    // TBD: siblings would also fail if n is not a goal.
    if (!nodes.empty() && backtrack &&
        nodes[0]->children().empty() && nodes[0]->is_closed()) {
        model_node* n1 = nodes[0];
        n1->set_open();
        enqueue_leaf(*n1);
    }

    if (nodes.empty()) cache(n).remove(n.post());
}


lbool context::gpdr_solve_core() {
    scoped_watch _w_(m_solve_watch);
    //if there is no query predicate, abort
    if (!m_rels.find(m_query_pred, m_query)) { return l_false; }

    model_search ms(m_pdr_bfs);
    unsigned lvl = 0;
    unsigned max_level = m_max_level;
    for (lvl = 0; lvl < max_level; ++lvl) {
        checkpoint();
        IF_VERBOSE(1,verbose_stream() << "GPDR Entering level "<< lvl << "\n";);
        STRACE("spacer_progress", tout << "\n* LEVEL " << lvl << "\n";);
        m_expanded_lvl = infty_level();
        m_stats.m_max_query_lvl = lvl;
        if (gpdr_check_reachability(lvl, ms)) {return l_true;}
        if (lvl > 0) {
            if (propagate(m_expanded_lvl, lvl, UINT_MAX)) {return l_false;}
        }
    }

    // communicate failure to datalog::context
    if (m_context) {
        m_context->set_status(datalog::BOUNDED);
    }
    return l_undef;
}

bool context::gpdr_check_reachability(unsigned lvl, model_search &ms) {
    pob_ref root_pob = m_query->mk_pob(nullptr, lvl, 0, m.mk_true());
    model_node *root_node = alloc(model_node, nullptr, root_pob.get());

    ms.set_root(root_node);
    pob_ref_buffer new_pobs;

    while (model_node *node = ms.pop_front()) {
        IF_VERBOSE(2, verbose_stream() << "Expand node: "
                   << node->level() << "\n";);
        new_pobs.reset();
        checkpoint();
        pred_transformer &pt = node->pt();

        // check reachable cache
        if (pt.is_must_reachable(node->pob()->post(), nullptr)) {
            TRACE("spacer",
                  tout << "must-reachable: " << pt.head()->get_name() << " level: "
                  << node->level() << " depth: " << node->depth () << "\n";
                  tout << mk_pp(node->pob()->post(), m) << "\n";);

            node->set_closed();
            if (node == root_node) return true;
            continue;
        }

        switch (expand_pob(*node->pob(), new_pobs)){
        case l_true:
            node->set_closed();
            if (node == root_node) return true;
            break;
        case l_false:
            ms.backtrack_level(false, *node);
            if (node == root_node) return false;
            break;
        case l_undef:
            SASSERT(!new_pobs.empty());
            for (auto pob : new_pobs) {
                TRACE("spacer_pdr",
                      tout << "looking at pob at level " << pob->level() << " "
                      << mk_pp(pob->post(), m) << "\n";);
                if (pob != node->pob())
                    ms.add_leaf(alloc(model_node, node, pob));
            }
            node->check_pre_closed();
            break;
        }
    }

    return root_node->is_closed();
}

bool context::gpdr_create_split_children(pob &n, const datalog::rule &r,
                                         expr *trans,
                                         model &mdl,
                                         pob_ref_buffer &out) {
    pred_transformer &pt = n.pt();
    ptr_vector<func_decl> preds;
    pt.find_predecessors(r, preds);
    SASSERT(preds.size() > 1);

    ptr_vector<pred_transformer> ppts;
    for (auto *p : preds) ppts.push_back(&get_pred_transformer(p));

    mbc::partition_map pmap;
    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
        func_decl *p = preds.get(i);
        pred_transformer &ppt = *ppts.get(i);
        for (unsigned j = 0, jsz = p->get_arity(); j < jsz; ++j) {
            pmap.insert(m_pm.o2o(ppt.sig(j), 0, i), i);
        }
    }


    spacer::mbc _mbc(m);
    expr_ref_vector lits(m);
    flatten_and(trans, lits);
    vector<expr_ref_vector> res(preds.size(), expr_ref_vector(m));
    _mbc(pmap, lits, mdl, res);

    // pick an order to process children
    unsigned_vector kid_order;
    kid_order.resize(preds.size(), 0);
    for (unsigned i = 0, sz = preds.size(); i < sz; ++i) kid_order[i] = i;
    if (m_children_order == CO_REV_RULE) {
        kid_order.reverse();
    }
    else if (m_children_order == CO_RANDOM) {
        shuffle(kid_order.size(), kid_order.c_ptr(), m_random);
    }


    for (unsigned i = 0, sz = res.size(); i < sz; ++i) {
        unsigned j = kid_order[i];
        expr_ref post(m);
        pred_transformer &ppt = *ppts.get(j);
        post = mk_and(res.get(j));
        m_pm.formula_o2n(post.get(), post, j, true);
        pob * k = ppt.mk_pob(&n, prev_level(n.level()), n.depth(), post);
        out.push_back(k);
        IF_VERBOSE (1, verbose_stream()
                    << "\n\tcreate_child: " << k->pt().head()->get_name()
                    << " (" << k->level() << ", " << k->depth() << ") "
                    << (k->use_farkas_generalizer() ? "FAR " : "SUB ")
                    << k->post()->get_id();
                    verbose_stream().flush(););
        TRACE ("spacer",
               tout << "create-pob: " << k->pt().head()->get_name()
               << " level: " << k->level()
               << " depth: " << k->depth ()
               << " fvsz: " << k->get_free_vars_size() << "\n"
               << mk_pp(k->post(), m) << "\n";);


    }

    return true;
}


} // spacer

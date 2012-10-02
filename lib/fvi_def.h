/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    fvi_def.h

Abstract:

    Feature Vector Indexing.

Author:

    Leonardo de Moura (leonardo) 2008-02-01.

Revision History:

--*/
#ifndef _FVI_DEF_H_
#define _FVI_DEF_H_

#include"fvi.h"
#include"splay_tree_def.h"
#include"buffer.h"

template<typename T, typename ToVector, typename Hash, typename Eq>
fvi<T, ToVector, Hash, Eq>::fvi(unsigned num_features, ToVector const & t):
    ToVector(t),
    m_num_features(num_features),
    m_root(0) {
    m_tmp_buffer.resize(num_features, 0);
    m_root = alloc(non_leaf);
    SASSERT(num_features >= 2);
    DEBUG_CODE(m_visiting = false;);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::reset() {
    SASSERT(!m_visiting);
    dealloc(m_root);
    m_root = alloc(non_leaf);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::insert(T * d) {
    SASSERT(!m_visiting);
    to_fvector(d);
    non_leaf * n = m_root;
    unsigned i = 0;
    for (; i < m_num_features - 1; i++) {
        node * child = 0;
        if (!n->m_children.find(m_tmp_buffer[i], child)) { 
            child = alloc(non_leaf);
            n->m_children.insert(m_tmp_buffer[i], child);
        }
        SASSERT(child);
        SASSERT(!child->is_leaf());
        n = static_cast<non_leaf*>(child);
    }
    node * l = 0;
    SASSERT(i == m_num_features - 1);
    if (!n->m_children.find(m_tmp_buffer[i], l)) {
        l = alloc(leaf);
        n->m_children.insert(m_tmp_buffer[i], l);
    }
    SASSERT(l);
    SASSERT(l->is_leaf());
    static_cast<leaf*>(l)->m_set.insert(d);
}
    
template<typename T, typename ToVector, typename Hash, typename Eq>
bool fvi<T, ToVector, Hash, Eq>::contains(T * d) const {
    to_fvector(d);
    non_leaf * n = m_root;
    node * child;
    unsigned i = 0;
    for (; i < m_num_features - 1; i++) {        
        if (!n->m_children.find(m_tmp_buffer[i], child))
            return false;
        SASSERT(child);
        SASSERT(!child->is_leaf());
        n = static_cast<non_leaf*>(child);
    }
    SASSERT(i == m_num_features - 1);
    return 
        n->m_children.find(m_tmp_buffer[i], child) &&
        static_cast<leaf*>(child)->m_set.contains(d);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::erase(T * d) {
    SASSERT(!m_visiting);
    SASSERT(contains(d));
    ptr_buffer<non_leaf> path;
    to_fvector(d);
    non_leaf * n = m_root;
    node * child;
    unsigned i = 0;
    for (; i < m_num_features - 1; i++) {        
        path.push_back(n);
        if (!n->m_children.find(m_tmp_buffer[i], child)) {
            UNREACHABLE();
        }
        SASSERT(child);
        SASSERT(!child->is_leaf());
        n = static_cast<non_leaf*>(child);
    }
    path.push_back(n);    
    SASSERT(i == m_num_features - 1);
    if (!n->m_children.find(m_tmp_buffer[i], child)) {
        UNREACHABLE();
    }
    SASSERT(child);
    SASSERT(child->is_leaf());
    leaf * l = static_cast<leaf*>(child);
    l->m_set.erase(d);
    if (l->m_set.empty()) {
        dealloc(l);
        while (true) {
            non_leaf * n = path.back();
            n->m_children.erase(m_tmp_buffer[i]);
            path.pop_back();
            i--;
            if (!n->m_children.empty() || n == m_root)
                break;
            dealloc(n);
        }
    }
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::non_leaf_stat_visitor::operator()(unsigned k, node * n) {
    if (n->is_leaf())
        m_owner.stats(static_cast<leaf*>(n), m_stats);
    else
        m_owner.stats(static_cast<non_leaf*>(n), m_stats);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::stats(leaf * n, statistics & result) const {
    unsigned sz = n->m_set.size();
    result.m_size += sz;
    if (sz > result.m_max_leaf_size)
        result.m_max_leaf_size = sz;
    if (sz < result.m_min_leaf_size)
        result.m_min_leaf_size = sz;
    result.m_num_leaves ++;
    result.m_num_nodes ++;
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::stats(non_leaf * n, statistics & result) const {
    result.m_num_nodes++;
    // Remark: this function is recursive, but there is no risk
    // of stack overflow since the number of features is small.
    non_leaf_stat_visitor v(*this, result);
    n->m_children.visit(v);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::stats(statistics & result) const {
    result.reset();
    stats(m_root, result);
    if (m_root->m_children.empty())
        result.m_min_leaf_size = 0;
    if (result.m_num_leaves > 0)
        result.m_avg_leaf_size = result.m_size / result.m_num_leaves;
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::non_leaf_collect_visitor::operator()(unsigned k, node * n) {
    if (n->is_leaf())
        m_owner.collect(static_cast<leaf*>(n), m_elems);
    else
        m_owner.collect(static_cast<non_leaf*>(n), m_elems);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::collect(leaf * n, ptr_vector<T> & result) const {
    typename set::iterator it  = n->m_set.begin();
    typename set::iterator end = n->m_set.end();
    for (; it != end; ++it)
        result.push_back(*it);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::collect(non_leaf * n, ptr_vector<T> & result) const {
    // Remark: this function is recursive, but there is no risk
    // of stack overflow since the number of features is small.
    non_leaf_collect_visitor v(*this, result);
    n->m_children.visit(v);
}

template<typename T, typename ToVector, typename Hash, typename Eq>
void fvi<T, ToVector, Hash, Eq>::collect(ptr_vector<T> & result) const {
    collect(m_root, result);
}

#endif /* _FVI_DEF_H_ */

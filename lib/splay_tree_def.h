/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    splay_tree_def.h

Abstract:

    Splay trees

Author:

    Leonardo de Moura (leonardo) 2008-01-31.

Revision History:

--*/
#ifndef _SPLAY_TREE_DEF_H_
#define _SPLAY_TREE_DEF_H_

#include"splay_tree.h"

template<typename Key, typename Compare>
typename splay_tree<Key, Compare>::cell * splay_tree<Key, Compare>::splay(cell * root, Key const & k) {
    if (!root) 
        return 0;
    
    cell aux;
    cell * tmp;
    cell * left  = &aux;
    cell * right = &aux;
    cell * t     = root;
    
    while (true) {
        int r = compare(k, t->m_key);
        if (r < 0) {
            if (!t->m_left)
                break;
            if (compare(k, t->m_left->m_key) < 0) {
                tmp          = t->m_left;
                t->m_left    = tmp->m_right;
                tmp->m_right = t;
                t            = tmp;
                if (!t->m_left)
                    break;
            }
            right->m_left = t;
            right         = t;
            t             = t->m_left;
        }
        else if (r > 0) {
            if (!t->m_right)
                break;
            if (compare(k, t->m_right->m_key) > 0) {
                tmp          = t->m_right;
                t->m_right   = tmp->m_left;
                tmp->m_left  = t;
                t            = tmp;
                if (!t->m_right)
                    break;
                
            }
            left->m_right = t;
            left          = t;
            t             = t->m_right;
        }
        else 
            break;
    }
    
    left->m_right = t->m_left;
    right->m_left = t->m_right;
    t->m_left     = aux.m_right;
    t->m_right    = aux.m_left;
    
    return t;
}

template<typename Key, typename Compare>
void splay_tree<Key, Compare>::insert(Key const & k) {
    if (!m_root) 
        m_root = alloc(cell, k);
    else {
        m_root = splay(m_root, k);
        int r = compare(k, m_root->m_key);
        if (r < 0) {
            cell * new_cell   = alloc(cell, k, m_root->m_left, m_root);
            m_root->m_left    = 0;
            m_root            = new_cell;
        }
        else if (r > 0) {
            cell * new_cell   = alloc(cell, k, m_root, m_root->m_right);
            m_root->m_right   = 0;
            m_root            = new_cell;
        }
        else
            m_root->m_key     = k;
    }
}

template<typename Key, typename Compare>
bool splay_tree<Key, Compare>::find(Key const & k, Key & r) const {
    if (m_root) {
        splay_tree<Key, Compare> * _this = const_cast<splay_tree<Key, Compare> *>(this);
        _this->m_root = _this->splay(m_root, k);
        if (compare(k, m_root->m_key) == 0) {
            r = m_root->m_key;
            return true;
        }
    }
    return false;
}

template<typename Key, typename Compare>
void splay_tree<Key, Compare>::erase(Key const & k) {
    if (m_root) {
        m_root = splay(m_root, k);
        if (compare(k, m_root->m_key) == 0) {
            cell * to_delete = m_root;
            if (m_root->m_left) {
                cell * aux = splay(m_root->m_left, k);
                SASSERT(!aux->m_right);
                aux->m_right = m_root->m_right;
                m_root       = aux;
            }
            else
                m_root = m_root->m_right;

            dealloc(to_delete);
        }
    }
}

template<typename Key, typename Compare>
void splay_tree<Key, Compare>::reset() {
    ptr_buffer<cell> todo;
    if (m_root) 
        todo.push_back(m_root);
    while (!todo.empty()) {
        cell * c = todo.back();
        todo.pop_back();
        if (c->m_left)
            todo.push_back(c->m_left);
        if (c->m_right)
            todo.push_back(c->m_right);
        dealloc(c);
    }
    m_root = 0;
}

#endif /* _SPLAY_TREE_DEF_H_ */

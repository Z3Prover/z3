/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    top_sort.h

Abstract:
    Topological sort over objects

Author:

    Nikolaj Bjorner (nbjorner) 2018-02-14

Revision History:

--*/

#pragma once

#include<algorithm>
#include<type_traits>
#include<memory.h>
#include "util/obj_hashtable.h"
#include "util/vector.h"
#include "util/memory_manager.h"
#include "util/tptr.h"


template<typename T>
class top_sort {
    typedef obj_hashtable<T> T_set;
    unsigned_vector      m_partition_id;
    unsigned_vector      m_dfs_num;
    ptr_vector<T>        m_top_sorted;
    ptr_vector<T>        m_stack_S;
    ptr_vector<T>        m_stack_P;
    unsigned             m_next_preorder;    
    ptr_vector<T_set>    m_deps;
    ptr_vector<T>        m_dep_keys;

    static T_set*  add_tag(T_set* t) { return TAG(T_set*, t, 1); }
    static T_set*  del_tag(T_set* t) { return UNTAG(T_set*, t); }


    bool contains_partition(T* f) const {
        return m_partition_id.get(f->get_small_id(), UINT_MAX) != UINT_MAX;
    }


    void traverse(T* f) {
        unsigned p_id = m_dfs_num.get(f->get_small_id(), UINT_MAX);
        if (p_id != UINT_MAX) {
            if (!contains_partition(f)) {
                while (!m_stack_P.empty() && contains_partition(m_stack_P.back()) && partition_id(m_stack_P.back()) > p_id) {
                    m_stack_P.pop_back();
                }
            }
        }
        else if (!contains_dep(f))
            return;
        else {
            m_dfs_num.setx(f->get_small_id(), m_next_preorder, UINT_MAX);
            ++m_next_preorder;
            m_stack_S.push_back(f);
            m_stack_P.push_back(f);
            T_set* ts = get_dep(f);
            if (ts) {
                for (T* g : *ts)
                    traverse(g);
            }
            if (f == m_stack_P.back()) {                
                p_id = m_top_sorted.size();            
                T* s_f;
                do {
                    s_f = m_stack_S.back();
                    m_stack_S.pop_back();
                    m_top_sorted.push_back(s_f);
                    m_partition_id.setx(s_f->get_small_id(), p_id, UINT_MAX);
                } 
                while (s_f != f);
                m_stack_P.pop_back();
            }
        }
    }

public:

    virtual ~top_sort() {
        for (auto * t : m_dep_keys) {
            dealloc(get_dep(t));
            m_deps[t->get_small_id()] = nullptr;
        }
    }

    void topological_sort() {
        m_next_preorder = 0;
        m_partition_id.reset();
        m_top_sorted.reset();
        for (auto * t : m_dep_keys) 
            traverse(t);
        SASSERT(m_stack_S.empty());
        SASSERT(m_stack_P.empty());
        m_dfs_num.reset();        
    }

    void insert(T* t, T_set* s) {
        if (contains_dep(t)) 
            dealloc(get_dep(t));
        else 
            m_dep_keys.push_back(t);
        m_deps.setx(t->get_small_id(), add_tag(s), nullptr);
    }

    ptr_vector<T> const& deps() { return m_dep_keys; }

    void add(T* t, T* s) {
        T_set* tb = get_dep(t); 
        if (!tb) {
            tb = alloc(T_set);
            insert(t, tb);
        }
        tb->insert(s);
    }

    ptr_vector<T> const& top_sorted() const { return m_top_sorted; }    

    unsigned partition_id(T* t) const { return m_partition_id[t->get_small_id()]; }

    bool find(T* t, unsigned& p) const { p = m_partition_id.get(t->get_small_id(), UINT_MAX); return p != UINT_MAX; }

    bool contains_dep(T* t) const { return m_deps.get(t->get_small_id(), nullptr) != nullptr; }

    T_set* get_dep(T* t) const { return del_tag(m_deps.get(t->get_small_id(), nullptr)); }


    bool is_singleton_partition(T* f) const {
        unsigned pid = m_partition_id(f);
        return f == m_top_sorted[pid] &&
            (pid == 0 || partition_id(m_top_sorted[pid-1]) != pid) && 
            (pid + 1 == m_top_sorted.size() || partition_id(m_top_sorted[pid+1]) != pid);        
    }

};


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

#ifndef TOP_SORT_H_
#define TOP_SORT_H_

#include "util/obj_hashtable.h"
#include "util/vector.h"
#include<algorithm>
#include<type_traits>
#include<memory.h>
#include "util/memory_manager.h"


template<typename T>
class top_sort {
    typedef obj_hashtable<T> T_set;
    obj_map<T, unsigned> m_partition_id;
    obj_map<T, unsigned> m_dfs_num;
    ptr_vector<T>        m_top_sorted;
    ptr_vector<T>        m_stack_S;
    ptr_vector<T>        m_stack_P;
    unsigned             m_next_preorder;    
    obj_map<T, T_set*>   m_deps;

    void traverse(T* f) {
        unsigned p_id = 0;
        if (m_dfs_num.find(f, p_id)) {
            if (!m_partition_id.contains(f)) {
                while (!m_stack_P.empty() && m_partition_id.contains(m_stack_P.back()) && m_partition_id[m_stack_P.back()] > p_id) {
                    m_stack_P.pop_back();
                }
            }
        }
        else if (!m_deps.contains(f)) {
            return;
        }
        else {
            m_dfs_num.insert(f, m_next_preorder++);        
            m_stack_S.push_back(f);
            m_stack_P.push_back(f);  
            for (T* g : *m_deps[f]) {
                traverse(g);
            }        
            if (f == m_stack_P.back()) {
                
                p_id = m_top_sorted.size();            
                T* s_f;
                do {
                    s_f = m_stack_S.back();
                    m_stack_S.pop_back();
                    m_top_sorted.push_back(s_f);
                    m_partition_id.insert(s_f, p_id);
                } 
                while (s_f != f);
                m_stack_P.pop_back();
        }
        }
    }

public:

    ~top_sort() {
        for (auto & kv : m_deps) dealloc(kv.m_value);
    }

    void topological_sort() {
        m_next_preorder = 0;
        m_partition_id.reset();
        m_top_sorted.reset();
        for (auto & kv : m_deps) {
            traverse(kv.m_key);
        }
        SASSERT(m_stack_S.empty());
        SASSERT(m_stack_P.empty());
        m_dfs_num.reset();        
    }

    void insert(T* t, T_set* s) { 
        m_deps.insert(t, s); 
    }

    ptr_vector<T> const& top_sorted() { return m_top_sorted; }    
};

#endif /* TOP_SORT_H_ */

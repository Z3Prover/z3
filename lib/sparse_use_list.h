/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    sparse_use_list.h

Abstract:

    Sparse use list index.

Author:

    Leonardo de Moura (leonardo) 2008-02-13.

Revision History:

--*/
#ifndef _SPARSE_USE_LIST_H_
#define _SPARSE_USE_LIST_H_

#include"ast.h"
#include"obj_hashtable.h"

/**
   \brief (Generic sparse) use-list data-structure.
*/
template<typename T, typename Set>
class sparse_use_list {
    typedef obj_map<T, Set *> use_list;
    use_list        m_use_list;

public:
    typedef typename Set::iterator iterator;
    sparse_use_list() {}
    ~sparse_use_list() { 
        reset();
    }

    void insert(typename Set::data const & parent, T * child) {
        Set * parents = 0;
        if (!m_use_list.find(child, parents)) {
            parents = alloc(Set);
            m_use_list.insert(child, parents);
        }
        SASSERT(parents);
        parents->insert(parent);
    }

    /**
       \brief Return 0 if child did not contain any parents.
       Return 1, if child does not have more parents after 
       removing parent.
       Return 2 otherwise.
    */
    unsigned erase(typename Set::data const & parent, T * child) {
        Set * parents = 0;
        if (m_use_list.find(child, parents)) {
            parents->erase(parent);
            if (parents->empty()) {
                dealloc(parents);
                m_use_list.erase(child);
                return 1;
            }
            return 2;
        }
        return 0;
    }

    void reset() {
        typename use_list::iterator it  = m_use_list.begin();
        typename use_list::iterator end = m_use_list.end();
        for (; it != end; ++it)
            dealloc(it->m_value);
        m_use_list.reset();
    }

    Set * get_parents(T * e) {
        Set * parents = 0;
        m_use_list.find(e, parents);
        return parents;
    }
    
    iterator begin(T * e) {
        Set * parents = 0;
        m_use_list.find(e, parents);
        SASSERT(parents);
        return parents->begin();
    }

    iterator end(T * e) {
        Set * parents = 0;
        m_use_list.find(e, parents);
        SASSERT(parents);
        return parents->end();
    }

    bool empty(T * e) const {
        Set * parents = 0;
        if (m_use_list.find(e, parents))
            return parents->empty();
        return true;
    }
};

#endif /* _SPARSE_USE_LIST_H_ */


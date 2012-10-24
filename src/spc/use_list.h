/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    use_list.h

Abstract:

    Use list expression index.

Author:

    Leonardo de Moura (leonardo) 2008-02-04.

Revision History:

--*/
#ifndef _USE_LIST_H_
#define _USE_LIST_H_

#include"ast.h"
#include"vector.h"

/**
   \brief Generic use-list data-structure.
*/
template<typename T>
class use_list {
    typedef vector<T> set;
    vector<set> m_use_list;
public:
    typedef typename set::const_iterator iterator;
    use_list() {}
    
    void insert(T const & parent, expr * child) {
        unsigned id  = child->get_id();
        if (id >= m_use_list.size())
            m_use_list.resize(id+1, set());
        set & s = m_use_list[id];
        s.push_back(parent);
    }
    
    void erase(T const & parent, expr * child) {
        unsigned id  = child->get_id();
        if (id >= m_use_list.size())
            return;
        set & s = m_use_list[id];
        s.erase(parent);
    }

    void reset() {
        m_use_list.reset();
    }
    
    iterator begin(expr * e) const {
        unsigned id = e->get_id();
        if (id >= m_use_list.size())
            return 0;
        return m_use_list[id].begin();
    }
    
    iterator end(expr * e) const {
        unsigned id = e->get_id();
        if (id >= m_use_list.size())
            return 0;
        return m_use_list[id].end();
    }

    bool empty(expr * e) const {
        unsigned id = e->get_id();
        if (id >= m_use_list.size())
            return true;
        return m_use_list[id].empty();
    }
};

/**
   \brief Index for tracking the uses of an expression. It is a
   mapping from expressions to expressions. For example, consider the
   term (f a (g a)), the constant a is used by f and g applications.
   
   \remark The expressions inserted in this index should not contain
   quantifiers.

   \warning This index will not increase the reference counter of the
   indexed expressions.
*/
class app_use_list : use_list<app*> {
    
    bool m_ignore_vars; //!< when true, variables are not indexed
    unsigned_vector  m_ref_counter;
    ptr_vector<app> m_todo;

    void inc_ref(app * n);
    void dec_ref(app * n);

public:
    /**
       \brief If ignore_vars = true, then the index will not track
       the use of variables.
    */
    app_use_list(bool ignore_vars = true):
        m_ignore_vars(ignore_vars) {
    }

    /**
       \brief Update the use list of all direct/indirect children of n.
    */
    void insert(expr * n);

    /**
       \brief Remove n (and its unreachable direct/indirect children) from the index.
    */
    void erase(expr * n);
    
    void reset();
};

#endif /* _USE_LIST_H_ */

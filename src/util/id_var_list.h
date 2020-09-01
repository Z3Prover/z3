/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    id_var_list.h

Abstract:

    Association list from theory id -> var
    where id in [0..255] and var is 24 bit.

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

    Extracted from smt_theory_var_list 
--*/
#pragma once

#include "util/region.h"
#include "util/debug.h"

template <int null_id = -1, int null_var = -1>
class id_var_list {
    int               m_id:8;
    int               m_var:24;
    id_var_list *     m_next;
    
public:
    id_var_list():
        m_id(null_id),
        m_var(null_var), 
        m_next(nullptr) {
    }
    
    id_var_list(int t, int v, id_var_list * n = nullptr):
        m_id(t),
        m_var(v),
        m_next(n) {
    }
    
    int get_id() const {
        return m_id;
    }
    
    int get_var() const {
        return m_var;
    }

    bool empty() const {
        return get_var() == null_var;
    }
    
    int find(int id) const {
        if (empty())
            return null_var;
        auto l = this;
        do {
            if (id == l->get_id())
                return l->get_var();
            l = l->get_next();
        }
        while (l);
        return null_var;
    }
    
    unsigned size() const {
        if (empty())
            return 0;
        unsigned r = 0;
        auto l = this;
        while (l) {
            ++r;
            l = l->get_next();
        }
        return r;
    }
    
    void add_var(int v, int id, region& r) {
        SASSERT(find(id) == null_var);
        if (get_var() == null_var) {
            m_var = v;
            m_id = id;
            m_next = nullptr;
            }
        else {
            auto l = this;
            while (l->get_next()) {
                SASSERT(l->get_id() != id);
                l = l->get_next();
            }
            SASSERT(l); 
            SASSERT(!l->get_next());
            auto * new_cell = new (r) id_var_list<null_id, null_var>(id, v);
            l->set_next(new_cell);
        }
        SASSERT(find(id) == v);            
    }

    /**
       \brief Replace the entry (v', id) with the entry (v, id).
       The enode must have an entry (v', id)
    */
    void replace(int v, int id) {
        SASSERT(find(id) != null_var);
        auto l = this;
        while (l) {
            if (l->get_id() == id) {
                l->set_var(v);
                return;
            }
            l = l->get_next();
        }
        UNREACHABLE();
    }

    /**
       \brief Delete theory variable. It assumes the 
       enode is associated with a variable of the given theory.
    */
    void del_var(int id) {
        SASSERT(find(id) != null_var);
        if (get_id() == id) {
            if (!m_next) {
                // most common case
                m_var = null_var;
                m_id = null_id;
            }
            else {
                m_var = m_next->get_var();
                m_id = m_next->get_id();
                m_next = m_next->get_next();
            }
        }
        else {
            auto* prev = this;
            auto* l    = prev->get_next();
            while (l) {
                SASSERT(prev->get_next() == l);
                if (l->get_id() == id) {
                    prev->set_next(l->get_next());
                    return;
                }
                prev = l;
                l    = l->get_next();
            }
            UNREACHABLE();
        }
    }
    
    id_var_list * get_next() const {
        return m_next;
    }
    
    void set_id(int id) {
        m_id = id;
    }
    
    void set_var(int v) {
        m_var = v;
    }
    
    void set_next(id_var_list * next) {
        m_next = next;
    }
};

// 32 bit machine
static_assert(sizeof(unsigned*) != 4 || sizeof(id_var_list<>) == sizeof(id_var_list<> *) + sizeof(int), "32 bit"); 
// 64 bit machine
static_assert(sizeof(unsigned*) != 8 || sizeof(id_var_list<>) == sizeof(id_var_list<> *) + sizeof(int) + /* a structure must be aligned */ sizeof(int), "64 bit"); 



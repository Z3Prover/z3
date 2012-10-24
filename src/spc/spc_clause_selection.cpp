/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_clause_selection.cpp

Abstract:

    Superposition Calculus Clause Selection

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#include"spc_clause_selection.h"

namespace spc {
  
    const unsigned default_heap_size = 1024;

    clause_selection::clause_selection(unsigned num_heaps, clause_eval * const * fs, unsigned * slot_size):
        m_curr_slot(0),
        m_counter(0),
        m_fs(num_heaps, fs) {
        SASSERT(num_heaps > 0);
        for (unsigned i = 0; i < num_heaps; i++) {
            m_heaps.push_back(alloc(heap<lt>, default_heap_size, lt(m_id2clause, *(fs[i]))));
            SASSERT(slot_size[i] > 0);
            m_slot_size.push_back(slot_size[i]);
        }
    }

    clause_selection::~clause_selection() {
        std::for_each(m_heaps.begin(), m_heaps.end(), delete_proc<heap<lt> >());
        std::for_each(m_fs.begin(), m_fs.end(), delete_proc<clause_eval>());
    }

    void clause_selection::reserve(unsigned cid) {
        unsigned capacity = m_heaps[0]->get_bounds();
        if (cid >= capacity) {
            unsigned new_capacity = 2 * cid + 1;
            SASSERT(cid < new_capacity);
            ptr_vector<heap<lt> >::iterator it  = m_heaps.begin();
            ptr_vector<heap<lt> >::iterator end = m_heaps.end();
            for (; it != end; ++it) {
                heap<lt> * h = *it;
                h->reserve(new_capacity);;
            }
        }
    }

    void clause_selection::reset() {
        ptr_vector<heap<lt> >::iterator it  = m_heaps.begin();
        ptr_vector<heap<lt> >::iterator end = m_heaps.end();
        for (; it != end; ++it) {
            heap<lt> * h = *it;
            h->reset();
        }
    }
    
    void clause_selection::insert(clause * c) {
        reserve(c->get_id());
        m_id2clause.insert(c);
        ptr_vector<heap<lt> >::iterator it  = m_heaps.begin();
        ptr_vector<heap<lt> >::iterator end = m_heaps.end();
        for (; it != end; ++it) {
            heap<lt> * h = *it;
            h->insert(c->get_id());
        }
    }
    
    void clause_selection::erase(clause * c) {
        // remark: it is not necessary to remove c from m_id2clause
        ptr_vector<heap<lt> >::iterator it  = m_heaps.begin();
        ptr_vector<heap<lt> >::iterator end = m_heaps.end();
        SASSERT(it != end);
        if (!(*it)->contains(c->get_id()))
            return;
        for (; it != end; ++it) {
            heap<lt> * h = *it;
            h->erase(c->get_id());
        }
    }

    bool clause_selection::empty() const {
        ptr_vector<heap<lt> >::const_iterator it  = m_heaps.begin();
        ptr_vector<heap<lt> >::const_iterator end = m_heaps.end();
        for (; it != end; ++it)
            if (!(*it)->empty())
                return false;
        return true;
    }
    
    clause * clause_selection::get_best() {
        heap<lt> * h = m_heaps[m_curr_slot];
        if (h->empty())
            return 0;
        unsigned cid = m_heaps[m_curr_slot]->erase_min();
        clause * c = m_id2clause(cid);
        SASSERT(c);
        // remove clause from the other heaps
        unsigned num_heaps = m_heaps.size();
        for (unsigned i = 0; i < num_heaps; i++) {
            if (m_curr_slot != i)
                m_heaps[i]->erase(cid);
        }
        // remark: it is not necessary to remove c from m_id2clause
        m_counter++;
        if (m_counter >= m_slot_size[m_curr_slot]) {
            m_counter = 0;
            m_curr_slot++;
            if (m_curr_slot >= m_slot_size.size()) 
                m_curr_slot = 0;
        }
        return c;
    }
};

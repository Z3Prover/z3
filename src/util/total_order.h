/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    total_order.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-07-01.

Revision History:

--*/
#pragma once

#include "util/util.h"
#include "util/small_object_allocator.h"
#include "util/map.h"
#include "util/uint_map.h"
#include "util/trace.h"

/**
   \brief An object for maintaining a total-order on sets of T values.
   \c Map should be a class implementing the map API for T to void *.

*/
template<typename T, typename Map>
class total_order {
    struct cell {
        cell * m_next;
        cell * m_prev;
        uint64_t m_val;
        T      m_data;
    };
    
    small_object_allocator * m_allocator;
    bool                     m_own_allocator;
    Map                      m_map;
    cell                     m_base;
    unsigned                 m_size;

    cell * base() const { return const_cast<cell*>(&m_base); }

    void init_base() {
        m_base.m_next = &m_base;
        m_base.m_prev = &m_base;
        m_base.m_val  = 0;
    }

    uint64_t v(cell * a) const { return a->m_val; }

    uint64_t vb(cell * a) const { return v(a) - v(base()); }

    uint64_t vbn(cell * a) const { return a->m_next == base() ? UINT64_MAX : vb(a->m_next); }
        
    cell * mk_cell(T const & a) {
        SASSERT(!m_map.contains(a));
        cell * c  = reinterpret_cast<cell*>(m_allocator->allocate(sizeof(cell)));
        m_map.insert(a, c);
        c->m_data = a;
        m_size++;
        return c;
    }

    void del_cell(cell * c) {
#ifdef Z3DEBUG
        T d = c->m_data;
#endif
        m_map.erase(c->m_data);
        m_allocator->deallocate(sizeof(cell), c);
        m_size--;
        SASSERT(!m_map.contains(d));
    }
    
    cell * to_cell(T const & a) const {
        void * r = m_map.find(a);
        return reinterpret_cast<cell*>(r);
    }

    void _insert_after(cell * a, cell * b) {
        uint64_t vb_a  = vb(a);
        uint64_t vbn_a = vbn(a);
        SASSERT(vb_a < vbn_a);
        if (vbn_a < 2 || (vb_a > vbn_a - 2)) {
            TRACE("total_order", tout << "relabeling...\n"; tout << "\n";);
            uint64_t  v0       = v(a);
            unsigned sz        = size();
            uint64_t ideal_gap = UINT64_MAX / sz;
            uint64_t goal_gap  = ideal_gap / 32;
            cell * c           = a->m_next->m_next;
            unsigned j         = 2;
            uint64_t curr_gap  = (v(c) - v0) / j;
            while (j < sz && curr_gap < goal_gap) {
                j++;
                c         = c->m_next;
                curr_gap  = (v(c) - v0) / j; 
            }
            TRACE("total_order", tout << "j: " << j << " curr_gap: " << curr_gap << " sz: " << sz << "\n";);
            if (j == sz)
                curr_gap  = ideal_gap;
            c = a->m_next;
            uint64_t inc    = curr_gap;
            for (unsigned i = 0; i < j; i++) {
                c->m_val  = v0 + inc;
                c         = c->m_next;
                inc      += curr_gap;
            }
            CASSERT("total_order", check_invariant());
            vb_a  = vb(a);
            vbn_a = vbn(a);
        }
        SASSERT(vb_a <= vbn_a - 2);
        uint64_t vb_b = vb_a + ((vbn_a - vb_a)/2);
        SASSERT(vb_b > vb_a);
        SASSERT(vb_b < vbn_a);
        b->m_val          = vb_b + v(base()); 
        b->m_next         = a->m_next;
        a->m_next->m_prev = b;
        b->m_prev         = a;
        a->m_next         = b;
        SASSERT(vb(a) < vb(b));
        CASSERT("total_order", check_invariant());
    }
    
    void insert_core(cell * a) {
        _insert_after(base(), a);
    }
    
    void remove_cell(cell * a) {
        SASSERT(a != base());
        cell * p = a->m_prev;
        cell * n = a->m_next;
        p->m_next = n;
        n->m_prev = p;
    }

    void move_after(cell * a, cell * b) {
        if (a->m_next == b)
            return;
        remove_cell(b);
        _insert_after(a, b);
    }

    void move_beginning(cell * b) {
        if (base()->m_next == b)
            return; // already in the beginning
        remove_cell(b);
        insert_core(b);
    }
    
    void erase(cell * a) {
        remove_cell(a);
        del_cell(a);
    }
    
public:
    total_order():
        m_allocator(alloc(small_object_allocator)),
        m_own_allocator(true),
        m_size(0) {
        init_base();
    }

    total_order(Map const & m):
        m_allocator(alloc(small_object_allocator)),
        m_own_allocator(true),
        m_map(m),
        m_size(0) {
        init_base();
    }

    total_order(small_object_allocator * allocator):
        m_allocator(allocator),
        m_own_allocator(false),
        m_size(0) {
        init_base();
    }

    total_order(small_object_allocator * allocator, Map const & m):
        m_allocator(allocator),
        m_own_allocator(false),
        m_map(m),
        m_size(0) {
        init_base();
    }
    
    ~total_order() {
        cell * curr = base()->m_next;
        while (curr != base()) {
            cell * c = curr;
            curr = curr->m_next;
            del_cell(c);
        }
        if (m_own_allocator)
            dealloc(m_allocator);
    }

    /**
       \brief Return true if \c a is in the total order.
    */
    bool contains(T const & a) const { 
        return m_map.contains(a); 
    }

    /**
       \brief Insert \c a in the beginning of the total order.

       \pre \c a must not be an element of the total order.
    */
    void insert(T const & a) { 
        SASSERT(!contains(a)); 
        insert_core(mk_cell(a)); 
    }

    /**
       \brief Insert \c b after \c a in the total order.

       \pre \c a is an element of the total order.
       \pre \c b must not be an element of the total order.
    */
    void insert_after(T const & a, T const & b) { 
        SASSERT(contains(a)); 
        SASSERT(!contains(b)); 
        _insert_after(to_cell(a), mk_cell(b)); 
        SASSERT(lt(a, b));
    } 

    /**
       \brief Move \c a to the beginning of the total order.

       \pre \c a is an element of the total order.
    */
    void move_beginning(T const & a) { 
        SASSERT(contains(a)); 
        move_beginning(to_cell(a)); 
    }

    /**
       \brief Move \b after \c a in the total order.

       \pre \c a is an element of the total order.
       \pre \c b is an element of the total order.
       \pre \c a must be different from \c b.
    */
    void move_after(T const & a, T const & b) { 
        SASSERT(contains(a)); 
        SASSERT(contains(b)); 
        move_after(to_cell(a), to_cell(b)); 
        SASSERT(lt(a, b));
    }
    
    /**
       \brief Remove \c a from the total order.

       \pre \c a is an element of the total order.
    */
    void erase(T const & a) { 
        SASSERT(contains(a)); 
        erase(to_cell(a)); 
    }
    
    /**
       \brief Return true if \c a is less than \c b in the total order.
    */
    bool lt(T const & a, T const & b) const { 
        SASSERT(contains(a)); 
        SASSERT(contains(b)); 
        return vb(to_cell(a)) < vb(to_cell(b)); 
    }

    /**
       \brief Return true if \c a is greater than \c b in the total order.
    */
    bool gt(T const & a, T const & b) const { 
        SASSERT(contains(a)); 
        SASSERT(contains(b)); 
        return vb(to_cell(a)) > vb(to_cell(b)); 
    }

    /**
       \brief Return true if the total order is empty.
    */
    bool empty() const { 
        return base()->m_next == base(); 
    }

    /**
       \brief Return the number of elements in the total order.
    */
    unsigned size() const {
        return m_size;
    }

    /**
       \brief Return the first element of the total order.
    */
    T const & first() const {
        SASSERT(!empty());
        return base()->m_next->m_data;
    }

    /**
       \brief Return true if \c a has a successor in the total order.
       
       \pre \c a is an element of the total order.
    */
    bool has_next(T const & a) const { 
        SASSERT(contains(a));
        return to_cell(a)->m_next != base(); 
    }

    /**
       \brief Return the successor of \c a in the total order.
       
       \pre \c a is an element of the total order.
       \pre has_next(a)
    */
    T const & next(T const & a) const { 
        SASSERT(contains(a));
        SASSERT(has_next(a)); 
        return to_cell(a)->m_next->m_data; 
    }

    /**
       \brief Return true if \c a has a predecessor in the total order.
       
       \pre \c a is an element of the total order.
    */
    bool has_pred(T const & a) const { 
        SASSERT(contains(a));
        return to_cell(a)->m_prev != base(); 
    }

    /**
       \brief Return the predecessor of \c a in the total order.
       
       \pre \c a is an element of the total order.
       \pre has_pred(a)
    */
    T const & pred(T const & a) const { 
        SASSERT(has_pred(a)); 
        return to_cell(a)->m_prev->m_data; 
    }

    /**
       \brief Display the elements of the total order in increasing order.
       
       \remark For debugging purposes.
    */
    void display(std::ostream & out) const {
        cell * curr = base()->m_next;
        bool first = true;
        while (curr != base()) {
            if (first)
                first = false;
            else
                out << " ";
            out << curr->m_data;
            curr = curr->m_next;
        }
    }

    void display_detail(std::ostream & out) const {
        cell * curr = base()->m_next;
        bool first = true;
        while (curr != base()) {
            if (first)
                first = false;
            else
                out << " ";
            out << curr->m_data << ":" << curr->m_val;
            curr = curr->m_next;
        }
    }

#ifdef Z3DEBUG
    bool check_invariant() const {
        cell * curr = base()->m_next;
        while (curr != base()) {
            SASSERT(curr->m_next == base() || vb(curr) < vb(curr->m_next));
            curr = curr->m_next;
        }
        return true;
    }
#endif

};

typedef total_order<int, map<int, void*, int_hash, int_eq> > int_total_order;

/**
   \brief A total order that uses vectors to implement a mapping from unsigned to void *.
*/
typedef total_order<unsigned, uint_map<void> > uint_total_order;

template<typename T, typename Map>
std::ostream & operator<<(std::ostream & out, total_order<T, Map> const & to) {
    to.display(out);
    return out;
}




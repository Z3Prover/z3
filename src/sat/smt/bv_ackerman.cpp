/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_ackerman.cpp

Abstract:

    Ackerman reduction plugin for bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-28

--*/

#include "sat/smt/bv_solver.h"
#include "sat/smt/bv_ackerman.h"

namespace bv {

    ackerman::ackerman(solver& s): s(s) {
        new_tmp();
    }

    ackerman::~ackerman() {
        reset();
        dealloc(m_tmp_vv);
    }

    void ackerman::reset() {
        m_table.reset();
        m_queue = nullptr;        
    }

    void ackerman::used_eq_eh(euf::theory_var v1, euf::theory_var v2) {
        if (v1 == v2)
            return;
        if (v1 > v2)
            std::swap(v1, v2);
        vv* n = m_tmp_vv;
        n->v1 = v1;
        n->v2 = v2;
        vv* other = m_table.insert_if_not_there(n);
        other->m_count++;
        push_to_front(other);

        if (other == n) {
            new_tmp();        
            gc();
        }
    }

    void ackerman::remove_from_queue(vv* p) {
        if (m_queue->m_next == m_queue) {
            SASSERT(p == m_queue);
            m_queue = nullptr;
            return;
        }            
        if (m_queue == p) 
            m_queue = p->m_next;
        auto* next = p->m_next;
        auto* prev = p->m_prev;
        prev->m_next = next;
        next->m_prev = prev;        
    }

    void ackerman::push_to_front(vv* p) {
        if (!m_queue) {
            m_queue = p;
        }
        else if (m_queue != p) {
            auto* next = p->m_next;
            auto* prev = p->m_prev;
            prev->m_next = next;
            next->m_prev = prev;
            p->m_prev = m_queue->m_prev;
            p->m_next = m_queue;
            m_queue->m_prev = p;
        }
    }

    void ackerman::remove(vv* p) {
        remove_from_queue(p);
        m_table.erase(p);
        dealloc(p);
    }

    void ackerman::new_tmp() {
        m_tmp_vv = alloc(vv);
        m_tmp_vv->m_next = m_tmp_vv->m_prev = m_tmp_vv;
        m_tmp_vv->m_count = 0;
    }
        
    void ackerman::gc() {
        m_num_propagations_since_last_gc++;
        if (m_num_propagations_since_last_gc <= s.get_config().m_dack_gc) 
            return;
        m_num_propagations_since_last_gc = 0;
        
        while (m_table.size() > m_gc_threshold) 
            remove(m_queue->m_prev);     

        m_gc_threshold *= 110;
        m_gc_threshold /= 100;
        m_gc_threshold++;
    }

    void ackerman::propagate() {
        SASSERT(s.s().at_base_lvl());
        auto* n = m_queue;
        vv* k = nullptr;
        unsigned num_prop = static_cast<unsigned>(s.s().get_stats().m_conflict * s.get_config().m_dack_factor);
        num_prop = std::min(num_prop, m_table.size());
        for (unsigned i = 0; i < num_prop; ++i, n = k) {
            k = n->m_next;
            if (n->m_count < s.get_config().m_dack_threshold) 
                continue;
            add_cc(n->v1, n->v2);
            remove(n);
        }
    }

    void ackerman::add_cc(euf::theory_var v1, euf::theory_var v2) {
        SASSERT(v1 < v2);
        if (static_cast<unsigned>(v2) >= s.get_num_vars())
            return;
        if (!s.var2enode(v1) || !s.var2enode(v2))
            return;
        sort* s1 = s.m.get_sort(s.var2expr(v1));
        sort* s2 = s.m.get_sort(s.var2expr(v2));
        if (s1 != s2 || !s.bv.is_bv_sort(s1))
            return;
        s.assert_ackerman(v1, v2);
    }

}

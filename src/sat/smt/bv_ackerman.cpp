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
        m_propagate_low_watermark = s.get_config().m_dack_threshold;
    }

    ackerman::~ackerman() {
        reset();
        dealloc(m_tmp_vv);
    }

    void ackerman::reset() {
        while (m_queue)
            remove(m_queue->prev());     
        m_table.reset();
        m_queue = nullptr;        
    }

    void ackerman::used_eq_eh(euf::theory_var v1, euf::theory_var v2) {
        if (v1 == v2)
            return;
        if (v1 > v2)
            std::swap(v1, v2);
        vv* n = m_tmp_vv;
        n->set_var(v1, v2);
        vv* other = m_table.insert_if_not_there(n);        
        other->m_count++;
        update_glue(*other);

        vv::push_to_front(m_queue, other);
        if (other == n) {
            new_tmp();        
            gc();
        }
        if (other->m_glue == 0) {
            remove(other);
            add_cc(v1, v2);
        }
        else if (other->m_count > m_propagate_high_watermark) 
            s.s().set_should_simplify();
    }

    void ackerman::used_diseq_eh(euf::theory_var v1, euf::theory_var v2) {
        if (v1 == v2)
            return;
        if (v1 > v2)
            std::swap(v1, v2);
        vv* n = m_tmp_vv;
        n->set_var(v1, v2);
        vv* other = m_table.insert_if_not_there(n);
        other->m_count++;

        vv::push_to_front(m_queue, other);
        if (other == n) {
            new_tmp();
            gc();
        }
        if (other->m_count > m_propagate_high_watermark) 
            s.s().set_should_simplify();
    }

    void ackerman::update_glue(vv& v) {
        unsigned sz = s.m_bits[v.v1].size();
        m_diff_levels.reserve(s.s().scope_lvl() + 1, false);
        unsigned glue = 0;
        unsigned max_glue = v.m_glue;
        auto const& bitsa = s.m_bits[v.v1];
        auto const& bitsb = s.m_bits[v.v2];
        unsigned i = 0;
        for (; i < sz && i < max_glue; ++i) {
            sat::literal a = bitsa[i];
            sat::literal b = bitsb[i];
            if (a == b)
                continue;
            SASSERT(s.s().value(a) != l_undef);
            SASSERT(s.s().value(b) == s.s().value(a));
            unsigned lvl_a = s.s().lvl(a);
            unsigned lvl_b = s.s().lvl(b);
            if (!m_diff_levels[lvl_a]) {
                m_diff_levels[lvl_a] = true;
                ++glue;
            }
            if (!m_diff_levels[lvl_b]) {
                m_diff_levels[lvl_b] = true;
                ++glue;
            }            
        }
        for (; i-- > 0; ) {
            sat::literal a = bitsa[i];
            sat::literal b = bitsb[i];
            if (a != b) {
                m_diff_levels[s.s().lvl(a)] = false;
                m_diff_levels[s.s().lvl(b)] = false;
            }
        }
        
        if (glue < max_glue) 
            v.m_glue = (sz > 6 && 2*glue <= sz) ? 0 : glue;
    }

    void ackerman::remove(vv* p) {
        vv::remove_from(m_queue, p);
        m_table.erase(p);
        dealloc(p);
    }

    void ackerman::new_tmp() {
        m_tmp_vv = alloc(vv);
        m_tmp_vv->init(m_tmp_vv);
        m_tmp_vv->m_count = 0;
        m_tmp_vv->m_glue = UINT_MAX;
    }
        
    void ackerman::gc() {
        m_num_propagations_since_last_gc++;
        if (m_num_propagations_since_last_gc <= s.get_config().m_dack_gc) 
            return;
        m_num_propagations_since_last_gc = 0;
        
        while (m_table.size() > m_gc_threshold) 
            remove(m_queue->prev());     

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
            k = n->next();
            if (n->m_count < m_propagate_low_watermark && n->m_glue != 0)
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
        sort* s1 = s.var2expr(v1)->get_sort();
        sort* s2 = s.var2expr(v2)->get_sort();
        if (s1 != s2 || !s.bv.is_bv_sort(s1))
            return;
        // IF_VERBOSE(0, verbose_stream() << "assert ackerman " << v1 << " " << v2 << "\n");
        s.assert_ackerman(v1, v2);
    }

}

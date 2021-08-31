/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_ackerman.cpp

Abstract:

    Ackerman reduction plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-28

--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/euf_ackerman.h"

namespace euf {

    ackerman::ackerman(solver& s, ast_manager& m): s(s), m(m) {
        new_tmp();
    }

    ackerman::~ackerman() {
        reset();
        dealloc(m_tmp_inference);
    }

    void ackerman::reset() {
        for (inference* inf : m_table) {
            m.dec_ref(inf->a);
            m.dec_ref(inf->b);
            m.dec_ref(inf->c);
            dealloc(inf);
        }
        m_table.reset();
        m_queue = nullptr;        
    }

    void ackerman::insert(expr* a, expr* b, expr* lca) {
        if (a->get_id() > b->get_id())
            std::swap(a, b);
        inference& inf = *m_tmp_inference;
        inf.a = a;
        inf.b = b;
        inf.c = lca;
        inf.is_cc = false;
        inf.m_count = 0;
        insert();
    }

    void ackerman::insert(app* a, app* b) {
        if (a->get_id() > b->get_id())
            std::swap(a, b);
        inference& inf = *m_tmp_inference;
        inf.a = a;
        inf.b = b;
        inf.c = nullptr;
        inf.is_cc = true;
        inf.m_count = 0;
        insert();
    }


    void ackerman::insert() {
        inference* inf = m_tmp_inference;
        inference* other = m_table.insert_if_not_there(inf);
        if (other == inf) {
            m.inc_ref(inf->a);
            m.inc_ref(inf->b);
            m.inc_ref(inf->c);
            new_tmp();        
        }
        other->m_count++;
        if (other->m_count > m_high_watermark) {
            if (other->is_cc)
                add_cc(other->a, other->b);
            else
                add_eq(other->a, other->b, other->c);
            other->m_count = 0;
        }       
        inference::push_to_front(m_queue, other);
    }

    void ackerman::remove(inference* inf) {
        inference::remove_from(m_queue, inf);
        m_table.erase(inf);
        m.dec_ref(inf->a);
        m.dec_ref(inf->b);
        m.dec_ref(inf->c);
        dealloc(inf);
    }

    void ackerman::new_tmp() {
        m_tmp_inference = alloc(inference);
        m_tmp_inference->init(m_tmp_inference);
    }

    void ackerman::cg_conflict_eh(expr * n1, expr * n2) {
        if (!is_app(n1) || !is_app(n2))
            return;
        SASSERT(!s.m_drating);
        app* a = to_app(n1);
        app* b = to_app(n2);
        if (a->get_decl() != b->get_decl() || a->get_num_args() != b->get_num_args())
            return;
        TRACE("ack", tout << "conflict eh: " << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n";);
        insert(a, b);
        gc();
    }

    void ackerman::used_eq_eh(expr* a, expr* b, expr* c) {
        if (a == b || a == c || b == c)
            return;
        if (s.m_drating)
            return;
        TRACE("ack", tout << mk_pp(a, m) << " " << mk_pp(b, m) << " " << mk_pp(c, m) << "\n";);
        insert(a, b, c);
        gc();
    }
        
    void ackerman::used_cc_eh(app* a, app* b) {
        if (s.m_drating)
            return;
        TRACE("ack", tout << "used cc: " << mk_pp(a, m) << " == " << mk_pp(b, m) << "\n";);
        SASSERT(a->get_decl() == b->get_decl());
        SASSERT(a->get_num_args() == b->get_num_args());
        insert(a, b);
        gc();
    }

    void ackerman::gc() {
        m_num_propagations_since_last_gc++;
        if (m_num_propagations_since_last_gc <= s.m_config.m_dack_gc) 
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
        inference* k = nullptr;
        unsigned num_prop = static_cast<unsigned>(s.s().get_stats().m_conflict * s.m_config.m_dack_factor);
        num_prop = std::min(num_prop, m_table.size());
        for (unsigned i = 0; i < num_prop; ++i, n = k) {
            k = n->next();
            if (n->m_count < s.m_config.m_dack_threshold) 
                continue;
            if (n->m_count >= m_high_watermark && num_prop < m_table.size())
                ++num_prop;
            if (n->is_cc) 
                add_cc(n->a, n->b);
            else 
                add_eq(n->a, n->b, n->c);       
            ++s.m_stats.m_ackerman;
            remove(n);
        }
    }

    void ackerman::add_cc(expr* _a, expr* _b) {     
        flet<bool> _is_redundant(s.m_is_redundant, true);
        app* a = to_app(_a);
        app* b = to_app(_b);
        TRACE("ack", tout << mk_pp(a, m) << " " << mk_pp(b, m) << "\n";);
        sat::literal_vector lits;
        unsigned sz = a->get_num_args();
        
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref eq(m.mk_eq(a->get_arg(i), b->get_arg(i)), m);
            lits.push_back(~s.mk_literal(eq));
        }
        expr_ref eq(m.mk_eq(a, b), m);
        lits.push_back(s.mk_literal(eq));
        s.s().mk_clause(lits, sat::status::th(true, m.get_basic_family_id()));
    }

    void ackerman::add_eq(expr* a, expr* b, expr* c) {
        flet<bool> _is_redundant(s.m_is_redundant, true);
        sat::literal lits[3];
        expr_ref eq1(m.mk_eq(a, c), m);
        expr_ref eq2(m.mk_eq(b, c), m);
        expr_ref eq3(m.mk_eq(a, b), m);
        TRACE("ack", tout << mk_pp(a, m) << " " << mk_pp(b, m) << " " << mk_pp(c, m) << "\n";);
        lits[0] = ~s.mk_literal(eq1);
        lits[1] = ~s.mk_literal(eq2);
        lits[2] = s.mk_literal(eq3);
        s.s().mk_clause(3, lits, sat::status::th(true, m.get_basic_family_id()));
    }
}

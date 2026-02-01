/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    preferred_value_propagator.h

Abstract:

    Specialized propagator for preferred values

Author:

    Nikolaj Bjorner (nbjorner) 10-2-2025

Notes:

--*/
#pragma once

#include "tactic/user_propagator_base.h"
#include "util/trail.h"


class preferred_value_propagator {
    ast_manager &m;
    expr_ref_vector m_preferred;
    unsigned m_qhead = 0;
    trail_stack m_trail;

    bool decide(user_propagator::callback& cb) {
        if (m_qhead >= m_preferred.size())
            return false;
        m_trail.push(value_trail(m_qhead));
        while (m_qhead < m_preferred.size()) {
            expr *e = m_preferred.get(m_qhead);
            bool is_not = m.is_not(e, e);
            m_qhead++;
            if (cb.next_split_cb(e, 0, is_not ? l_false : l_true))
                return true;
        }
        return false;
    }

public:
    preferred_value_propagator(ast_manager &m) : m(m), m_preferred(m) {
         push_eh = [](void * ctx, user_propagator::callback* cb) {
            auto &p = *static_cast<preferred_value_propagator *>(ctx);
            p.m_trail.push_scope(); 
         };
        pop_eh = [](void * ctx, user_propagator::callback* cb, unsigned n) -> void {
            auto &p = *static_cast<preferred_value_propagator *>(ctx);
            p.m_trail.pop_scope(n);
        };
        fresh_eh = [](void* ctx, ast_manager& dst, user_propagator::context_obj*& co) -> void* {
            auto &p = *static_cast<preferred_value_propagator *>(ctx);
            ast_translation tr(p.m, dst);
            auto r = alloc(preferred_value_propagator, dst);
            for (auto e : p.m_preferred)
                r->set_preferred(tr(e));
            return r;
        };

        decide_eh = [](void * ctx, user_propagator::callback * cb, expr *, unsigned, bool) -> bool {
            auto &p = *static_cast<preferred_value_propagator *>(ctx);
            return p.decide(*cb);
        };
    }
    void set_preferred(expr *e) {
        m_preferred.push_back(e);
        if (m_trail.get_num_scopes() > 0)
            m_trail.push(push_back_vector(m_preferred));
    }
    void reset_preferred() {
        if (m_trail.get_num_scopes() != 0)
            throw default_exception("cannot reset preferred values in scoped context");
        m_preferred.reset();
        SASSERT(m_qhead == 0);
    }
    user_propagator::push_eh_t push_eh;
    user_propagator::pop_eh_t pop_eh;
    user_propagator::fresh_eh_t fresh_eh;
    user_propagator::decide_eh_t decide_eh;
};
/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    bv_internalize.cpp

Abstract:

    Internalize utilities for bit-vector solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30

--*/

#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/sat_th.h"
#include "tactic/tactic_exception.h"

namespace bv {

    euf::theory_var solver::mk_var(euf::enode* n) {
        theory_var r  = euf::th_euf_solver::mk_var(n);
        m_find.mk_var();
        m_bits.push_back(sat::literal_vector());
        m_wpos.push_back(0);
        m_zero_one_bits.push_back(zero_one_bits());        
        ctx.attach_th_var(n, this, r);
        return r;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) {
        flet<bool> _is_learned(m_is_redundant, learned);
        sat::scoped_stack _sc(m_stack);
        unsigned sz = m_stack.size();
        visit(e);
        while (m_stack.size() > sz) {
        loop:
            if (!m.inc())
                throw tactic_exception(m.limit().get_cancel_msg());
            sat::eframe & fr = m_stack.back();
            expr* e = fr.m_e;
            if (visited(e)) {
                m_stack.pop_back();
                continue;
            }
            unsigned num = is_app(e) ? to_app(e)->get_num_args() : 0;
            
            while (fr.m_idx < num) {
                expr* arg = to_app(e)->get_arg(fr.m_idx);
                fr.m_idx++;
                visit(arg);
                if (!visited(arg))
                    goto loop;
            }
            visit(e);
            SASSERT(visited(e));
            m_stack.pop_back();
        }        
        SASSERT(visited(e));
        return sat::null_literal;
    }

    bool solver::visit(expr* e) {
        return false;
    }

    bool solver::visited(expr* e) {
        return false;
    }

}

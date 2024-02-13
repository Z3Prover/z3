/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls.cpp

Abstract:

    A Stochastic Local Search (SLS) engine
    Uses invertibility conditions, 
    interval annotations
    don't care annotations

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/sls/bv_sls.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

namespace bv {

    sls::sls(ast_manager& m): 
        m(m), 
        bv(m),
        m_terms(m),
        m_eval(m)
    {}

    void sls::init() {
        m_terms.init(); 
    }

    void sls::init_eval(std::function<bool(expr*, unsigned)>& eval) {
        m_eval.init_eval(m_terms.assertions(), eval);
        for (auto* e : m_terms.assertions()) {
            if (!m_eval.bval0(e)) {
                m_eval.set(e, true);
                m_repair_down.insert(e->get_id());
            }
        }
        m_eval.init_fixed(m_terms.assertions());
    }

    lbool sls::operator()() {
        // init and init_eval were invoked.
        unsigned& n = m_stats.m_moves;
        n = 0;
        for (; n < m_config.m_max_repairs && m.inc(); ++n) {
            if (!m_repair_down.empty()) {
                unsigned index = m_rand(m_repair_down.size());
                unsigned expr_id = m_repair_down.elem_at(index);
                auto e = m_terms.term(expr_id);
                if (eval_is_correct(e))
                    m_repair_down.remove(expr_id);
                else
                    try_repair_down(e);
            }
            else if (!m_repair_up.empty()) {
                unsigned index = m_rand(m_repair_up.size());
                unsigned expr_id = m_repair_up.elem_at(index);
                auto e = m_terms.term(expr_id);
                if (eval_is_correct(e))
                    m_repair_up.remove(expr_id);
                else
                    try_repair_up(e);
            }
            else
                return l_true;
        }
        return l_undef;
    }

    bool sls::try_repair_down(app* e) {
        IF_VERBOSE(20, verbose_stream() << "d " << mk_bounded_pp(e, m, 1) << "\n");
        unsigned n = e->get_num_args();
        unsigned s = m_rand(n);
        for (unsigned i = 0; i < n; ++i) 
            if (try_repair_down(e, (i + s) % n))
                return true;                    
        return false;
    }

    bool sls::try_repair_down(app* e, unsigned i) {
        expr* child = e->get_arg(i);
        bool was_repaired = m_eval.try_repair(e, i);
        if (was_repaired) {
            m_repair_down.insert(child->get_id());
            for (auto p : m_terms.parents(child))
                m_repair_up.insert(p->get_id());            
        }
        return was_repaired;
    }

    bool sls::try_repair_up(app* e) {
        IF_VERBOSE(20, verbose_stream() << "u " << mk_bounded_pp(e, m, 1) << "\n");
        m_repair_up.remove(e->get_id());
        if (m_terms.is_assertion(e)) {
            m_repair_down.insert(e->get_id());
            return false;
        }
        m_eval.repair_up(e);
        for (auto p : m_terms.parents(e)) 
            m_repair_up.insert(p->get_id());     
        
        return true;
    }

    bool sls::eval_is_correct(app* e) {
        if (m.is_bool(e))
            return m_eval.bval0(e) == m_eval.bval1(e);
        if (bv.is_bv(e))
            return 0 == memcmp(m_eval.wval0(e).bits.data(), m_eval.wval1(e).data(), m_eval.wval0(e).nw * 8);
        UNREACHABLE();
        return false;
    }

    model_ref sls::get_model() {
        model_ref mdl = alloc(model, m);
        m_eval.sort_assertions(m_terms.assertions());
        for (expr* e : m_todo) {
            if (!is_uninterp_const(e))
                continue;
            auto f = to_app(e)->get_decl();
            if (m.is_bool(e))
                mdl->register_decl(f, m.mk_bool_val(m_eval.bval0(e)));
            else if (bv.is_bv(e)) {
                auto const& v = m_eval.wval0(e);
                rational n;
                v.get_value(v.bits, n);
                mdl->register_decl(f, bv.mk_numeral(n, v.bw));
            }
        }
        return mdl;
    }

    std::ostream& sls::display(std::ostream& out) { 
        auto& terms = m_eval.sort_assertions(m_terms.assertions());
        for (expr* e : terms) {
            out << e->get_id() << ": " << mk_bounded_pp(e, m, 1) << " ";
            if (m_eval.is_fixed0(e))
                out << "f ";
            if (m_repair_down.contains(e->get_id()))
                out << "d ";
            if (m_repair_up.contains(e->get_id()))
                out << "u ";
            if (bv.is_bv(e))
                out << m_eval.wval0(e);
            else if (m.is_bool(e))
                out << (m_eval.bval0(e)?"T":"F");
            out << "\n";
        }
        terms.reset();
        return out; 
    }
}

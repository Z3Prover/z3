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
#include "params/sls_params.hpp"

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
        m_eval.tighten_range(m_terms.assertions());
        init_repair();
    }

    void sls::init_repair() {
        m_repair_down = UINT_MAX;
        m_repair_up.reset();
        m_repair_roots.reset();
        for (auto* e : m_terms.assertions()) {
            if (!m_eval.bval0(e)) {
                m_eval.set(e, true);
                m_repair_roots.insert(e->get_id());
            }
        }
        for (auto* t : m_terms.terms()) {
            if (t && !re_eval_is_correct(t)) 
                m_repair_roots.insert(t->get_id());            
        }
    }

    void sls::init_repair_goal(app* t) {
        if (m.is_bool(t)) 
            m_eval.set(t, m_eval.bval1(t));        
        else if (bv.is_bv(t)) {
            auto& v = m_eval.wval(t);
            v.bits().copy_to(v.nw, v.eval);
        }
    }

    void sls::reinit_eval() {
        std::function<bool(expr*, unsigned)> eval = [&](expr* e, unsigned i) {
            auto should_keep = [&]() {
                return m_rand() % 100 <= 92;
            };
            if (m.is_bool(e)) {
                if (m_eval.is_fixed0(e) || should_keep())
                    return m_eval.bval0(e);
            }
            else if (bv.is_bv(e)) {
                auto& w = m_eval.wval(e);
                if (w.fixed.get(i) || should_keep())
                    return w.get_bit(i);                
            }
            return m_rand() % 2 == 0;
        };
        m_eval.init_eval(m_terms.assertions(), eval);
        init_repair();
    }

    std::pair<bool, app*> sls::next_to_repair() {
        app* e = nullptr;
        if (m_repair_down != UINT_MAX) {
            e = m_terms.term(m_repair_down);
            m_repair_down = UINT_MAX;
            return { true, e };
        }

        if (!m_repair_up.empty()) {
            unsigned index = m_repair_up.elem_at(m_rand(m_repair_up.size()));
            m_repair_up.remove(index);
            e = m_terms.term(index);
            return { false, e };
        }

        while (!m_repair_roots.empty()) {
            unsigned index = m_repair_roots.elem_at(m_rand(m_repair_roots.size()));
            e = m_terms.term(index);
            if (m_terms.is_assertion(e) && !m_eval.bval1(e)) {
                SASSERT(m_eval.bval0(e));
                return { true, e };
            }
            if (!re_eval_is_correct(e)) {
                init_repair_goal(e);
                return { true, e };
            }
            m_repair_roots.remove(index);
        }

        return { false, nullptr };
    }

    lbool sls::search() {
        // init and init_eval were invoked
        unsigned n = 0;
        for (; n++ < m_config.m_max_repairs && m.inc(); ) {
            auto [down, e] = next_to_repair();
            if (!e)
                return l_true;


            trace_repair(down, e);

            ++m_stats.m_moves;

            if (down) 
                try_repair_down(e);
            else
                try_repair_up(e);            
        }
        return l_undef;
    }


    lbool sls::operator()() {
        lbool res = l_undef;
        m_stats.reset();
        m_stats.m_restarts = 0;
        do {
            res = search();
            if (res != l_undef)
                break;
            trace();
            reinit_eval();
        } 
        while (m.inc() && m_stats.m_restarts++ < m_config.m_max_restarts);

        return res;
    }

    void sls::try_repair_down(app* e) {

        unsigned n = e->get_num_args();
        if (n == 0) {
            if (m.is_bool(e)) 
                m_eval.set(e, m_eval.bval1(e));                            
            else 
                VERIFY(m_eval.wval(e).commit_eval());
            
            for (auto p : m_terms.parents(e))
                m_repair_up.insert(p->get_id());
            return;
        }        

        unsigned s = m_rand(n);
        for (unsigned i = 0; i < n; ++i) {
            auto j = (i + s) % n;
            if (m_eval.try_repair(e, j)) {
                set_repair_down(e->get_arg(j));
                return;
            }
        }
        // search a new root / random walk to repair        
    }

    void sls::try_repair_up(app* e) {       
        
        if (m_terms.is_assertion(e) || !m_eval.repair_up(e)) 
            m_repair_roots.insert(e->get_id());        
        else {
            if (!eval_is_correct(e)) {
                verbose_stream() << "incorrect eval #" << e->get_id() << " " << mk_bounded_pp(e, m) << "\n";
            }
            SASSERT(eval_is_correct(e));
            for (auto p : m_terms.parents(e))
                m_repair_up.insert(p->get_id());
        }
    }

    bool sls::eval_is_correct(app* e) {
        if (!m_eval.can_eval1(e))
            return false;
        if (m.is_bool(e))
            return m_eval.bval0(e) == m_eval.bval1(e);
        if (bv.is_bv(e)) {
            auto const& v = m_eval.wval(e);
            return v.eval == v.bits();
        }
        UNREACHABLE();
        return false;
    }


    bool sls::re_eval_is_correct(app* e) {
        if (!m_eval.can_eval1(e))
            return false;
        if (m.is_bool(e))
            return m_eval.bval0(e) == m_eval.bval1(e);
        if (bv.is_bv(e)) {
            auto const& v = m_eval.eval(e);
            return v.eval == v.bits();
        }
        UNREACHABLE();
        return false;
    }

    model_ref sls::get_model() {
        model_ref mdl = alloc(model, m);
        auto& terms = m_eval.sort_assertions(m_terms.assertions());
        for (expr* e : terms) {
            if (!re_eval_is_correct(to_app(e))) {
                verbose_stream() << "missed evaluation #" << e->get_id() << " " << mk_bounded_pp(e, m) << "\n";
                if (bv.is_bv(e)) {
                    auto const& v = m_eval.wval(e);
                    verbose_stream() << v << "\n" << v.eval << "\n";
                }
            }
            if (!is_uninterp_const(e))
                continue;

            auto f = to_app(e)->get_decl();
            if (m.is_bool(e))
                mdl->register_decl(f, m.mk_bool_val(m_eval.bval0(e)));
            else if (bv.is_bv(e)) {
                auto const& v = m_eval.wval(e);
                rational n = v.get_value();
                mdl->register_decl(f, bv.mk_numeral(n, v.bw));
            }
        }
        terms.reset();
        return mdl;
    }

    std::ostream& sls::display(std::ostream& out) { 
        auto& terms = m_eval.sort_assertions(m_terms.assertions());
        for (expr* e : terms) {
            out << e->get_id() << ": " << mk_bounded_pp(e, m, 1) << " ";
            if (m_eval.is_fixed0(e))
                out << "f ";
            if (m_repair_up.contains(e->get_id()))
                out << "u ";
            if (m_repair_roots.contains(e->get_id()))
                out << "r ";
            if (bv.is_bv(e))
                out << m_eval.wval(e);
            else if (m.is_bool(e))
                out << (m_eval.bval0(e)?"T":"F");
            out << "\n";
        }
        terms.reset();
        return out; 
    }

    void sls::updt_params(params_ref const& _p) {
        sls_params p(_p);
        m_config.m_max_restarts = p.max_restarts();
        m_rand.set_seed(p.random_seed());
    }

    void sls::trace_repair(bool down, expr* e) {
        IF_VERBOSE(20,
            verbose_stream() << (down ? "d #" : "u #")
            << e->get_id() << ": "
            << mk_bounded_pp(e, m, 1) << " ";
        if (bv.is_bv(e)) verbose_stream() << m_eval.wval(e) << " " << (m_eval.is_fixed0(e) ? "fixed " : " ");
        if (m.is_bool(e)) verbose_stream() << m_eval.bval0(e) << " ";
        verbose_stream() << "\n");
    }

    void sls::trace() {
        IF_VERBOSE(2, verbose_stream()
            << "(bvsls :restarts " << m_stats.m_restarts
            << " :repair-up " << m_repair_up.size()
            << " :repair-roots " << m_repair_roots.size() << ")\n");
    }
}

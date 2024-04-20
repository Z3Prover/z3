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

    sls::sls(ast_manager& m, params_ref const& p): 
        m(m), 
        bv(m),
        m_terms(m),
        m_eval(m),
        m_engine(m, p)
    {
        updt_params(p);
    }

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
            if (t && !m_eval.re_eval_is_correct(t)) 
                m_repair_roots.insert(t->get_id());            
        }
    }


    void sls::set_model() {
        if (!m_set_model)
            return;
        if (m_repair_roots.size() >= m_min_repair_size)
            return;
        m_min_repair_size = m_repair_roots.size();
        IF_VERBOSE(2, verbose_stream() << "(sls-update-model :num-unsat " << m_min_repair_size << ")\n");
        m_set_model(*get_model());
    }

    void sls::init_repair_goal(app* t) {
        m_eval.init_eval(t);
    }

    void sls::init_repair_candidates() {
        m_to_repair.reset();
        ptr_vector<expr> todo;
        expr_fast_mark1 mark;
        for (auto index : m_repair_roots) 
            todo.push_back(m_terms.term(index));
        for (unsigned i = 0; i < todo.size(); ++i) {
            expr* e = todo[i];
            if (mark.is_marked(e))
                continue;
            mark.mark(e);
            if (!is_app(e))
                continue;
            for (expr* arg : *to_app(e))
                todo.push_back(arg);

            if (is_uninterp_const(e))
                m_to_repair.insert(e->get_id());

        }
    }


    void sls::reinit_eval() {
        init_repair_candidates();

        if (m_to_repair.empty())
            return;

        // refresh the best model so far to a callback
        set_model();

        // add fresh units, if any
        bool new_assertion = false;
        while (m_get_unit) {
            auto e = m_get_unit();
            if (!e)
                break;
            new_assertion = true;
            assert_expr(e);
        }
        if (new_assertion) 
            init();        
           
        std::function<bool(expr*, unsigned)> eval = [&](expr* e, unsigned i) {
            unsigned id = e->get_id();
            bool keep = !m_to_repair.contains(id);
            if (m.is_bool(e)) {
                if (m_eval.is_fixed0(e) || keep)
                    return m_eval.bval0(e);
                if (m_engine_init) {
                    auto const& z = m_engine.get_value(e);
                    return rational(z).get_bit(0);
                }
            }
            else if (bv.is_bv(e)) {
                auto& w = m_eval.wval(e);
                if (w.fixed.get(i) || keep)
                    return w.get_bit(i);
                if (m_engine_init) {
                    auto const& z = m_engine.get_value(e);
                    return rational(z).get_bit(i);
                }
            }
            
            return m_rand() % 2 == 0;
        };
        m_eval.init_eval(m_terms.assertions(), eval);
        init_repair();
        // m_engine_init = false;
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
            if (!m_eval.re_eval_is_correct(e)) {
                init_repair_goal(e);
                return { true, e };
            }
            m_repair_roots.remove(index);
        }

        return { false, nullptr };
    }

    lbool sls::search1() {
        // init and init_eval were invoked
        unsigned n = 0;
        for (; n < m_config.m_max_repairs && m.inc(); ++n) {
            auto [down, e] = next_to_repair();
            if (!e)
                return l_true;

            IF_VERBOSE(20, trace_repair(down, e));
            
            ++m_stats.m_moves;
            if (down) 
                try_repair_down(e);            
            else
                try_repair_up(e);            
        }
        return l_undef;
    }

    lbool sls::search2() {
        lbool res = l_undef;
        if (m_stats.m_restarts == 0)
            res = m_engine(),
            m_engine_init = true;
        else if (m_stats.m_restarts % 1000 == 0)
            res = m_engine.search_loop(),
            m_engine_init = true;
        if (res != l_undef) 
            m_engine_model = true;   
        return res;
    }


    lbool sls::operator()() {
        lbool res = l_undef;
        m_stats.reset();
        m_stats.m_restarts = 0;
        m_engine_model = false;
        m_engine_init = false;

        do {
            res = search1();
            if (res != l_undef)
                break;
            trace();
            //res = search2();
            if (res != l_undef)
                break;
            reinit_eval();
        } 
        while (m.inc() && m_stats.m_restarts++ < m_config.m_max_restarts);

        return res;
    }

    void sls::try_repair_down(app* e) {
        unsigned n = e->get_num_args();
        if (n == 0) {
            m_eval.commit_eval(e);           
            for (auto p : m_terms.parents(e))
                m_repair_up.insert(p->get_id());
            
            return;
        }        

        if (n == 2) {
            auto d1 = get_depth(e->get_arg(0));
            auto d2 = get_depth(e->get_arg(1));
            unsigned s = m_rand(d1 + d2 + 2);
            if (s <= d1 && m_eval.try_repair(e, 0)) {
                set_repair_down(e->get_arg(0));
                return;
            }
            if (m_eval.try_repair(e, 1)) {
                set_repair_down(e->get_arg(1));
                return;
            }
            if (m_eval.try_repair(e, 0)) {
                set_repair_down(e->get_arg(0));
                return;
            }
        }
        else {
            unsigned s = m_rand(n);
            for (unsigned i = 0; i < n; ++i) {
                auto j = (i + s) % n;
                if (m_eval.try_repair(e, j)) {
                    set_repair_down(e->get_arg(j));
                    return;
                }
            }
        }
        IF_VERBOSE(3, verbose_stream() << "init-repair " << mk_bounded_pp(e, m) << "\n");
        // repair was not successful, so reset the state to find a different way to repair
        init_repair();
    }

    void sls::try_repair_up(app* e) {       
        
        if (m_terms.is_assertion(e)) 
            m_repair_roots.insert(e->get_id());    
        else if (!m_eval.repair_up(e)) {
            IF_VERBOSE(2, verbose_stream() << "repair-up "; trace_repair(true, e));
            if (m_rand(10) != 0) {
                m_eval.set_random(e);                
                m_repair_roots.insert(e->get_id());
            }
            else
                init_repair();
        }
        else {
            if (!m_eval.eval_is_correct(e)) {
                verbose_stream() << "incorrect eval #" << e->get_id() << " " << mk_bounded_pp(e, m) << "\n";
            }
            SASSERT(m_eval.eval_is_correct(e));
            for (auto p : m_terms.parents(e))
                m_repair_up.insert(p->get_id());
        }
    }


    model_ref sls::get_model() {
        if (m_engine_model)
            return m_engine.get_model();

        model_ref mdl = alloc(model, m);         
        auto& terms = m_eval.sort_assertions(m_terms.assertions());
        for (expr* e : terms) {
            if (!is_uninterp_const(e))
                continue;
            auto f = to_app(e)->get_decl();
            auto v = m_eval.get_value(to_app(e));
            if (v)
                mdl->register_decl(f, v);
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
            m_eval.display_value(out, e);
            out << "\n";
        }
        terms.reset();
        return out; 
    }

    void sls::updt_params(params_ref const& _p) {
        sls_params p(_p);
        m_config.m_max_restarts = p.max_restarts();
        m_config.m_max_repairs = p.max_repairs();
        m_rand.set_seed(p.random_seed());
        m_terms.updt_params(_p);
        params_ref q = _p;
        q.set_uint("max_restarts", 10);
        m_engine.updt_params(q);
    }

    std::ostream& sls::trace_repair(bool down, expr* e) {
        verbose_stream() << (down ? "d #" : "u #")
            << e->get_id() << ": "
            << mk_bounded_pp(e, m, 1) << " ";
        m_eval.display_value(verbose_stream(), e) << "\n";
        return verbose_stream();
    }

    void sls::trace() {
        IF_VERBOSE(2, verbose_stream()
            << "(bvsls :restarts " << m_stats.m_restarts
            << " :repair-up " << m_repair_up.size()
            << " :repair-roots " << m_repair_roots.size() << ")\n");
    }
}

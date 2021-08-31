/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    opt_lns.cpp

Abstract:
   
    "large" neighborhood search for maxsat problem instances.

Author:

    Nikolaj Bjorner (nbjorner) 2021-02-01

--*/

#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/pb_decl_plugin.h"
#include "opt/maxsmt.h"
#include "opt/opt_lns.h"
#include "sat/sat_params.hpp"
#include <algorithm>

namespace opt {

    lns::lns(solver& s, lns_context& ctx)
        : m(s.get_manager()),
          s(s),
          ctx(ctx),
          m_hardened(m),
          m_unprocessed(m)
    {}

    void lns::set_lns_params() {
        params_ref p;
        p.set_sym("phase", symbol("frozen"));
        p.set_uint("restart.initial", 1000000);
        p.set_uint("max_conflicts", m_max_conflicts);    
        p.set_uint("simplify.delay", 1000000);
  //      p.set_bool("gc.burst", true);
        s.updt_params(p);
    }

    void lns::save_defaults(params_ref& p) {
        sat_params sp(p);
        p.set_sym("phase", sp.phase());
        p.set_uint("restart.initial", sp.restart_initial());
        p.set_uint("max_conflicts", sp.max_conflicts());
        p.set_uint("simplify.delay", sp.simplify_delay());
        p.set_uint("gc.burst", sp.gc_burst());
    }

    unsigned lns::climb(model_ref& mdl) {
        IF_VERBOSE(1, verbose_stream() << "(opt.lns :climb)\n");
        m_num_improves = 0;
        params_ref old_p(s.get_params());
        save_defaults(old_p);
        set_lns_params();
        update_best_model(mdl);
        for (unsigned i = 0; i < 2; ++i)
            improve_bs();
        IF_VERBOSE(1, verbose_stream() << "(opt.lns :relax-cores " << m_cores.size() << ")\n");
        relax_cores();
        s.updt_params(old_p);
        IF_VERBOSE(1, verbose_stream() << "(opt.lns :num-improves " << m_num_improves << ")\n");
        return m_num_improves;
    }

    void lns::update_best_model(model_ref& mdl) {
        rational cost = ctx.cost(*mdl);
        if (m_best_cost.is_zero() || m_best_cost >= cost) {
            m_best_cost = cost;
            m_best_model = mdl;
            m_best_phase = s.get_phase();
            m_best_bound = 0;
            for (expr* e : ctx.soft()) 
                if (!mdl->is_true(e))
                    m_best_bound += 1;
        }
    }

    void lns::apply_best_model() {
        s.set_phase(m_best_phase.get());
        for (expr* e : m_unprocessed) {
            s.move_to_front(e);
            s.set_phase(e);
        }
    }

    void lns::improve_bs() {
        m_unprocessed.reset();
        m_unprocessed.append(ctx.soft());

        m_hardened.reset();
        for (expr* a : ctx.soft())
            m_is_assumption.mark(a);
        shuffle(m_unprocessed.size(), m_unprocessed.data(), m_rand);
        
        model_ref mdl = m_best_model->copy();
        unsigned j = 0;
        for (unsigned i = 0; i < m_unprocessed.size(); ++i) {
            if (mdl->is_false(unprocessed(i))) {
                expr_ref tmp(m_unprocessed.get(j), m);
                m_unprocessed[j++] = m_unprocessed.get(i);
                m_unprocessed[i] = tmp;
                break;
            }
        }
        for (unsigned i = j; i < m_unprocessed.size(); ++i) {
            if (mdl->is_true(unprocessed(i))) {
                expr_ref tmp(m_unprocessed.get(j), m);
                m_unprocessed[j++] = m_unprocessed.get(i);
                m_unprocessed[i] = tmp;
            }
        }
        for (unsigned i = 0; i < 3 && !m_unprocessed.empty(); ++i)
            improve_bs1();
    }

    void lns::improve_bs1() {
        model_ref mdl = m_best_model->copy();
        unsigned j = 0;
        for (expr* e : m_unprocessed) {
            if (!m.inc())
                return;
            if (mdl->is_true(e))
                m_hardened.push_back(e);
            else {
                apply_best_model();
                switch (improve_step(mdl, e)) {
                case l_true:
                    m_hardened.push_back(e);
                    ctx.update_model(mdl);
                    update_best_model(mdl);
                    break;
                case l_false:
                    m_hardened.push_back(m.mk_not(e));
                    break;
                case l_undef:
                    m_unprocessed[j++] = e;
                    break;
                }
            }
        }
        m_unprocessed.shrink(j);
    }

    struct lns::scoped_bounding {
        lns& m_lns;
        bool m_cores_are_valid { true };

        scoped_bounding(lns& l):m_lns(l) {
            if (!m_lns.m_enable_scoped_bounding) 
                return;
            if (m_lns.m_best_bound == 0)
                return;
            m_cores_are_valid = m_lns.m_cores_are_valid;
            m_lns.m_cores_are_valid = false;
            m_lns.s.push();
            pb_util pb(m_lns.m);
            expr_ref bound(pb.mk_at_most_k(m_lns.ctx.soft(), m_lns.m_best_bound - 1), m_lns.m);
            m_lns.s.assert_expr(bound);
        }
        ~scoped_bounding() {
            if (!m_lns.m_enable_scoped_bounding)
                return;
            m_lns.m_cores_are_valid = m_cores_are_valid;
            m_lns.s.pop(1);
        }
    };

    void lns::relax_cores() {
        if (!m_cores.empty() && m_cores_are_valid) {
            std::sort(m_cores.begin(), m_cores.end(), [&](expr_ref_vector const& a, expr_ref_vector const& b) { return a.size() < b.size(); });
            unsigned num_disjoint = 0;
            vector<expr_ref_vector> new_cores;
            for (auto const& c : m_cores) {
                bool in_core = false;
                for (auto* e : c)
                    in_core |= m_in_core.is_marked(e);
                if (in_core)
                    continue;
                for (auto* e : c)
                    m_in_core.mark(e);
                new_cores.push_back(c);
                ++num_disjoint;
            }
            IF_VERBOSE(2, verbose_stream() << "num cores: " << m_cores.size() << " new cores: " << new_cores.size() << "\n");
            ctx.relax_cores(new_cores);
        }
        m_in_core.reset();
        m_is_assumption.reset();
        m_cores.reset();
    }

    unsigned lns::improve_linear(model_ref& mdl) {
        scoped_bounding _scoped_bouding(*this);
        unsigned num_improved = 0;
        unsigned max_conflicts = m_max_conflicts;
        while (m.inc()) {
            unsigned reward = improve_step(mdl);
            if (reward == 0)
                break;
            num_improved += reward;
            m_max_conflicts *= 3;
            m_max_conflicts /= 2;
            set_lns_params();
        }
        m_max_conflicts = max_conflicts;
        return num_improved;
    }

    unsigned lns::improve_step(model_ref& mdl) {
        unsigned num_improved = 0;
        for (unsigned i = 0; m.inc() && i < m_unprocessed.size(); ++i) {
            switch (improve_step(mdl, unprocessed(i))) {
            case l_undef:
                break;
            case l_false:
                TRACE("opt", tout << "pruned " << mk_bounded_pp(unprocessed(i), m) << "\n";);
                m_hardened.push_back(m.mk_not(unprocessed(i)));
                for (unsigned k = i; k + 1 < m_unprocessed.size(); ++k) 
                    m_unprocessed[k] = unprocessed(k + 1);
                m_unprocessed.pop_back();
                --i;
                break;
            case l_true: {
                unsigned k = 0, offset = 0;
                for (unsigned j = 0; j < m_unprocessed.size(); ++j) {
                    if (mdl->is_true(unprocessed(j))) {
                        if (j <= i)
                            ++offset;
                        ++m_num_improves;                        
                        TRACE("opt", tout << "improved " << mk_bounded_pp(unprocessed(j), m) << "\n";);
                        m_hardened.push_back(unprocessed(j));
                        ++num_improved;
                    }
                    else {
                        m_unprocessed[k++] = unprocessed(j);
                    }
                }
                m_unprocessed.shrink(k);
                i -= offset;
                IF_VERBOSE(1, verbose_stream() << "(opt.lns :num-improves " << m_num_improves << " :remaining-soft " << m_unprocessed.size() << ")\n");
                ctx.update_model(mdl);
                break;
            }       
            }
        }
        return num_improved;
    }

    lbool lns::improve_step(model_ref& mdl, expr* e) {
        m_hardened.push_back(e);
        lbool r = s.check_sat(m_hardened);
        m_hardened.pop_back();
        if (r == l_true) 
            s.get_model(mdl);
        if (r == l_false) {
            expr_ref_vector core(m);
            s.get_unsat_core(core);
            bool all_assumed = true;            
            for (expr* c : core) 
                all_assumed &= m_is_assumption.is_marked(c);
            IF_VERBOSE(2, verbose_stream() << "core " << all_assumed << " - " << core.size() << "\n");
            if (all_assumed) 
                m_cores.push_back(core);            
        }
        return r;
    } 

};

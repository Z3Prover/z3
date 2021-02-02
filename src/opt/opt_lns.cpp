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

    lns::lns(solver& s, std::function<void(model_ref& mdl)>& update_model)
        : m(s.get_manager()),
          s(s),
          m_hardened(m),
          m_soft(m),
          m_update_model(update_model)
    {}

    void lns::set_lns_params() {
        params_ref p;
        p.set_sym("phase", symbol("frozen"));
        p.set_uint("restart.initial", 1000000);
        p.set_uint("max_conflicts", m_max_conflicts);    
        p.set_uint("simplify.delay", 1000000);
//       p.set_bool("gc.burst", true);
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

    unsigned lns::climb(model_ref& mdl, expr_ref_vector const& asms) {
        m_num_improves = 0;
        params_ref old_p(s.get_params());
        save_defaults(old_p);
        set_lns_params();
        setup_assumptions(mdl, asms);
        unsigned num_improved = improve_linear(mdl);
        // num_improved += improve_rotate(mdl, asms);
        s.updt_params(old_p);
        IF_VERBOSE(1, verbose_stream() << "(opt.lns :num-improves " << m_num_improves << " :remaining-soft " << m_soft.size() << ")\n");
        return num_improved;
    }

    struct lns::scoped_bounding {
        lns& m_lns;
        bool m_cores_are_valid { true };

        scoped_bounding(lns& l):m_lns(l) {
            if (!m_lns.m_enable_scoped_bounding) 
                return;
            m_cores_are_valid = m_lns.m_cores_are_valid;
            m_lns.m_cores_are_valid = false;
            m_lns.s.push();
            pb_util pb(m_lns.m);
            // TBD: bound should to be adjusted for current best solution, not number of soft constraints left.
            expr_ref bound(pb.mk_at_most_k(m_lns.m_soft, m_lns.m_soft.size() - 1), m_lns.m);
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
        if (!m_cores.empty() && m_relax_cores && m_cores_are_valid) {
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
            m_relax_cores(new_cores);
        }
        m_in_core.reset();
        m_is_assumption.reset();
        m_cores.reset();
    }

    void lns::setup_assumptions(model_ref& mdl, expr_ref_vector const& asms) {
        m_hardened.reset();
        m_soft.reset();
        for (expr* a : asms) {
            m_is_assumption.mark(a);
            if (mdl->is_true(a))
                m_hardened.push_back(a);
            else
                m_soft.push_back(a);
        }
    }

    unsigned lns::improve_rotate(model_ref& mdl, expr_ref_vector const& asms) {
        unsigned num_improved = 0;
    repeat:
        setup_assumptions(mdl, asms);
        unsigned sz = m_hardened.size();
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref tmp(m_hardened.get(i), m);
            m_hardened[i] = m.mk_not(tmp);
            unsigned reward = improve_linear(mdl);
            if (reward > 1) {
                num_improved += (reward - 1);
                goto repeat;
            }
            setup_assumptions(mdl, asms);
        }
        return num_improved;
    }

    unsigned lns::improve_linear(model_ref& mdl) {
        scoped_bounding _scoped_bouding(*this);
        unsigned num_improved = 0;
        unsigned max_conflicts = m_max_conflicts;
        while (m.inc()) {
            unsigned hard = m_hardened.size();
            unsigned reward = improve_step(mdl);
            if (reward == 0)
                break;
            num_improved += reward;
            m_max_conflicts *= 3;
            m_max_conflicts /= 2;
            set_lns_params();
        }
        m_max_conflicts = max_conflicts;
        relax_cores();
        return num_improved;
    }

    unsigned lns::improve_step(model_ref& mdl) {
        unsigned num_improved = 0;
        for (unsigned i = 0; m.inc() && i < m_soft.size(); ++i) {
            switch (improve_step(mdl, soft(i))) {
            case l_undef:
                break;
            case l_false:
                TRACE("opt", tout << "pruned " << mk_bounded_pp(soft(i), m) << "\n";);
                m_hardened.push_back(m.mk_not(soft(i)));
                for (unsigned k = i; k + 1 < m_soft.size(); ++k) 
                    m_soft[k] = soft(k + 1);
                m_soft.pop_back();
                --i;
                break;
            case l_true: {
                unsigned k = 0, offset = 0;
                for (unsigned j = 0; j < m_soft.size(); ++j) {
                    if (mdl->is_true(soft(j))) {
                        if (j <= i)
                            ++offset;
                        ++m_num_improves;                        
                        TRACE("opt", tout << "improved " << mk_bounded_pp(soft(j), m) << "\n";);
                        m_hardened.push_back(soft(j));
                        ++num_improved;
                    }
                    else {
                        m_soft[k++] = soft(j);
                    }
                }
                m_soft.shrink(k);
                i -= offset;
                IF_VERBOSE(1, verbose_stream() << "(opt.lns :num-improves " << m_num_improves << " :remaining-soft " << m_soft.size() << ")\n");
                m_update_model(mdl);
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
            if (all_assumed) {
                m_cores.push_back(core);
            }
        }
        return r;
    } 

};

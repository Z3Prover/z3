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
        s.updt_params(p);
    }

    void lns::save_defaults(params_ref& p) {
        sat_params sp(p);
        p.set_sym("phase", sp.phase());
        p.set_uint("restart.initial", sp.restart_initial());
        p.set_uint("max_conflicts", sp.max_conflicts());
        p.set_uint("simplify.delay", sp.simplify_delay());
    }

    unsigned lns::climb(model_ref& mdl, expr_ref_vector const& asms) {
        m_num_improves = 0;
        params_ref old_p(s.get_params());
        save_defaults(old_p);
        set_lns_params();
        setup_assumptions(mdl, asms);
        unsigned num_improved = improve_linear(mdl);
//      num_improved += improve_rotate(mdl, asms);
        s.updt_params(old_p);
        IF_VERBOSE(1, verbose_stream() << "(opt.lns :num-improves " << m_num_improves << " :remaining-soft " << m_soft.size() << ")\n");
        return num_improved;
    }

    void lns::setup_assumptions(model_ref& mdl, expr_ref_vector const& asms) {
        m_hardened.reset();
        m_soft.reset();
        std::cout << "disjoint cores: " << m_cores.size() << "\n";
        for (auto const& c : m_cores)
            std::cout << c.size() << "\n";
        m_was_flipped.reset();
        m_in_core.reset();
        m_cores.reset();
        for (expr* a : asms) {
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
        for (unsigned i = 0; m.inc() && i < m_soft.size(); ++i) {
            switch (improve_step(mdl, soft(i))) {
            case l_undef:
                break;
            case l_false:
                TRACE("opt", tout << "pruned " << mk_bounded_pp(soft(i), m) << "\n";);
                m_hardened.push_back(m.mk_not(soft(i)));
                for (unsigned k = i; k + 1 < m_soft.size(); ++k) 
                    m_soft[k] = soft(k + 1);
                m_was_flipped.mark(m_hardened.back());
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
#if 0
        if (r == l_false) {
            expr_ref_vector core(m);
            s.get_unsat_core(core);
            bool was_flipped = false;
            for (expr* c : core) 
                was_flipped |= m_was_flipped.is_marked(c);
            if (!was_flipped) {
                for (expr* c : core) 
                    m_in_core.mark(c, true);
                m_cores.push_back(core);
            }
        }
#endif
        return r;
    } 

};

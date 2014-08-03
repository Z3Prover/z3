/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsmt.cpp

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/

#include <typeinfo>
#include "maxsmt.h"
#include "fu_malik.h"
#include "core_maxsat.h"
#include "maxres.h"
#include "maxhs.h"
#include "bcd2.h"
#include "wpm2.h"
#include "pbmax.h"
#include "wmax.h"
#include "maxsls.h"
#include "ast_pp.h"
#include "opt_params.hpp"
#include "pb_decl_plugin.h"
#include "pb_sls.h"
#include "tactical.h"
#include "tactic.h"
#include "tactic2solver.h"
#include "qfbv_tactic.h"
#include "card2bv_tactic.h"
#include "uint_set.h"
#include "opt_sls_solver.h"
#include "pb_preprocess_tactic.h"
#include "inc_sat_solver.h"


namespace opt {

    void maxsmt_solver_base::updt_params(params_ref& p) {
        m_params.copy(p);
        s().updt_params(p);
        opt_params _p(p);
        m_enable_sat = _p.enable_sat();
        m_enable_sls = _p.enable_sls();
    }       

    void maxsmt_solver_base::init_soft(vector<rational> const& weights, expr_ref_vector const& soft) {
        m_weights.reset();
        m_soft.reset();
        m_weights.append(weights);
        m_soft.append(soft);
    }

    void maxsmt_solver_base::init() {
        m_lower.reset();
        m_upper.reset();
        m_assignment.reset();
        for (unsigned i = 0; i < m_weights.size(); ++i) {
            expr_ref val(m);
            VERIFY(m_model->eval(m_soft[i].get(), val));                
            m_assignment.push_back(m.is_true(val));
            if (!m_assignment.back()) {
                m_upper += m_weights[i];
            }
        }
        
        TRACE("opt", 
              tout << m_upper << ": ";
              for (unsigned i = 0; i < m_weights.size(); ++i) {
                  tout << (m_assignment[i]?"1":"0");
              }
              tout << "\n";);
    }

    expr* maxsmt_solver_base::mk_not(expr* e) {
        if (m.is_not(e, e)) {
            return e;
        }
        else {
            return m.mk_not(e);
        }
    }

    struct maxsmt_solver_base::is_bv {
        struct found {};
        ast_manager& m;
        pb_util      pb;
        bv_util      bv;
        is_bv(ast_manager& m): m(m), pb(m), bv(m) {}
        void operator()(var *) { throw found(); }
        void operator()(quantifier *) { throw found(); }
        void operator()(app *n) {
            family_id fid = n->get_family_id();
            if (fid != m.get_basic_family_id() &&
                fid != pb.get_family_id() &&
                fid != bv.get_family_id() &&
                !is_uninterp_const(n)) {
                throw found();
            }
        }        
    };

    bool maxsmt_solver_base::probe_bv() {
        expr_fast_mark1 visited;
        is_bv proc(m);
        try {
            unsigned sz = s().get_num_assertions();
            for (unsigned i = 0; i < sz; i++) {
                quick_for_each_expr(proc, visited, s().get_assertion(i));
            }
            sz = m_soft.size();
            for (unsigned i = 0; i < sz; ++i) {
                quick_for_each_expr(proc, visited, m_soft[i].get());
            }
        }
        catch (is_bv::found) {
            return false;
        }
        return true;
    }

    void maxsmt_solver_base::enable_inc_bvsat() {
        m_params.set_bool("minimize_core", true);
        solver* sat_solver = mk_inc_sat_solver(m, m_params);
        unsigned sz = s().get_num_assertions();
        for (unsigned i = 0; i < sz; ++i) {
            sat_solver->assert_expr(s().get_assertion(i));
        }   
        m_s = sat_solver;
    }



    void maxsmt_solver_base::enable_bvsat()  {
        if (m_enable_sat && !m_sat_enabled && probe_bv()) {
            enable_inc_bvsat();
            m_sat_enabled = true;
        }
    }

    void maxsmt_solver_base::enable_sls() {
        if (m_enable_sls && !m_sls_enabled && probe_bv()) {
            m_params.set_uint("restarts", 20);
            unsigned lvl = m_s->get_scope_level();
            sls_solver* sls = alloc(sls_solver, m, m_s.get(), m_soft, m_weights, m_params);
            m_s = sls;
            while (lvl > 0) { m_s->push(); --lvl; }
            m_sls_enabled = true;
            sls->opt(m_model);
        }
    }       

    app* maxsmt_solver_base::mk_fresh_bool(char const* name) {
        app* result = m.mk_fresh_const(name, m.mk_bool_sort());
        m_mc->insert(result->get_decl());
        return result;
    }


    lbool maxsmt::operator()(opt_solver* s) {
        lbool is_sat;
        m_msolver = 0;
        m_s = s;
        IF_VERBOSE(1, verbose_stream() << "(maxsmt)\n";);
        TRACE("opt", tout << "maxsmt\n";);
        if (m_soft_constraints.empty()) {
            TRACE("opt", tout << "no constraints\n";);
            m_msolver = 0;
            is_sat = m_s->check_sat(0, 0);
        }
        else if (m_maxsat_engine == symbol("maxres")) {            
            m_msolver = mk_maxres(m, s, m_params, m_weights, m_soft_constraints);
        }
        else if (m_maxsat_engine == symbol("mus-mss-maxres")) {            
            m_msolver = mk_mus_mss_maxres(m, s, m_params, m_weights, m_soft_constraints);
        }
        else if (m_maxsat_engine == symbol("pbmax")) {
            m_msolver = mk_pbmax(m, s, m_params, m_weights, m_soft_constraints);
        }
        else if (m_maxsat_engine == symbol("wpm2")) {
            m_msolver = mk_wpm2(m, s, m_params, m_weights, m_soft_constraints);
        }
        else if (m_maxsat_engine == symbol("bcd2")) {
            m_msolver = mk_bcd2(m, s, m_params, m_weights, m_soft_constraints);
        }
        else if (m_maxsat_engine == symbol("maxhs")) {                
            m_msolver = mk_maxhs(m, s, m_params, m_weights, m_soft_constraints);
        }
        else if (m_maxsat_engine == symbol("sls")) {                
            // NB: this is experimental one-round version of SLS
            m_msolver = mk_sls(m, s, m_params, m_weights, m_soft_constraints);
        }        
        else if (is_maxsat_problem(m_weights) && m_maxsat_engine == symbol("core_maxsat")) {
            m_msolver = alloc(core_maxsat, m, *m_s, m_soft_constraints);
        }
        else if (is_maxsat_problem(m_weights) && m_maxsat_engine == symbol("fu_malik")) {
            m_msolver = alloc(fu_malik, m, *m_s, m_soft_constraints);
        }
        else {
            if (m_maxsat_engine != symbol::null && m_maxsat_engine != symbol("wmax")) {
                warning_msg("solver %s is not recognized, using default 'wmax'", 
                            m_maxsat_engine.str().c_str());
            }
            m_msolver = mk_wmax(m, m_s.get(), m_params, m_weights, m_soft_constraints);
        }

        if (m_msolver) {
            is_sat = (*m_msolver)();
            if (is_sat != l_false) {
                m_msolver->get_model(m_model);
            }
        }

        // Infrastructure for displaying and storing solution is TBD.
        IF_VERBOSE(1, verbose_stream() << "is-sat: " << is_sat << "\n";
                   if (is_sat == l_true) {
                       verbose_stream() << "Satisfying soft constraints\n";
                       display_answer(verbose_stream());
                   });

        DEBUG_CODE(if (is_sat == l_true) {
                m_s->push();
                commit_assignment();
                VERIFY(l_true == m_s->check_sat(0,0));
                m_s->pop(1);
                // TBD: check that all extensions are unsat too

            });
        return is_sat;
    }

    bool maxsmt::get_assignment(unsigned idx) const {
        if (m_msolver) {
            return m_msolver->get_assignment(idx);
        }
        else {
            return true;
        }
    } 

    rational maxsmt::get_lower() const {
        rational r = m_lower;
        if (m_msolver) {
            rational q = m_msolver->get_lower();
            if (q > r) r = q;
        }
        return r;
    }

    rational maxsmt::get_upper() const {
        rational r = m_upper;
        if (m_msolver) {
            rational q = m_msolver->get_upper();
            if (q < r) r = q;
        }
        return r;
    }

    void maxsmt::update_lower(rational const& r, bool override) {
        if (m_lower > r || override)  m_lower = r;
    }

    void maxsmt::update_upper(rational const& r, bool override) {
        if (m_upper < r || override)  m_upper = r;
    }
    

    void maxsmt::get_model(model_ref& mdl) {
        mdl = m_model.get();
    }

    void maxsmt::commit_assignment() {
        SASSERT(m_s);
        for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
            expr_ref tmp(m);
            tmp = m_soft_constraints[i].get();
            if (!get_assignment(i)) {
                tmp = m.mk_not(tmp);
            }
            TRACE("opt", tout << "committing: " << tmp << "\n";);
            m_s->assert_expr(tmp);            
        }
    }

    void maxsmt::add(expr* f, rational const& w) {
        TRACE("opt", tout << mk_pp(f, m) << " weight: " << w << "\n";);
        SASSERT(m.is_bool(f));
        SASSERT(w.is_pos());
        m_soft_constraints.push_back(f);
        m_weights.push_back(w);
        m_upper += w;
    }

    void maxsmt::display_answer(std::ostream& out) const {
        for (unsigned i = 0; i < m_soft_constraints.size(); ++i) {
            out << mk_pp(m_soft_constraints[i], m)
                << (get_assignment(i)?" |-> true\n":" |-> false\n");
        }
    }
    
    void maxsmt::set_cancel(bool f) {
        m_cancel = f;
        if (m_msolver) {
            m_msolver->set_cancel(f);
        }
    }
    
    bool maxsmt::is_maxsat_problem(vector<rational> const& ws) const {
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }

    void maxsmt::updt_params(params_ref& p) {
        opt_params _p(p);
        m_maxsat_engine = _p.maxsat_engine();        
        m_params = p;
        if (m_msolver) {
            m_msolver->updt_params(p);
        }
    }

    void maxsmt::collect_statistics(statistics& st) const {
        if (m_msolver) {
            m_msolver->collect_statistics(st);
        }
    }


};

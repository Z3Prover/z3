/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    optsmt.cpp

Abstract:
   
    Objective optimization method.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

    Suppose we obtain solution t1 = k1, ..., tn = kn-epsilon
    Assert:
      t1 > k1 \/ t2 > k2 \/ ... \/ tn >= kn
    If this solution is satisfiable, then for each t_i, maximize the 
    assignment and assert the new frontier.
    Claim: we don't necessarily have to freeze assignments of 
    t_i when optimizing assignment for t_j
    because the state will always satisfy the disjunction.
    If one of the k_i is unbounded, then omit a disjunction for it.        
    

--*/

#include <typeinfo>
#include "opt/optsmt.h"
#include "opt/opt_solver.h"
#include "opt/opt_context.h"
#include "ast/arith_decl_plugin.h"
#include "smt/theory_arith.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "model/model_pp.h"
#include "ast/rewriter/th_rewriter.h"
#include "opt/opt_params.hpp"

namespace opt {


    void optsmt::set_max(vector<inf_eps>& dst, vector<inf_eps> const& src, expr_ref_vector& fmls) {
        for (unsigned i = 0; i < src.size(); ++i) {
            if (src[i] >= dst[i]) {
                dst[i] = src[i];
                m_models.set(i, m_s->get_model_idx(i));
                m_s->get_labels(m_labels);
                m_lower_fmls[i] = fmls[i].get();
                if (dst[i].is_pos() && !dst[i].is_finite()) { // review: likely done already.
                    m_lower_fmls[i] = m.mk_false();
                    fmls[i] = m.mk_false();
                }
            }
            else if (src[i] < dst[i] && !m.is_true(m_lower_fmls[i].get())) {
                fmls[i] = m_lower_fmls[i].get();                
            }
        }
    }

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool optsmt::basic_opt() {
        lbool is_sat = l_true;

        expr_ref bound(m.mk_true(), m), tmp(m);
        expr* vars[1];

        solver::scoped_push _push(*m_s);
        while (is_sat == l_true && !m.canceled()) {

            tmp = m.mk_fresh_const("b", m.mk_bool_sort());            
            vars[0] = tmp;
            bound = m.mk_implies(tmp, bound);
            m_s->assert_expr(bound);
            is_sat = m_s->check_sat(1, vars); 
            if (is_sat == l_true) {
                bound = update_lower();
            }
        }      
        
        if (m.canceled() || is_sat == l_undef) {
            return l_undef;
        }

        // set the solution tight.
        for (unsigned i = 0; i < m_lower.size(); ++i) {
            m_upper[i] = m_lower[i];
        }
        
        return l_true;        
    }

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool optsmt::geometric_opt() {
        lbool is_sat = l_true;

        expr_ref bound(m);

        vector<inf_eps> lower(m_lower);
        unsigned steps = 0;
        unsigned step_incs = 0;
        rational delta_per_step(1);
        unsigned num_scopes = 0;
        unsigned delta_index = 0;    // index of objective to speed up.

        while (!m.canceled()) {
            SASSERT(delta_per_step.is_int());
            SASSERT(delta_per_step.is_pos());
            is_sat = m_s->check_sat(0, nullptr);
            if (is_sat == l_true) {                
                bound = update_lower();
                if (!get_max_delta(lower, delta_index)) {
                    delta_per_step = rational::one();
                }
                else if (steps > step_incs) {
                    delta_per_step *= rational(2);
                    ++step_incs;
                    steps = 0;
                }
                else {
                    ++steps;
                }
                if (delta_per_step > rational::one()) {
                    m_s->push();
                    ++num_scopes;
                    // only try to improve delta_index. 
                    bound = m_s->mk_ge(delta_index, m_lower[delta_index] + inf_eps(delta_per_step));
                }
                TRACE("opt", tout << delta_per_step << " " << bound << "\n";);
                m_s->assert_expr(bound);
            }
            else if (is_sat == l_false && delta_per_step > rational::one()) {
                steps = 0;
                step_incs = 0;
                delta_per_step = rational::one();
                SASSERT(num_scopes > 0);
                --num_scopes;
                m_s->pop(1);             
            }
            else {
                break;
            }
        }
        m_s->pop(num_scopes);        
        
        if (m.canceled() || is_sat == l_undef) {
            return l_undef;
        }

        // set the solution tight.
        for (unsigned i = 0; i < m_lower.size(); ++i) {
            m_upper[i] = m_lower[i];
        }
        
        return l_true;        
    }

    bool optsmt::is_unbounded(unsigned obj_index, bool is_maximize) {
        if (is_maximize) {
            return !m_upper[obj_index].is_finite();
        }
        else {
            return !m_lower[obj_index].is_finite();
        }
    }

    lbool optsmt::geometric_lex(unsigned obj_index, bool is_maximize) {
        TRACE("opt", tout << "index: " << obj_index << " is-max: " << is_maximize << "\n";);
        arith_util arith(m);
        bool is_int = arith.is_int(m_objs[obj_index].get());
        lbool is_sat = l_true;
        expr_ref bound(m);

        for (unsigned i = 0; i < obj_index; ++i) {
            commit_assignment(i);
        }

        unsigned steps = 0;
        unsigned step_incs = 0;
        rational delta_per_step(1);
        unsigned num_scopes = 0;

        while (!m.canceled()) {
            SASSERT(delta_per_step.is_int());
            SASSERT(delta_per_step.is_pos());
            is_sat = m_s->check_sat(0, nullptr);
            TRACE("opt", tout << "check " << is_sat << "\n";
                  tout << "lower: " << m_lower[obj_index] << "\n";
                  tout << "upper: " << m_upper[obj_index] << "\n";
                  );
            if (is_sat == l_true) {                
                m_s->maximize_objective(obj_index, bound);
                m_s->get_model(m_model);
                SASSERT(m_model);
                m_s->get_labels(m_labels);
                inf_eps obj = m_s->saved_objective_value(obj_index);
                update_lower_lex(obj_index, obj, is_maximize);
                if (!is_int || !m_lower[obj_index].is_finite()) {
                    delta_per_step = rational(1);
                }
                else if (steps > step_incs) {
                    delta_per_step *= rational(2);
                    ++step_incs;
                    steps = 0;
                }
                else {
                    ++steps;
                }
                if (delta_per_step > rational::one()) {
                    m_s->push();
                    ++num_scopes;
                    bound = m_s->mk_ge(obj_index, obj + inf_eps(delta_per_step));
                }
                TRACE("opt", tout << "delta: " << delta_per_step << " " << bound << "\n";);
                m_s->assert_expr(bound);
            }
            else if (is_sat == l_false && delta_per_step > rational::one()) {
                steps = 0;
                step_incs = 0;
                delta_per_step = rational::one();
                SASSERT(num_scopes > 0);
                --num_scopes;
                m_s->pop(1);                             
            }
            else {
                break;
            }
        }
        m_s->pop(num_scopes);        

        TRACE("opt", tout << is_sat << " " << num_scopes << "\n";);

        if (is_sat == l_false && !m_model) {
            return l_false;
        }
        
        if (m.canceled() || is_sat == l_undef) {
            return l_undef;
        }

        // set the solution tight.
        m_upper[obj_index] = m_lower[obj_index];    
        for (unsigned i = obj_index+1; i < m_lower.size(); ++i) {
            m_lower[i] = inf_eps(rational(-1), inf_rational(0));
        }
        return l_true;
    }

    bool optsmt::get_max_delta(vector<inf_eps> const& lower, unsigned& idx) {
        arith_util arith(m);
        inf_eps max_delta;
        for (unsigned i = 0; i < m_lower.size(); ++i) {
            if (arith.is_int(m_objs[i].get())) {
                inf_eps delta = m_lower[i] - lower[i];  
                if (m_lower[i].is_finite() && delta > max_delta) {
                    max_delta = delta;
                }
            }
        }
        return max_delta.is_pos();
    }

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool optsmt::farkas_opt() {
        smt::theory_opt& opt = m_s->get_optimizer();

        if (typeid(smt::theory_inf_arith) != typeid(opt)) {
            return l_undef;
        }

        lbool is_sat = l_true;

        while (is_sat == l_true && !m.canceled()) {
            is_sat = update_upper();
        }      
        
        if (m.canceled() || is_sat == l_undef) {
            return l_undef;
        }

        // set the solution tight.
        for (unsigned i = 0; i < m_lower.size(); ++i) {
            m_upper[i] = m_lower[i];
        }

        return l_true;        
    }

    lbool optsmt::symba_opt() {

        smt::theory_opt& opt = m_s->get_optimizer();

        if (typeid(smt::theory_inf_arith) != typeid(opt)) {
            return l_undef;
        }


        expr_ref_vector ors(m), disj(m);
        expr_ref fml(m), bound(m.mk_true(), m), tmp(m);
        expr* vars[1];
        {
            for (unsigned i = 0; i < m_upper.size(); ++i) {
                ors.push_back(m_s->mk_ge(i, m_upper[i]));
            }
            
            
            fml = mk_or(ors);
            tmp = m.mk_fresh_const("b", m.mk_bool_sort());
            fml = m.mk_implies(tmp, fml);
            vars[0] = tmp;
            lbool is_sat = l_true;

            solver::scoped_push _push(*m_s);
            while (!m.canceled()) {
                m_s->assert_expr(fml);
                TRACE("opt", tout << fml << "\n";);
                is_sat = m_s->check_sat(1,vars);
                if (is_sat == l_true) {
                    disj.reset();
                    m_s->maximize_objectives(disj);
                    m_s->get_model(m_model);       
                    m_s->get_labels(m_labels);            
                    for (unsigned i = 0; i < ors.size(); ++i) {
                        expr_ref tmp(m);
                        if (m_model->is_true(ors[i].get())) {
                            m_lower[i] = m_upper[i];
                            ors[i]  = m.mk_false();
                            disj[i] = m.mk_false();
                        }
                    }
                    set_max(m_lower, m_s->get_objective_values(), disj);
                    fml = mk_or(ors);
                    tmp = m.mk_fresh_const("b", m.mk_bool_sort());
                    fml = m.mk_implies(tmp, fml);
                    vars[0] = tmp;
                }
                else if (is_sat == l_undef) {
                    return l_undef;
                }
                else {
                    break;
                }
            }
        }
        bound = mk_or(m_lower_fmls);
        m_s->assert_expr(bound);
        
        if (m.canceled()) {
            return l_undef;
        }
        return geometric_opt();
    }

    void optsmt::update_lower_lex(unsigned idx, inf_eps const& v, bool is_maximize) {
        if (v > m_lower[idx]) {
            m_lower[idx] = v;                
            IF_VERBOSE(1, 
                       if (is_maximize) 
                           verbose_stream() << "(optsmt lower bound: " << v << ")\n";
                       else
                           verbose_stream() << "(optsmt upper bound: " << (-v) << ")\n";
                       );            
            expr_ref tmp(m);
            for (unsigned i = idx+1; i < m_vars.size(); ++i) {
                m_s->maximize_objective(i, tmp);
                m_lower[i] = m_s->saved_objective_value(i);
            }

            m_context.set_model(m_model);
        }
    }

    void optsmt::update_lower(unsigned idx, inf_eps const& v) {
        TRACE("opt", tout << "v" << idx << " >= " << v << "\n";);
        m_lower_fmls[idx] = m_s->mk_ge(idx, v);
        m_lower[idx] = v;                    
    }

    void optsmt::update_upper(unsigned idx, inf_eps const& v) {
        TRACE("opt", tout << "v" << idx << " <= " << v << "\n";);
        m_upper[idx] = v;                    
    }

    std::ostream& operator<<(std::ostream& out, vector<inf_eps> const& vs) {
        for (unsigned i = 0; i < vs.size(); ++i) {
            out << vs[i] << " ";
        }
        return out;
    }

    expr_ref optsmt::update_lower() {
        expr_ref_vector disj(m);
        m_s->get_model(m_model);
        m_s->get_labels(m_labels);
        m_s->maximize_objectives(disj);
        set_max(m_lower, m_s->get_objective_values(), disj);
        TRACE("opt", model_pp(tout << m_lower << "\n", *m_model););
        IF_VERBOSE(2, verbose_stream() << "(optsmt.lower " << m_lower << ")\n";);
        return mk_or(disj);
    }

    lbool optsmt::update_upper() {
        smt::theory_opt& opt = m_s->get_optimizer();
        SASSERT(typeid(smt::theory_inf_arith) == typeid(opt));
        smt::theory_inf_arith& th = dynamic_cast<smt::theory_inf_arith&>(opt); 
        expr_ref bound(m);
        expr_ref_vector bounds(m);

        solver::scoped_push _push(*m_s);

        //
        // NB: we have to create all bound expressions before calling check_sat
        // because the state after check_sat is not at base level.
        //

        vector<inf_eps> mid;

        for (unsigned i = 0; i < m_lower.size() && !m.canceled(); ++i) {
            if (m_lower[i] < m_upper[i]) {
                mid.push_back((m_upper[i]+m_lower[i])/rational(2));
                bound = m_s->mk_ge(i, mid[i]);
                bounds.push_back(bound);
            }
            else {
                bounds.push_back(nullptr);
                mid.push_back(inf_eps());
            }
        }
        bool progress = false;
        for (unsigned i = 0; i < m_lower.size() && !m.canceled(); ++i) {
            if (m_lower[i] <= mid[i] && mid[i] <= m_upper[i] && m_lower[i] < m_upper[i]) {
                th.enable_record_conflict(bounds[i].get());
                lbool is_sat = m_s->check_sat(1, bounds.c_ptr() + i);
                switch(is_sat) {
                case l_true:
                    IF_VERBOSE(2, verbose_stream() << "(optsmt lower bound for v" << m_vars[i] << " := " << m_upper[i] << ")\n";);
                    m_lower[i] = mid[i];
                    th.enable_record_conflict(nullptr);
                    m_s->assert_expr(update_lower());
                    break;
                case l_false:
                    IF_VERBOSE(2, verbose_stream() << "(optsmt conflict: " << th.conflict_minimize() << ") \n";);
                    if (!th.conflict_minimize().is_finite()) {
                        // bounds is not in the core. The context is unsat.
                        m_upper[i] = m_lower[i];
                        return l_false;
                    }
                    else {
                        m_upper[i] = std::min(m_upper[i], th.conflict_minimize());
                    }
                    break;
                default:
                    th.enable_record_conflict(nullptr);
                    return l_undef;
                }
                th.enable_record_conflict(nullptr);
                progress = true;
            }
        }
        if (m.canceled()) {
            return l_undef;
        }
        if (!progress) {
            return l_false;
        }
        return l_true;
    }

    void optsmt::setup(opt_solver& solver) {
        m_s = &solver;
        solver.reset_objectives();
        m_vars.reset();

        // force base level
        {
            solver::scoped_push _push(solver);
        }

        for (unsigned i = 0; i < m_objs.size(); ++i) {
            smt::theory_var v = solver.add_objective(m_objs[i].get());
            if (v == smt::null_theory_var) {
                std::ostringstream out;
                out << "Objective function '" << mk_pp(m_objs[i].get(), m) << "' is not supported";
                throw default_exception(out.str());
            }
            m_vars.push_back(v);
        }            
    }

    lbool optsmt::lex(unsigned obj_index, bool is_maximize) {
        TRACE("opt", tout << "optsmt:lex\n";);
        solver::scoped_push _push(*m_s);
        SASSERT(obj_index < m_vars.size());
        if (is_maximize && m_optsmt_engine == symbol("farkas")) {
            return farkas_opt();
        }
        else if (is_maximize && m_optsmt_engine == symbol("symba")) {
            return symba_opt();
        }
        else {
            return geometric_lex(obj_index, is_maximize);
        }
    }

    // deprecated
    lbool optsmt::basic_lex(unsigned obj_index, bool is_maximize) {
        lbool is_sat = l_true;
        expr_ref bound(m);

        for (unsigned i = 0; i < obj_index; ++i) {
            commit_assignment(i);
        }
        while (is_sat == l_true && !m.canceled()) {
            is_sat = m_s->check_sat(0, nullptr);
            if (is_sat != l_true) break;
            
            m_s->maximize_objective(obj_index, bound);
            m_s->get_model(m_model);
            m_s->get_labels(m_labels);
            inf_eps obj = m_s->saved_objective_value(obj_index);
            update_lower_lex(obj_index, obj, is_maximize);
            TRACE("opt", tout << "strengthen bound: " << bound << "\n";);
            m_s->assert_expr(bound);
            
            // TBD: only works for simplex 
            // blocking formula should be extracted based
            // on current state.
        }
        
        if (m.canceled() || is_sat == l_undef) {
            TRACE("opt", tout << "undef: " << m.canceled() << " " << is_sat << "\n";);
            return l_undef;
        }

        // set the solution tight.
        m_upper[obj_index] = m_lower[obj_index];    
        for (unsigned i = obj_index+1; i < m_lower.size(); ++i) {
            m_lower[i] = inf_eps(rational(-1), inf_rational(0));
        }
        return l_true;
    }



    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    lbool optsmt::box() {
        lbool is_sat = l_true;        
        if (m_vars.empty()) {
            return is_sat;
        }
        // assertions added during search are temporary.
        solver::scoped_push _push(*m_s);
        if (m_optsmt_engine == symbol("farkas")) {
            is_sat = farkas_opt();
        }
        else if (m_optsmt_engine == symbol("symba")) {
            is_sat = symba_opt();
        }
        else {
            is_sat = geometric_opt();
        }
        return is_sat;
    }


    inf_eps optsmt::get_lower(unsigned i) const {
        if (i >= m_lower.size()) return inf_eps();
        return m_lower[i];
    }

    bool optsmt::objective_is_model_valid(unsigned index) const {
        return m_s->objective_is_model_valid(index);
    }

    inf_eps optsmt::get_upper(unsigned i) const {
        if (i >= m_upper.size()) return inf_eps();
        return m_upper[i];
    }

    void optsmt::get_model(model_ref& mdl, svector<symbol> & labels) {        
        mdl = m_model.get();
        labels = m_labels;
    }

    // force lower_bound(i) <= objective_value(i)    
    void optsmt::commit_assignment(unsigned i) {
        inf_eps lo = m_lower[i];
        TRACE("opt", tout << "set lower bound of " << mk_pp(m_objs[i].get(), m) << " to: " << lo << "\n";
              tout << get_lower(i) << ":" << get_upper(i) << "\n";);    
        // Only assert bounds for bounded objectives
        if (lo.is_finite()) {
            m_s->assert_expr(m_s->mk_ge(i, lo));
        }
    }

    unsigned optsmt::add(app* t) {
        expr_ref t1(t, m), t2(m);
        th_rewriter rw(m);
        rw(t1, t2);
        SASSERT(is_app(t2));
        m_objs.push_back(to_app(t2));
        m_lower.push_back(inf_eps(rational(-1),inf_rational(0)));
        m_upper.push_back(inf_eps(rational(1), inf_rational(0)));
        m_lower_fmls.push_back(m.mk_true());
        m_models.push_back(nullptr);
        return m_objs.size()-1;
    }

    void optsmt::updt_params(params_ref& p) {
        opt_params _p(p);
        m_optsmt_engine = _p.optsmt_engine();        
    }

    void optsmt::reset() {
        m_lower.reset();
        m_upper.reset();
        m_objs.reset();
        m_vars.reset();
        m_model.reset();
        m_lower_fmls.reset();
        m_s = nullptr;
    }
}


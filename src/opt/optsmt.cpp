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
    Claim: the end result (when the constraints are no longer feasible) 
    is Pareto optimal, but convergence will probably not be as fast
    as when fixing one parameter at a time.
    E.g., a different approach is first to find a global maximal for one
    variable. Then add a method to "freeze" that variable at the extremum if it is finite.
    To do this, add lower and upper bounds for that variable using infinitesimals.
    If the variable is unbounded, then this is of course not sufficient by itself.
        
    

--*/

#ifndef _OPT_OBJECTIVE_H_
#define _OPT_OBJECTIVE_H_

#include "optsmt.h"
#include "opt_solver.h"
#include "arith_decl_plugin.h"
#include "theory_arith.h"
#include "ast_pp.h"
#include "model_pp.h"
#include "th_rewriter.h"

namespace opt {


    void optsmt::set_cancel(bool f) {
        m_cancel = true;
    }

    void optsmt::set_max(vector<inf_eps>& dst, vector<inf_eps> const& src) {
        for (unsigned i = 0; i < src.size(); ++i) {
            if (src[i] > dst[i]) {
                dst[i] = src[i];
            }
        }
    }

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool optsmt::basic_opt() {
        opt_solver::toggle_objective _t(*s, true);          
        lbool is_sat = l_true;

        while (is_sat == l_true && !m_cancel) {
            is_sat = s->check_sat(0, 0); 
            if (is_sat == l_true) {
                update_lower();
            }
        }      
        
        if (m_cancel || is_sat == l_undef) {
            return l_undef;
        }
        return l_true;        
    }

    /*
        Enumerate locally optimal assignments until fixedpoint.
    */
    lbool optsmt::farkas_opt() {
        smt::theory_opt& opt = s->get_optimizer();

        IF_VERBOSE(1, verbose_stream() << typeid(opt).name() << "\n";);
        if (typeid(smt::theory_inf_arith) != typeid(opt)) {
            return l_undef;
        }

        opt_solver::toggle_objective _t(*s, true);
        lbool is_sat= l_true;

        while (is_sat == l_true && !m_cancel) {
            is_sat = update_upper();
        }      
        
        if (m_cancel || is_sat == l_undef) {
            return l_undef;
        }
        return l_true;        
    }

    void optsmt::update_lower() {
        model_ref md;
        s->get_model(md);
        set_max(m_lower, s->get_objective_values());
        IF_VERBOSE(1, 
                   for (unsigned i = 0; i < m_lower.size(); ++i) {
                       verbose_stream() << m_lower[i] << " ";
                   }
                   verbose_stream() << "\n";
                   model_pp(verbose_stream(), *md);
                   );
        expr_ref_vector disj(m);
        expr_ref constraint(m);
        
        for (unsigned i = 0; i < m_lower.size(); ++i) {
            inf_eps const& v = m_lower[i];
            disj.push_back(s->block_lower_bound(i, v));
        }
        constraint = m.mk_or(disj.size(), disj.c_ptr());
        s->assert_expr(constraint);
    }

    lbool optsmt::update_upper() {
        smt::theory_opt& opt = s->get_optimizer();

        SASSERT(typeid(smt::theory_inf_arith) == typeid(opt));

        smt::theory_inf_arith& th = dynamic_cast<smt::theory_inf_arith&>(opt); 

        expr_ref bound(m);
        expr_ref_vector bounds(m);

        opt_solver::scoped_push _push(*s);

        //
        // NB: we have to create all bound expressions before calling check_sat
        // because the state after check_sat is not at base level.
        //

        vector<inf_eps> mid;

        for (unsigned i = 0; i < m_lower.size() && !m_cancel; ++i) {
            if (m_lower[i] < m_upper[i]) {
                smt::theory_var v = m_vars[i]; 
                mid.push_back((m_upper[i]+m_lower[i])/rational(2));
                //mid.push_back(m_upper[i]);
                bound = th.block_upper_bound(v, mid[i]);
                bounds.push_back(bound);
            }
            else {
                bounds.push_back(0);
                mid.push_back(inf_eps());
            }
        }
        bool progress = false;
        for (unsigned i = 0; i < m_lower.size() && !m_cancel; ++i) {
            if (m_lower[i] <= mid[i] && mid[i] <= m_upper[i] && m_lower[i] < m_upper[i]) {
                th.enable_record_conflict(bounds[i].get());
                lbool is_sat = s->check_sat(1, bounds.c_ptr() + i);
                switch(is_sat) {
                case l_true:
                    IF_VERBOSE(2, verbose_stream() << "Setting lower bound for v" << m_vars[i] << " to " << m_upper[i] << "\n";);
                    m_lower[i] = mid[i];
                    th.enable_record_conflict(0);
                    update_lower();
                    break;
                case l_false:
                    IF_VERBOSE(2, verbose_stream() << "conflict: " << th.conflict_minimize() << "\n";);
                    if (!th.conflict_minimize().get_infinity().is_zero()) {
                        // bounds is not in the core. The context is unsat.
                        m_upper[i] = m_lower[i];
                        return l_false;
                    }
                    else {
                        m_upper[i] = std::min(m_upper[i], th.conflict_minimize());
                    }
                    break;
                default:
                    th.enable_record_conflict(0);
                    return l_undef;
                }
                th.enable_record_conflict(0);
                progress = true;
            }
        }
        if (m_cancel) {
            return l_undef;
        }
        if (!progress) {
            return l_false;
        }
        return l_true;
    }

    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */
    lbool optsmt::operator()(opt_solver& solver) {
        s = &solver;
        s->reset_objectives();
        m_lower.reset();
        m_upper.reset();
        m_vars.reset();
        for (unsigned i = 0; i < m_objs.size(); ++i) {
            m_lower.push_back(inf_eps(rational(-1),inf_rational(0)));
            m_upper.push_back(inf_eps(rational(1), inf_rational(0)));
        }

        // First check_sat call to initialize theories
        lbool is_sat = s->check_sat(0, 0);
        if (is_sat == l_true && !m_objs.empty()) {
            opt_solver::scoped_push _push(*s);
            
            for (unsigned i = 0; i < m_objs.size(); ++i) {
                m_vars.push_back(s->add_objective(m_objs[i].get()));
            }

            if (m_engine == symbol("basic")) {
                is_sat = basic_opt();
            }
            else if (m_engine == symbol("farkas")) {
                is_sat = farkas_opt();
            }
            else {
                // TODO: implement symba engine
                // report error on bad configuration.
                NOT_IMPLEMENTED_YET();
                UNREACHABLE();
            }
        }

        std::cout << "is-sat: " << is_sat << std::endl;
        display(std::cout);

        return is_sat;
    }

    inf_eps  optsmt::get_value(bool as_positive, unsigned index) const {
        if (as_positive) {
            return m_lower[index];
        }
        else {
            return -m_lower[index];
        }
    }

    void optsmt::display(std::ostream& out) const {
        unsigned sz = m_objs.size();
        for (unsigned i = 0; i < sz; ++i) {
            bool is_max = m_is_max[i];
            inf_eps val = get_value(is_max, i);
            expr_ref obj(m_objs[i], m);
            if (!is_max) {
                arith_util a(m);
                th_rewriter rw(m);
                obj = a.mk_uminus(obj);
                rw(obj, obj);
            }
            out << "objective value: " << obj << " |-> " << val << std::endl;                
        }        
    }

    void optsmt::add(app* t, bool is_max) {
        expr_ref t1(t, m), t2(m);
        th_rewriter rw(m);
        if (!is_max) {
            arith_util a(m);
            t1 = a.mk_uminus(t);
        }
        rw(t1, t2);
        SASSERT(is_app(t2));
        m_objs.push_back(to_app(t2));
        m_is_max.push_back(is_max);
    }


}

#endif

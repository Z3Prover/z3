/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_tactic.cpp

Abstract:
    API for creating tactics and probes
    
Author:

    Leonardo de Moura (leonardo) 2012-03-06.

Revision History:

--*/
#include<iostream>
#include "api/z3.h"
#include "api/api_log_macros.h"
#include "api/api_context.h"
#include "api/api_tactic.h"
#include "api/api_model.h"
#include "util/scoped_ctrl_c.h"
#include "util/cancel_eh.h"
#include "util/scoped_timer.h"

Z3_apply_result_ref::Z3_apply_result_ref(api::context& c, ast_manager & m): api::object(c) {
}

extern "C" {

#define RETURN_TACTIC(_t_) {                                    \
        Z3_tactic_ref * _ref_ = alloc(Z3_tactic_ref, *mk_c(c)); \
        _ref_->m_tactic   = _t_;                                \
        mk_c(c)->save_object(_ref_);                            \
        Z3_tactic _result_  = of_tactic(_ref_);                 \
        RETURN_Z3(_result_);                                    \
}

#define RETURN_PROBE(_t_) {                                     \
        Z3_probe_ref * _ref_ = alloc(Z3_probe_ref, *mk_c(c));   \
        _ref_->m_probe   = _t_;                                 \
        mk_c(c)->save_object(_ref_);                            \
        Z3_probe _result_  = of_probe(_ref_);                   \
        RETURN_Z3(_result_);                                    \
}

    Z3_tactic Z3_API Z3_mk_tactic(Z3_context c, Z3_string name) {
        Z3_TRY;
        LOG_Z3_mk_tactic(c, name);
        RESET_ERROR_CODE();
        tactic_cmd * t = mk_c(c)->find_tactic_cmd(symbol(name));
        if (t == nullptr) {
            std::stringstream err;
            err << "unknown tactic " << name;
            SET_ERROR_CODE(Z3_INVALID_ARG, err.str().c_str());
            RETURN_Z3(nullptr);
        }
        tactic * new_t = t->mk(mk_c(c)->m());
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_tactic_inc_ref(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_tactic_inc_ref(c, t);
        RESET_ERROR_CODE();
        to_tactic(t)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_tactic_dec_ref(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_tactic_dec_ref(c, t);
        RESET_ERROR_CODE();
        to_tactic(t)->dec_ref();
        Z3_CATCH;
    }

    Z3_probe Z3_API Z3_mk_probe(Z3_context c, Z3_string name) {
        Z3_TRY;
        LOG_Z3_mk_probe(c, name);
        RESET_ERROR_CODE();
        probe_info * p = mk_c(c)->find_probe(symbol(name));
        if (p == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            RETURN_Z3(nullptr);
        }
        probe * new_p = p->get();
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    void Z3_API Z3_probe_inc_ref(Z3_context c, Z3_probe p) {
        Z3_TRY;
        LOG_Z3_probe_inc_ref(c, p);
        RESET_ERROR_CODE();
        to_probe(p)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_probe_dec_ref(Z3_context c, Z3_probe p) {
        Z3_TRY;
        LOG_Z3_probe_dec_ref(c, p);
        RESET_ERROR_CODE();
        to_probe(p)->dec_ref();
        Z3_CATCH;
    }

    Z3_tactic Z3_API Z3_tactic_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2) {
        Z3_TRY;
        LOG_Z3_tactic_and_then(c, t1, t2);
        RESET_ERROR_CODE();
        tactic * new_t = and_then(to_tactic_ref(t1), to_tactic_ref(t2));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_or_else(Z3_context c, Z3_tactic t1, Z3_tactic t2) {
        Z3_TRY;
        LOG_Z3_tactic_or_else(c, t1, t2);
        RESET_ERROR_CODE();
        tactic * new_t = or_else(to_tactic_ref(t1), to_tactic_ref(t2));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_par_or(Z3_context c, unsigned num, Z3_tactic const ts[]) {
        Z3_TRY;
        LOG_Z3_tactic_par_or(c, num, ts);
        RESET_ERROR_CODE();
        ptr_buffer<tactic> _ts;
        for (unsigned i = 0; i < num; i++) {
            _ts.push_back(to_tactic_ref(ts[i]));
        }
        tactic * new_t = par(num, _ts.c_ptr());
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_par_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2) {
        Z3_TRY;
        LOG_Z3_tactic_par_and_then(c, t1, t2);
        RESET_ERROR_CODE();
        tactic * new_t = par_and_then(to_tactic_ref(t1), to_tactic_ref(t2));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_try_for(Z3_context c, Z3_tactic t, unsigned ms) {
        Z3_TRY;
        LOG_Z3_tactic_try_for(c, t, ms);
        RESET_ERROR_CODE();
        tactic * new_t = try_for(to_tactic_ref(t), ms);
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_when(Z3_context c, Z3_probe p, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_tactic_when(c, p, t);
        RESET_ERROR_CODE();
        tactic * new_t = when(to_probe_ref(p), to_tactic_ref(t));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }
    
    Z3_tactic Z3_API Z3_tactic_cond(Z3_context c, Z3_probe p, Z3_tactic t1, Z3_tactic t2) {
        Z3_TRY;
        LOG_Z3_tactic_cond(c, p, t1, t2);
        RESET_ERROR_CODE();
        tactic * new_t = cond(to_probe_ref(p), to_tactic_ref(t1), to_tactic_ref(t2));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_repeat(Z3_context c, Z3_tactic t, unsigned max) {
        Z3_TRY;
        LOG_Z3_tactic_repeat(c, t, max);
        RESET_ERROR_CODE();
        tactic * new_t = repeat(to_tactic_ref(t), max);
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_skip(Z3_context c) {
        Z3_TRY;
        LOG_Z3_tactic_skip(c);
        RESET_ERROR_CODE();
        tactic * new_t = mk_skip_tactic();
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_fail(Z3_context c) {
        Z3_TRY;
        LOG_Z3_tactic_fail(c);
        RESET_ERROR_CODE();
        tactic * new_t = mk_fail_tactic();
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_fail_if(Z3_context c, Z3_probe p) {
        Z3_TRY;
        LOG_Z3_tactic_fail_if(c, p);
        RESET_ERROR_CODE();
        tactic * new_t = fail_if(to_probe_ref(p));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_fail_if_not_decided(Z3_context c) {
        Z3_TRY;
        LOG_Z3_tactic_fail_if_not_decided(c);
        RESET_ERROR_CODE();
        tactic * new_t = mk_fail_if_undecided_tactic();
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_tactic Z3_API Z3_tactic_using_params(Z3_context c, Z3_tactic t, Z3_params p) {
        Z3_TRY;
        LOG_Z3_tactic_using_params(c, t, p);
        RESET_ERROR_CODE();
        param_descrs r;
        to_tactic_ref(t)->collect_param_descrs(r);
        to_param_ref(p).validate(r);
        tactic * new_t = using_params(to_tactic_ref(t), to_param_ref(p));
        RETURN_TACTIC(new_t);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_const(Z3_context c, double val) {
        Z3_TRY;
        LOG_Z3_probe_const(c, val);
        RESET_ERROR_CODE();
        probe * new_p = mk_const_probe(val);
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }
    
    Z3_probe Z3_API Z3_probe_lt(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_lt(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_lt(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_gt(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_gt(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_gt(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_le(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_le(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_le(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_ge(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_ge(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_ge(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_eq(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_eq(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_eq(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_and(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_and(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_and(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_or(Z3_context c, Z3_probe p1, Z3_probe p2) {
        Z3_TRY;
        LOG_Z3_probe_or(c, p1, p2);
        RESET_ERROR_CODE();
        probe * new_p = mk_or(to_probe_ref(p1), to_probe_ref(p2));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_probe Z3_API Z3_probe_not(Z3_context c, Z3_probe p) {
        Z3_TRY;
        LOG_Z3_probe_not(c, p);
        RESET_ERROR_CODE();
        probe * new_p = mk_not(to_probe_ref(p));
        RETURN_PROBE(new_p);
        Z3_CATCH_RETURN(nullptr);
    }

    unsigned Z3_API Z3_get_num_tactics(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_num_tactics(c);
        RESET_ERROR_CODE();
        return mk_c(c)->num_tactics();
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_get_tactic_name(Z3_context c, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_tactic_name(c, idx);
        RESET_ERROR_CODE();
        if (idx >= mk_c(c)->num_tactics()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return "";
        }
        return mk_c(c)->get_tactic(idx)->get_name().bare_str();
        Z3_CATCH_RETURN("");
    }

    unsigned Z3_API Z3_get_num_probes(Z3_context c) {
        Z3_TRY;
        LOG_Z3_get_num_probes(c);
        RESET_ERROR_CODE();
        return mk_c(c)->num_probes();
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_get_probe_name(Z3_context c, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_probe_name(c, idx);
        RESET_ERROR_CODE();
        if (idx >= mk_c(c)->num_probes()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            return "";
        }
        return mk_c(c)->get_probe(idx)->get_name().bare_str();
        Z3_CATCH_RETURN("");
    }

    Z3_string Z3_API Z3_tactic_get_help(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_tactic_get_help(c, t);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        param_descrs descrs;
        to_tactic_ref(t)->collect_param_descrs(descrs);
        descrs.display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_param_descrs Z3_API Z3_tactic_get_param_descrs(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_tactic_get_param_descrs(c, t);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref, *mk_c(c));
        mk_c(c)->save_object(d);
        to_tactic_ref(t)->collect_param_descrs(d->m_descrs);
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }

    Z3_string Z3_API Z3_tactic_get_descr(Z3_context c, Z3_string name) {
        Z3_TRY;
        LOG_Z3_tactic_get_descr(c, name);
        RESET_ERROR_CODE();
        tactic_cmd * t = mk_c(c)->find_tactic_cmd(symbol(name));
        if (t == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return "";
        }
        return t->get_descr();
        Z3_CATCH_RETURN("");
    }
    
    Z3_string Z3_API Z3_probe_get_descr(Z3_context c, Z3_string name) {
        Z3_TRY;
        LOG_Z3_probe_get_descr(c, name);
        RESET_ERROR_CODE();
        probe_info * p = mk_c(c)->find_probe(symbol(name));
        if (p == nullptr) {
            SET_ERROR_CODE(Z3_INVALID_ARG, nullptr);
            return "";
        }
        return p->get_descr();
        Z3_CATCH_RETURN("");
    }

    static Z3_apply_result _tactic_apply(Z3_context c, Z3_tactic t, Z3_goal g, params_ref p) {
        goal_ref new_goal;
        new_goal = alloc(goal, *to_goal_ref(g));
        Z3_apply_result_ref * ref = alloc(Z3_apply_result_ref, (*mk_c(c)), mk_c(c)->m());
        mk_c(c)->save_object(ref); 

        unsigned timeout     = p.get_uint("timeout", UINT_MAX);
        bool     use_ctrl_c  = p.get_bool("ctrl_c", false);
        cancel_eh<reslimit> eh(mk_c(c)->m().limit());
        
        to_tactic_ref(t)->updt_params(p);

        api::context::set_interruptable si(*(mk_c(c)), eh);
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            try {
                exec(*to_tactic_ref(t), new_goal, ref->m_subgoals);
                ref->m_pc = new_goal->pc();
                ref->m_mc = new_goal->mc();
                return of_apply_result(ref);
            }
            catch (z3_exception & ex) {
                mk_c(c)->handle_exception(ex);
                return nullptr;
            }
        }
    }

    double Z3_API Z3_probe_apply(Z3_context c, Z3_probe p, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_probe_apply(c, p, g);
        RESET_ERROR_CODE();
        return to_probe_ref(p)->operator()(*to_goal_ref(g)).get_value();
        Z3_CATCH_RETURN(0);
    }

    Z3_apply_result Z3_API Z3_tactic_apply(Z3_context c, Z3_tactic t, Z3_goal g) {
        Z3_TRY;
        LOG_Z3_tactic_apply(c, t, g);
        RESET_ERROR_CODE();
        params_ref p;
        Z3_apply_result r = _tactic_apply(c, t, g, p);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    Z3_apply_result Z3_API Z3_tactic_apply_ex(Z3_context c, Z3_tactic t, Z3_goal g, Z3_params p) {
        Z3_TRY;
        LOG_Z3_tactic_apply_ex(c, t, g, p);
        RESET_ERROR_CODE();
        param_descrs pd;
        to_tactic_ref(t)->collect_param_descrs(pd);
        to_param_ref(p).validate(pd);
        Z3_apply_result r = _tactic_apply(c, t, g, to_param_ref(p));
        RETURN_Z3(r);
        Z3_CATCH_RETURN(nullptr);
    }
    
    void Z3_API Z3_apply_result_inc_ref(Z3_context c, Z3_apply_result r) {
        Z3_TRY;
        LOG_Z3_apply_result_inc_ref(c, r);
        RESET_ERROR_CODE();
        to_apply_result(r)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_apply_result_dec_ref(Z3_context c, Z3_apply_result r) {
        Z3_TRY;
        LOG_Z3_apply_result_dec_ref(c, r);
        RESET_ERROR_CODE();
        to_apply_result(r)->dec_ref();
        Z3_CATCH;
    }
    
    Z3_string Z3_API Z3_apply_result_to_string(Z3_context c, Z3_apply_result r) {
        Z3_TRY;
        LOG_Z3_apply_result_to_string(c, r);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        buffer << "(goals\n";
        unsigned sz = to_apply_result(r)->m_subgoals.size();
        for (unsigned i = 0; i < sz; i++) {
            to_apply_result(r)->m_subgoals[i]->display(buffer);
        }
        buffer << ")";
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }
    
    unsigned Z3_API Z3_apply_result_get_num_subgoals(Z3_context c, Z3_apply_result r) {
        Z3_TRY;
        LOG_Z3_apply_result_get_num_subgoals(c, r);
        RESET_ERROR_CODE();
        return to_apply_result(r)->m_subgoals.size();
        Z3_CATCH_RETURN(0);
    }
    
    Z3_goal Z3_API Z3_apply_result_get_subgoal(Z3_context c, Z3_apply_result r, unsigned i) {
        Z3_TRY;
        LOG_Z3_apply_result_get_subgoal(c, r, i);
        RESET_ERROR_CODE();
        if (i > to_apply_result(r)->m_subgoals.size()) {
            SET_ERROR_CODE(Z3_IOB, nullptr);
            RETURN_Z3(nullptr);
        }
        Z3_goal_ref * g = alloc(Z3_goal_ref, *mk_c(c));
        g->m_goal       = to_apply_result(r)->m_subgoals[i];
        mk_c(c)->save_object(g);
        Z3_goal result  = of_goal(g);
        RETURN_Z3(result);
        Z3_CATCH_RETURN(nullptr);
    }
    

};

/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_solver.cpp

Abstract:
    New solver API

Author:

    Leonardo de Moura (leonardo) 2012-03-07.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_tactic.h"
#include"api_solver.h"
#include"api_model.h"
#include"api_stats.h"
#include"api_ast_vector.h"
#include"tactic2solver.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"
#include"scoped_timer.h"
#include"smt_strategic_solver.h"
#include"smt_solver.h"
#include"smt_implied_equalities.h"

extern "C" {

    static void init_solver_core(Z3_context c, Z3_solver _s) {
        Z3_solver_ref * s = to_solver(_s);
        bool proofs_enabled, models_enabled, unsat_core_enabled;
        params_ref p = s->m_params;
        mk_c(c)->params().get_solver_params(mk_c(c)->m(), p, proofs_enabled, models_enabled, unsat_core_enabled);
        s->m_solver = (*(s->m_solver_factory))(mk_c(c)->m(), p, proofs_enabled, models_enabled, unsat_core_enabled, s->m_logic);
        
        param_descrs r;
        s->m_solver->collect_param_descrs(r);
        context_params::collect_solver_param_descrs(r);
        p.validate(r);
        s->m_solver->updt_params(p);
    }

    static void init_solver(Z3_context c, Z3_solver s) {
        if (to_solver(s)->m_solver.get() == 0)
            init_solver_core(c, s);
    }

    Z3_solver Z3_API Z3_mk_simple_solver(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_simple_solver(c);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, mk_smt_solver_factory());
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_mk_solver(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_solver(c);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, mk_smt_strategic_solver_factory());
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic) {
        Z3_TRY;
        LOG_Z3_mk_solver_for_logic(c, logic);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, mk_smt_strategic_solver_factory(to_symbol(logic)));
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_solver Z3_API Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t) {
        Z3_TRY;
        LOG_Z3_mk_solver_from_tactic(c, t);
        RESET_ERROR_CODE();
        Z3_solver_ref * s = alloc(Z3_solver_ref, mk_tactic2solver_factory(to_tactic_ref(t)));
        mk_c(c)->save_object(s);
        Z3_solver r = of_solver(s);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_solver_get_help(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_help(c, s);
        RESET_ERROR_CODE();
        std::ostringstream buffer;
        param_descrs descrs;
        bool initialized = to_solver(s)->m_solver.get() != 0;
        if (!initialized)
            init_solver(c, s);
        to_solver_ref(s)->collect_param_descrs(descrs);
        context_params::collect_solver_param_descrs(descrs);
        if (!initialized)
            to_solver(s)->m_solver = 0;
        descrs.display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }

    Z3_param_descrs Z3_API Z3_solver_get_param_descrs(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_param_descrs(c, s);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref);
        mk_c(c)->save_object(d);
        bool initialized = to_solver(s)->m_solver.get() != 0;
        if (!initialized)
            init_solver(c, s);
        to_solver_ref(s)->collect_param_descrs(d->m_descrs);
        context_params::collect_solver_param_descrs(d->m_descrs);
        if (!initialized)
            to_solver(s)->m_solver = 0;
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p) {
        Z3_TRY;
        LOG_Z3_solver_set_params(c, s, p);
        RESET_ERROR_CODE();

        if (to_solver(s)->m_solver) {
            bool old_model = to_solver(s)->m_params.get_bool("model", true);
            bool new_model = to_param_ref(p).get_bool("model", true);
            if (old_model != new_model)
                to_solver_ref(s)->set_produce_models(new_model);
            param_descrs r;
            to_solver_ref(s)->collect_param_descrs(r);
            context_params::collect_solver_param_descrs(r);
            to_param_ref(p).validate(r);
            to_solver_ref(s)->updt_params(to_param_ref(p));
        }
        to_solver(s)->m_params.append(to_param_ref(p));
        Z3_CATCH;
    }
    
    void Z3_API Z3_solver_inc_ref(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_inc_ref(c, s);
        RESET_ERROR_CODE();
        to_solver(s)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_solver_dec_ref(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_dec_ref(c, s);
        RESET_ERROR_CODE();
        to_solver(s)->dec_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_solver_push(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_push(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        to_solver_ref(s)->push();
        Z3_CATCH;
    }

    void Z3_API Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n) {
        Z3_TRY;
        LOG_Z3_solver_pop(c, s, n);
        RESET_ERROR_CODE();
        init_solver(c, s);
        if (n > to_solver_ref(s)->get_scope_level()) {
            SET_ERROR_CODE(Z3_IOB);
            return;
        }
        if (n > 0)
            to_solver_ref(s)->pop(n);
        Z3_CATCH;
    }

    void Z3_API Z3_solver_reset(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_reset(c, s);
        RESET_ERROR_CODE();
        to_solver(s)->m_solver = 0;
        Z3_CATCH;
    }
    
    unsigned Z3_API Z3_solver_get_num_scopes(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_num_scopes(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return to_solver_ref(s)->get_scope_level();
        Z3_CATCH_RETURN(0);
    }
    
    void Z3_API Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_solver_assert(c, s, a);
        RESET_ERROR_CODE();
        init_solver(c, s);
        CHECK_FORMULA(a,);
        to_solver_ref(s)->assert_expr(to_expr(a));
        Z3_CATCH;
    }

    void Z3_API Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p) {
        Z3_TRY;
        LOG_Z3_solver_assert_and_track(c, s, a, p);
        RESET_ERROR_CODE();
        init_solver(c, s);
        CHECK_FORMULA(a,);
        CHECK_FORMULA(p,);
        to_solver_ref(s)->assert_expr(to_expr(a), to_expr(p));
        Z3_CATCH;
    }
    
    Z3_ast_vector Z3_API Z3_solver_get_assertions(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_assertions(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, mk_c(c)->m());
        mk_c(c)->save_object(v);
        unsigned sz = to_solver_ref(s)->get_num_assertions();
        for (unsigned i = 0; i < sz; i++) {
            v->m_ast_vector.push_back(to_solver_ref(s)->get_assertion(i));
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(0);
    }

    static Z3_lbool _solver_check(Z3_context c, Z3_solver s, unsigned num_assumptions, Z3_ast const assumptions[]) {
        for (unsigned i = 0; i < num_assumptions; i++) {
            if (!is_expr(to_ast(assumptions[i]))) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                return Z3_L_UNDEF;
            }
        }
        expr * const * _assumptions = to_exprs(assumptions);
        unsigned timeout     = to_solver(s)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        bool     use_ctrl_c  = to_solver(s)->m_params.get_bool("ctrl_c", false);
        cancel_eh<solver> eh(*to_solver_ref(s));
        api::context::set_interruptable si(*(mk_c(c)), eh);
        lbool result;
        {
            scoped_ctrl_c ctrlc(eh, false, use_ctrl_c);
            scoped_timer timer(timeout, &eh);
            try {
                result = to_solver_ref(s)->check_sat(num_assumptions, _assumptions);
            }
            catch (z3_exception & ex) {
                mk_c(c)->handle_exception(ex);
                return Z3_L_UNDEF;
            }
        }
        return static_cast<Z3_lbool>(result);
    }
    
    Z3_lbool Z3_API Z3_solver_check(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_check(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return _solver_check(c, s, 0, 0);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    Z3_lbool Z3_API Z3_solver_check_assumptions(Z3_context c, Z3_solver s, unsigned num_assumptions, Z3_ast const assumptions[]) {
        Z3_TRY;
        LOG_Z3_solver_check_assumptions(c, s, num_assumptions, assumptions);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return _solver_check(c, s, num_assumptions, assumptions);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }
    
    Z3_model Z3_API Z3_solver_get_model(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_model(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        model_ref _m;
        to_solver_ref(s)->get_model(_m);
        if (!_m) {
            SET_ERROR_CODE(Z3_INVALID_USAGE);
            RETURN_Z3(0);
        }
        Z3_model_ref * m_ref = alloc(Z3_model_ref); 
        m_ref->m_model = _m;
        mk_c(c)->save_object(m_ref);
        RETURN_Z3(of_model(m_ref));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_API Z3_solver_get_proof(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_proof(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        proof * p = to_solver_ref(s)->get_proof();
        if (!p) {
            SET_ERROR_CODE(Z3_INVALID_USAGE);
            RETURN_Z3(0);
        }
        mk_c(c)->save_ast_trail(p);
        RETURN_Z3(of_ast(p));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast_vector Z3_API Z3_solver_get_unsat_core(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_unsat_core(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        ptr_vector<expr> core;
        to_solver_ref(s)->get_unsat_core(core);
        Z3_ast_vector_ref * v = alloc(Z3_ast_vector_ref, mk_c(c)->m());
        mk_c(c)->save_object(v);
        for (unsigned i = 0; i < core.size(); i++) {
            v->m_ast_vector.push_back(core[i]);
        }
        RETURN_Z3(of_ast_vector(v));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_string Z3_API Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_reason_unknown(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        return mk_c(c)->mk_external_string(to_solver_ref(s)->reason_unknown());
        Z3_CATCH_RETURN("");
    }
    
    Z3_stats Z3_API Z3_solver_get_statistics(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_get_statistics(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        Z3_stats_ref * st = alloc(Z3_stats_ref);
        to_solver_ref(s)->collect_statistics(st->m_stats);
        get_memory_statistics(st->m_stats);
        mk_c(c)->save_object(st);
        Z3_stats r = of_stats(st);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_string Z3_API Z3_solver_to_string(Z3_context c, Z3_solver s) {
        Z3_TRY;
        LOG_Z3_solver_to_string(c, s);
        RESET_ERROR_CODE();
        init_solver(c, s);
        std::ostringstream buffer;
        to_solver_ref(s)->display(buffer);
        return mk_c(c)->mk_external_string(buffer.str());
        Z3_CATCH_RETURN("");
    }


    Z3_lbool Z3_API Z3_get_implied_equalities(Z3_context c, 
                                              Z3_solver s,
                                              unsigned num_terms,
                                              Z3_ast const terms[],
                                              unsigned class_ids[]) {
        Z3_TRY;
        LOG_Z3_get_implied_equalities(c, s, num_terms, terms, class_ids);
        ast_manager& m = mk_c(c)->m();
        RESET_ERROR_CODE();
        CHECK_SEARCHING(c);
        init_solver(c, s);
        lbool result = smt::implied_equalities(m, *to_solver_ref(s), num_terms, to_exprs(terms), class_ids);
        return static_cast<Z3_lbool>(result); 
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

};

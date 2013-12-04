/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    api_opt.cpp

Abstract:
    API for optimization 

Author:

    Nikolaj Bjorner (nbjorner) 2013-12-3.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"opt_context.h"
#include"cancel_eh.h"
#include"scoped_timer.h"

extern "C" {

    struct Z3_optimize_ref : public api::object {
        opt::context* m_opt;
        Z3_optimize_ref():m_opt(0) {}
        virtual ~Z3_optimize_ref() { dealloc(m_opt); }
    };
    inline Z3_optimize_ref * to_optimize(Z3_optimize o) { return reinterpret_cast<Z3_optimize_ref *>(o); }
    inline Z3_optimize of_optimize(Z3_optimize_ref * o) { return reinterpret_cast<Z3_optimize>(o); }
    inline opt::context& to_optimize_ref(Z3_optimize o) { return *to_optimize(o)->m_opt; }

    Z3_optimize Z3_API Z3_mk_optimize(Z3_context c) {
        Z3_TRY;
        LOG_Z3_mk_optimize(c);
        RESET_ERROR_CODE();
        Z3_optimize_ref * o = alloc(Z3_optimize_ref);
        o->m_opt = alloc(opt::context,mk_c(c)->m());
        mk_c(c)->save_object(o);
        RETURN_Z3(of_optimize(o));
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_optimize_inc_ref(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_inc_ref(c, o);
        RESET_ERROR_CODE();
        to_optimize(o)->inc_ref();
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_dec_ref(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_dec_ref(c, o);
        RESET_ERROR_CODE();
        to_optimize(o)->dec_ref();
        Z3_CATCH;
    }
    
    void Z3_API Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a) {
        Z3_TRY;
        LOG_Z3_optimize_assert(c, o, a);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        to_optimize_ref(o).add_hard_constraint(to_expr(a));
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a, Z3_string weight, Z3_symbol id) {
        Z3_TRY;
        LOG_Z3_optimize_assert_soft(c, o, a, weight, id);
        RESET_ERROR_CODE();
        CHECK_FORMULA(a,);        
        rational w("weight");
        to_optimize_ref(o).add_soft_constraint(to_expr(a), w, to_symbol(id));
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_maximize(Z3_context c, Z3_optimize o, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_optimize_maximize(c, o, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t,);        
        to_optimize_ref(o).add_objective(to_app(t), true);
        Z3_CATCH;
    }

    void Z3_API Z3_optimize_minimize(Z3_context c, Z3_optimize o, Z3_ast t) {
        Z3_TRY;
        LOG_Z3_optimize_minimize(c, o, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t,);        
        to_optimize_ref(o).add_objective(to_app(t), false);
        Z3_CATCH;
    }

    Z3_lbool Z3_API Z3_optimize_check(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_check(c, o);
        RESET_ERROR_CODE();
        lbool r = l_undef;
        cancel_eh<opt::context> eh(to_optimize_ref(o));
        unsigned timeout = 0; // to_optimize(o)->m_params.get_uint("timeout", mk_c(c)->get_timeout());
        api::context::set_interruptable si(*(mk_c(c)), eh);        
        {
            scoped_timer timer(timeout, &eh);
            try {
                r = to_optimize_ref(o).optimize();
            }
            catch (z3_exception& ex) {
                mk_c(c)->handle_exception(ex);
                r = l_undef;
            }
            // to_optimize_ref(d).cleanup();
        }
        return of_lbool(r);
        Z3_CATCH_RETURN(Z3_L_UNDEF);
    }

    void Z3_API Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p) {
        Z3_TRY;
        LOG_Z3_optimize_set_params(c, o, p);
        RESET_ERROR_CODE();
        param_descrs descrs;
        to_optimize_ref(o).collect_param_descrs(descrs);
        to_params(p)->m_params.validate(descrs);
        to_optimize_ref(o).updt_params(to_param_ref(p));
        Z3_CATCH;
    }
    
    Z3_param_descrs Z3_API Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o) {
        Z3_TRY;
        LOG_Z3_optimize_get_param_descrs(c, o);
        RESET_ERROR_CODE();
        Z3_param_descrs_ref * d = alloc(Z3_param_descrs_ref);
        mk_c(c)->save_object(d);
        to_optimize_ref(o).collect_param_descrs(d->m_descrs);
        Z3_param_descrs r = of_param_descrs(d);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    // get lower value or current approximation
    Z3_ast Z3_API Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned idx) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    // get upper or current approximation
    Z3_ast Z3_API Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned idx) {
        NOT_IMPLEMENTED_YET();
        return 0;
    }

#if 0

    /**
       \brief version with assumptions.

    */

    void check_assumptions;

    /**
       \brief retrieve the next answer. There are three modes:

       - the optimization context has been configured to produce partial results.
         It returns with L_UNDEF and an partial result and caller can retrieve
         the results by querying get_lower and get_upper.
       - The full result was produced and it returned L_TRUE. 
         Retrieve the next result that has the same objective optimal.
       - The context was configured to compute a Pareto front.
         Search proceeds incrementally identifying feasible boxes.
         Every return value is a new sub-box or set of sub-boxes.
     */
    void Z3_optimize_get_next(Z3_context c, Z3_optimize o) {
    }
    
    // 
#endif

};

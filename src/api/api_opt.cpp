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

extern "C" {

    struct Z3_optimize_ref : public api::object {
        opt::context* m_opt;
        Z3_optimize_ref():m_opt(0) {}
        virtual ~Z3_optimize_ref() { dealloc(m_opt); }
    };
    inline Z3_optimize_ref * to_optimize(Z3_optimize o) { return reinterpret_cast<Z3_optimize_ref *>(o); }
    inline Z3_optimize of_optimize(Z3_optimize_ref * o) { return reinterpret_cast<Z3_optimize>(o); }

    Z3_optimize Z3_API Z3_mk_optimize(Z3_context c) {
        return 0;
    }

    void Z3_API Z3_optimize_inc_ref(Z3_context c, Z3_optimize o) {

    }

    void Z3_API Z3_optimize_dec_ref(Z3_context c, Z3_optimize o) {

    }
    
    void Z3_API Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a) {

    }

    void Z3_API Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a, Z3_string weight, Z3_symbol id) {

    }

    void Z3_API Z3_optimize_maximize(Z3_context, Z3_optimize o, Z3_ast t) {

    }

    void Z3_API Z3_optimize_minimize(Z3_context, Z3_optimize o, Z3_ast t) {

    }

    Z3_lbool Z3_API Z3_optimize_check(Z3_context c) {
        return Z3_L_UNDEF;
    }

    void Z3_API Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p) {

    }
    
    Z3_param_descrs Z3_API Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o) {
        return 0;
    }
    

    // get lower value or current approximation
    Z3_ast Z3_API Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned idx) {
        return 0;
    }

    // get upper or current approximation
    Z3_ast Z3_API Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned idx) {
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

/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_polynomial.cpp

Abstract:

    Polynomial manager and caches for the external API.

Author:

    Leonardo de Moura (leonardo) 2012-12-08

Notes:
    
--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_polynomial.h"
#include"api_ast_vector.h"
#include"expr2polynomial.h"
#include"cancel_eh.h"
#include"scoped_timer.h"
#include"expr2var.h"

namespace api {

    pmanager::pmanager(reslimit& lim):
        m_pm(lim, m_nm) {
    }

    pmanager::~pmanager() {
    }
    
};

extern "C" {

    Z3_ast_vector Z3_API Z3_polynomial_subresultants(Z3_context c, Z3_ast p, Z3_ast q, Z3_ast x) {
        Z3_TRY;
        LOG_Z3_polynomial_subresultants(c, p, q, x);
        RESET_ERROR_CODE();
        polynomial::manager & pm = mk_c(c)->pm();
        polynomial_ref _p(pm), _q(pm);
        polynomial::scoped_numeral d(pm.m());
        default_expr2polynomial converter(mk_c(c)->m(), pm);
        if (!converter.to_polynomial(to_expr(p), _p, d) ||
            !converter.to_polynomial(to_expr(q), _q, d)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        Z3_ast_vector_ref* result = alloc(Z3_ast_vector_ref, mk_c(c)->m());
        mk_c(c)->save_object(result);
        if (converter.is_var(to_expr(x))) {
            expr2var const & mapping = converter.get_mapping();
            unsigned v_x = mapping.to_var(to_expr(x));
            polynomial_ref_vector rs(pm);
            polynomial_ref r(pm);
            expr_ref _r(mk_c(c)->m());

            {
                cancel_eh<reslimit> eh(mk_c(c)->poly_limit());
                api::context::set_interruptable si(*(mk_c(c)), eh);
                scoped_timer timer(mk_c(c)->params().m_timeout, &eh);
                pm.psc_chain(_p, _q, v_x, rs);
            }
            for (unsigned i = 0; i < rs.size(); i++) {
                r = rs.get(i);
                converter.to_expr(r, true, _r);
                result->m_ast_vector.push_back(_r);
            }
        }
        RETURN_Z3(of_ast_vector(result));
        Z3_CATCH_RETURN(0);
    }

};

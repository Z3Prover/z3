/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_poly.cpp

Abstract:

    External API for polynomial package
    
Author:

    Leonardo de Moura (leonardo) 2012-10-18.

Revision History:

--*/
#include"z3.h"
#include"z3_internal.h"
#include"api_context.h"
#include"api_poly.h"
#include"api_util.h"
#include"api_log_macros.h"

Z3_polynomial_manager Z3_mk_polynomial_manager(Z3_context c) {
    Z3_TRY;
    LOG_Z3_mk_polynomial_manager(c);
    RESET_ERROR_CODE();
    _Z3_polynomial_manager * m = alloc(_Z3_polynomial_manager);
    RETURN_Z3(of_poly_manager(m));
    Z3_CATCH_RETURN(0);
}

void Z3_del_polynomial_manager(Z3_context c, Z3_polynomial_manager m) {
    Z3_TRY;
    LOG_Z3_del_polynomial_manager(c, m);
    RESET_ERROR_CODE();
    dealloc(to_poly_manager(m));
    Z3_CATCH;
}

Z3_polynomial Z3_mk_zero_polynomial(Z3_context c, Z3_polynomial_manager m) {
    Z3_TRY;
    LOG_Z3_mk_zero_polynomial(c, m);
    RESET_ERROR_CODE();
    polynomial::polynomial * r = to_poly_manager(m)->m_manager.mk_zero();
    to_poly_manager(m)->m_result = r;
    RETURN_Z3(of_poly(r));
    Z3_CATCH_RETURN(0);
}

void Z3_polynomial_inc_ref(Z3_context c, Z3_polynomial_manager m, Z3_polynomial p) {
    Z3_TRY;
    LOG_Z3_polynomial_inc_ref(c, m, p);
    RESET_ERROR_CODE();
    to_poly_manager(m)->m_manager.inc_ref(to_poly(p));
    Z3_CATCH;
}

void Z3_polynomial_dec_ref(Z3_context c, Z3_polynomial_manager m, Z3_polynomial p) {
    Z3_TRY;
    LOG_Z3_polynomial_inc_ref(c, m, p);
    RESET_ERROR_CODE();
    to_poly_manager(m)->m_manager.dec_ref(to_poly(p));
    Z3_CATCH;
}

Z3_string Z3_polynomial_to_string(Z3_context c, Z3_polynomial_manager m, Z3_polynomial p) {
    Z3_TRY;
    LOG_Z3_polynomial_to_string(c, m, p);
    RESET_ERROR_CODE();
    std::ostringstream buffer;
    to_poly_manager(m)->m_manager.display(buffer, to_poly(p));
    return mk_c(c)->mk_external_string(buffer.str());
    Z3_CATCH_RETURN("");
}


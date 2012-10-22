/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_poly.h

Abstract:

    Z3 multivariate polynomial API.

Author:

    Leonardo de Moura (leonardo) 2012-10-18

Notes:
    
--*/
#ifndef _Z3_POLY_H_
#define _Z3_POLY_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /**
       \brief Create a new polynomial manager.

       def_API('Z3_mk_polynomial_manager', POLYNOMIAL_MANAGER, (_in(CONTEXT),))
    */
    Z3_polynomial_manager Z3_API Z3_mk_polynomial_manager(__in Z3_context c);
    
    /**
       \brief Delete the given polynomial manager.
       
       def_API('Z3_del_polynomial_manager', VOID, (_in(CONTEXT), _in(POLYNOMIAL_MANAGER)))
    */
    void Z3_API Z3_del_polynomial_manager(__in Z3_context c, __in Z3_polynomial_manager m);

    /**
       \brief Return the zero polynomial.

       def_API('Z3_mk_zero_polynomial', POLYNOMIAL, (_in(CONTEXT), _in(POLYNOMIAL_MANAGER)))
    */
    Z3_polynomial Z3_API Z3_mk_zero_polynomial(__in Z3_context c, __in Z3_polynomial_manager m);

    /**
       \brief Increment p's reference counter

       def_API('Z3_polynomial_inc_ref', VOID, (_in(CONTEXT), _in(POLYNOMIAL_MANAGER), _in(POLYNOMIAL)))
    */
    void Z3_API Z3_polynomial_inc_ref(__in Z3_context c, __in Z3_polynomial_manager m, __in Z3_polynomial p);

    /**
       \brief Decrement p's reference counter.

       def_API('Z3_polynomial_dec_ref', VOID, (_in(CONTEXT), _in(POLYNOMIAL_MANAGER), _in(POLYNOMIAL)))
    */
    void Z3_API Z3_polynomial_dec_ref(__in Z3_context c, __in Z3_polynomial_manager m, __in Z3_polynomial p);
    
    /**
       \brief Convert the given polynomial into a string.

       def_API('Z3_polynomial_to_string', STRING, (_in(CONTEXT), _in(POLYNOMIAL_MANAGER), _in(POLYNOMIAL)))
    */
    Z3_string Z3_API Z3_polynomial_to_string(__in Z3_context c, __in Z3_polynomial_manager m, __in Z3_polynomial p);

#ifdef __cplusplus
};
#endif // __cplusplus

#endif

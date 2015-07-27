/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_polynomial.h

Abstract:

    Additional APIs for polynomials.

Author:

    Leonardo de Moura (leonardo) 2012-12-09

Notes:
    
--*/

#ifndef Z3_POLYNOMIAL_H_
#define Z3_POLYNOMIAL_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /**
    \defgroup capi C API

    */

    /*@{*/


    /**
    @name Polynomials API
    */
    /*@{*/

    /**
       \brief Return the nonzero subresultants of \c p and \c q with respect to the "variable" \c x.
       
       \pre \c p, \c q and \c x are Z3 expressions where \c p and \c q are arithmetic terms.
       Note that, any subterm that cannot be viewed as a polynomial is assumed to be a variable.
       Example: f(a) is a considered to be a variable in the polynomial   
                  
       f(a)*f(a) + 2*f(a) + 1 

       def_API('Z3_polynomial_subresultants', AST_VECTOR, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
    */
    Z3_ast_vector Z3_API Z3_polynomial_subresultants(Z3_context c, Z3_ast p, Z3_ast q, Z3_ast x);


    /*@}*/
    /*@}*/

#ifdef __cplusplus
};
#endif // __cplusplus

#endif

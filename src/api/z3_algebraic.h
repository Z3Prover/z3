/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_algebraic.h

Abstract:

    Additional APIs for handling Z3 algebraic numbers encoded as 
    Z3_ASTs

Author:

    Leonardo de Moura (leonardo) 2012-12-07

Notes:
    
--*/

#ifndef Z3_ALGEBRAIC_H_
#define Z3_ALGEBRAIC_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus    

    /**
    \defgroup capi C API

    */

    /*@{*/

    /**
    @name Algebraic Numbers API
    */
    /*@{*/

    /**
       \brief Return Z3_TRUE if \c can be used as value in the Z3 real algebraic
       number package.

       def_API('Z3_algebraic_is_value', BOOL, (_in(CONTEXT), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_is_value(Z3_context c, Z3_ast a);

    /**
       \brief Return the Z3_TRUE if \c a is positive, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)

       def_API('Z3_algebraic_is_pos', BOOL, (_in(CONTEXT), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_is_pos(Z3_context c, Z3_ast a);

    /**
       \brief Return the Z3_TRUE if \c a is negative, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)

       def_API('Z3_algebraic_is_neg', BOOL, (_in(CONTEXT), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_is_neg(Z3_context c, Z3_ast a);

    /**
       \brief Return the Z3_TRUE if \c a is zero, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)

       def_API('Z3_algebraic_is_zero', BOOL, (_in(CONTEXT), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_is_zero(Z3_context c, Z3_ast a);

    /**
       \brief Return 1 if \c a is positive, 0 if \c a is zero, and -1 if \c a is negative.

       \pre Z3_algebraic_is_value(c, a)

       def_API('Z3_algebraic_sign', INT, (_in(CONTEXT), _in(AST)))
    */
    int Z3_API Z3_algebraic_sign(Z3_context c, Z3_ast a);

    /**
       \brief Return the value a + b. 

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)
       \post Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_add', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_algebraic_add(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Return the value a - b. 

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)
       \post Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_sub', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_algebraic_sub(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Return the value a * b. 

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)
       \post Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_mul', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_algebraic_mul(Z3_context c, Z3_ast a, Z3_ast b);    
    
    /**
       \brief Return the value a / b. 

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)
       \pre !Z3_algebraic_is_zero(c, b)
       \post Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_div', AST, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_algebraic_div(Z3_context c, Z3_ast a, Z3_ast b);    
    
    /**
       \brief Return the a^(1/k)

       \pre Z3_algebraic_is_value(c, a)
       \pre k is even => !Z3_algebraic_is_neg(c, a)
       \post Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_root', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_algebraic_root(Z3_context c, Z3_ast a, unsigned k);

    /**
       \brief Return the a^k

       \pre Z3_algebraic_is_value(c, a)
       \post Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_power', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
    */
    Z3_ast Z3_API Z3_algebraic_power(Z3_context c, Z3_ast a, unsigned k);
    
    /**
       \brief Return Z3_TRUE if a < b, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)

       def_API('Z3_algebraic_lt', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_lt(Z3_context c, Z3_ast a, Z3_ast b);    
    
    /**
       \brief Return Z3_TRUE if a > b, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)

       def_API('Z3_algebraic_gt', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_gt(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Return Z3_TRUE if a <= b, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)

       def_API('Z3_algebraic_le', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_le(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Return Z3_TRUE if a >= b, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)

       def_API('Z3_algebraic_ge', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_ge(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Return Z3_TRUE if a == b, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)

       def_API('Z3_algebraic_eq', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_eq(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Return Z3_TRUE if a != b, and Z3_FALSE otherwise.

       \pre Z3_algebraic_is_value(c, a)
       \pre Z3_algebraic_is_value(c, b)

       def_API('Z3_algebraic_neq', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
    */
    Z3_bool Z3_API Z3_algebraic_neq(Z3_context c, Z3_ast a, Z3_ast b);    

    /**
       \brief Given a multivariate polynomial p(x_0, ..., x_{n-1}, x_n), returns the 
       roots of the univariate polynomial p(a[0], ..., a[n-1], x_n).
       
       \pre p is a Z3 expression that contains only arithmetic terms and free variables.
       \pre forall i in [0, n) Z3_algebraic_is_value(c, a[i])
       \post forall r in result Z3_algebraic_is_value(c, result)

       def_API('Z3_algebraic_roots', AST_VECTOR, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))
    */
    Z3_ast_vector Z3_API Z3_algebraic_roots(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]);    

    /**
       \brief Given a multivariate polynomial p(x_0, ..., x_{n-1}), return the 
       sign of p(a[0], ..., a[n-1]).
       
       \pre p is a Z3 expression that contains only arithmetic terms and free variables.
       \pre forall i in [0, n) Z3_algebraic_is_value(c, a[i])

       def_API('Z3_algebraic_eval', INT, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))
    */
    int Z3_API Z3_algebraic_eval(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]);    

    /*@}*/
    /*@}*/

#ifdef __cplusplus
}
#endif // __cplusplus

#endif

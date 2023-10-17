/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    z3_rcf.h

Abstract:

    Additional APIs for handling elements of the Z3 real closed field that contains:
       - transcendental extensions
       - infinitesimal extensions
       - algebraic extensions

Author:

    Leonardo de Moura (leonardo) 2012-01-05

Notes:

--*/
#pragma once

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /**@{*/

    /** @name Real Closed Fields */
    /**@{*/
    /**
       \brief Delete a RCF numeral created using the RCF API.

       def_API('Z3_rcf_del', VOID, (_in(CONTEXT), _in(RCF_NUM)))
    */
    void Z3_API Z3_rcf_del(Z3_context c, Z3_rcf_num a);

    /**
       \brief Return a RCF rational using the given string.

       def_API('Z3_rcf_mk_rational', RCF_NUM, (_in(CONTEXT), _in(STRING)))
    */
    Z3_rcf_num Z3_API Z3_rcf_mk_rational(Z3_context c, Z3_string val);

    /**
       \brief Return a RCF small integer.

       def_API('Z3_rcf_mk_small_int', RCF_NUM, (_in(CONTEXT), _in(INT)))
    */
    Z3_rcf_num Z3_API Z3_rcf_mk_small_int(Z3_context c, int val);

    /**
       \brief Return Pi

       def_API('Z3_rcf_mk_pi', RCF_NUM, (_in(CONTEXT),))
    */
    Z3_rcf_num Z3_API Z3_rcf_mk_pi(Z3_context c);

    /**
       \brief Return e (Euler's constant)

       def_API('Z3_rcf_mk_e', RCF_NUM, (_in(CONTEXT),))
    */
    Z3_rcf_num Z3_API Z3_rcf_mk_e(Z3_context c);

    /**
       \brief Return a new infinitesimal that is smaller than all elements in the Z3 field.

       def_API('Z3_rcf_mk_infinitesimal', RCF_NUM, (_in(CONTEXT),))
    */
    Z3_rcf_num Z3_API Z3_rcf_mk_infinitesimal(Z3_context c);

    /**
       \brief Store in roots the roots of the polynomial \ccode{a[n-1]*x^{n-1} + ... + a[0]}.
       The output vector \c roots must have size \c n.
       It returns the number of roots of the polynomial.

       \pre The input polynomial is not the zero polynomial.

       def_API('Z3_rcf_mk_roots', UINT, (_in(CONTEXT), _in(UINT), _in_array(1, RCF_NUM), _out_array(1, RCF_NUM)))
    */
    unsigned Z3_API Z3_rcf_mk_roots(Z3_context c, unsigned n, Z3_rcf_num const a[], Z3_rcf_num roots[]);

    /**
       \brief Return the value \ccode{a + b}.

       def_API('Z3_rcf_add', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    Z3_rcf_num Z3_API Z3_rcf_add(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return the value \ccode{a - b}.

       def_API('Z3_rcf_sub', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    Z3_rcf_num Z3_API Z3_rcf_sub(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return the value \ccode{a * b}.

       def_API('Z3_rcf_mul', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    Z3_rcf_num Z3_API Z3_rcf_mul(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return the value \ccode{a / b}.

       def_API('Z3_rcf_div', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    Z3_rcf_num Z3_API Z3_rcf_div(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return the value \ccode{-a}.

       def_API('Z3_rcf_neg', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM)))
    */
    Z3_rcf_num Z3_API Z3_rcf_neg(Z3_context c, Z3_rcf_num a);

    /**
       \brief Return the value \ccode{1/a}.

       def_API('Z3_rcf_inv', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM)))
    */
    Z3_rcf_num Z3_API Z3_rcf_inv(Z3_context c, Z3_rcf_num a);

    /**
       \brief Return the value \ccode{a^k}.

       def_API('Z3_rcf_power', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(UINT)))
    */
    Z3_rcf_num Z3_API Z3_rcf_power(Z3_context c, Z3_rcf_num a, unsigned k);

    /**
       \brief Return \c true if \ccode{a < b}.

       def_API('Z3_rcf_lt', BOOL, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    bool Z3_API Z3_rcf_lt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return \c true if \ccode{a > b}.

       def_API('Z3_rcf_gt', BOOL, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    bool Z3_API Z3_rcf_gt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return \c true if \ccode{a <= b}.

       def_API('Z3_rcf_le', BOOL, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    bool Z3_API Z3_rcf_le(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return \c true if \ccode{a >= b}.

       def_API('Z3_rcf_ge', BOOL, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    bool Z3_API Z3_rcf_ge(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return \c true if \ccode{a == b}.

       def_API('Z3_rcf_eq', BOOL, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    bool Z3_API Z3_rcf_eq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Return \c true if \ccode{a != b}.

       def_API('Z3_rcf_neq', BOOL, (_in(CONTEXT), _in(RCF_NUM), _in(RCF_NUM)))
    */
    bool Z3_API Z3_rcf_neq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);

    /**
       \brief Convert the RCF numeral into a string.

       def_API('Z3_rcf_num_to_string', STRING, (_in(CONTEXT), _in(RCF_NUM), _in(BOOL), _in(BOOL)))
    */
    Z3_string Z3_API Z3_rcf_num_to_string(Z3_context c, Z3_rcf_num a, bool compact, bool html);

    /**
       \brief Convert the RCF numeral into a string in decimal notation.

       def_API('Z3_rcf_num_to_decimal_string', STRING, (_in(CONTEXT), _in(RCF_NUM), _in(UINT)))
    */
    Z3_string Z3_API Z3_rcf_num_to_decimal_string(Z3_context c, Z3_rcf_num a, unsigned prec);

    /**
       \brief Extract the "numerator" and "denominator" of the given RCF numeral.
       We have that \ccode{a = n/d}, moreover \c n and \c d are not represented using rational functions.

       def_API('Z3_rcf_get_numerator_denominator', VOID, (_in(CONTEXT), _in(RCF_NUM), _out(RCF_NUM), _out(RCF_NUM)))
   */
   void Z3_API Z3_rcf_get_numerator_denominator(Z3_context c, Z3_rcf_num a, Z3_rcf_num * n, Z3_rcf_num * d);

   /**
       \brief Return \c true if \c a represents a rational number.

       def_API('Z3_rcf_is_rational', BOOL, (_in(CONTEXT), _in(RCF_NUM)))
   */
   bool Z3_API Z3_rcf_is_rational(Z3_context c, Z3_rcf_num a);

   /**
       \brief Return \c true if \c a represents an algebraic number.

       def_API('Z3_rcf_is_algebraic', BOOL, (_in(CONTEXT), _in(RCF_NUM)))
   */
   bool Z3_API Z3_rcf_is_algebraic(Z3_context c, Z3_rcf_num a);

   /**
       \brief Return \c true if \c a represents an infinitesimal.

       def_API('Z3_rcf_is_infinitesimal', BOOL, (_in(CONTEXT), _in(RCF_NUM)))
   */
   bool Z3_API Z3_rcf_is_infinitesimal(Z3_context c, Z3_rcf_num a);

   /**
       \brief Return \c true if \c a represents a transcendental number.

       def_API('Z3_rcf_is_transcendental', BOOL, (_in(CONTEXT), _in(RCF_NUM)))
   */
   bool Z3_API Z3_rcf_is_transcendental(Z3_context c, Z3_rcf_num a);

   /**
       \brief Return the index of a field extension.

      def_API('Z3_rcf_extension_index', UINT, (_in(CONTEXT), _in(RCF_NUM)))
   */
   unsigned Z3_API Z3_rcf_extension_index(Z3_context c, Z3_rcf_num a);

   /**
       \brief Return the name of a transcendental.

       \pre Z3_rcf_is_transcendtal(ctx, a);

       def_API('Z3_rcf_transcendental_name', SYMBOL, (_in(CONTEXT), _in(RCF_NUM)))
   */
   Z3_symbol Z3_API Z3_rcf_transcendental_name(Z3_context c, Z3_rcf_num a);

    /**
       \brief Return the name of an infinitesimal.

       \pre Z3_rcf_is_infinitesimal(ctx, a);

       def_API('Z3_rcf_infinitesimal_name', SYMBOL, (_in(CONTEXT), _in(RCF_NUM)))
   */
   Z3_symbol Z3_API Z3_rcf_infinitesimal_name(Z3_context c, Z3_rcf_num a);

   /**
       \brief Return the number of coefficients in an algebraic number.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_num_coefficients', UINT, (_in(CONTEXT), _in(RCF_NUM)))
   */
   unsigned Z3_API Z3_rcf_num_coefficients(Z3_context c, Z3_rcf_num a);

   /**
       \brief Extract a coefficient from an algebraic number.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_coefficient', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(UINT)))
   */
   Z3_rcf_num Z3_API Z3_rcf_coefficient(Z3_context c, Z3_rcf_num a, unsigned i);

   /**
       \brief Extract an interval from an algebraic number.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_interval', INT, (_in(CONTEXT), _in(RCF_NUM), _out(INT), _out(INT), _out(RCF_NUM), _out(INT), _out(INT), _out(RCF_NUM)))
   */
   int Z3_API Z3_rcf_interval(Z3_context c, Z3_rcf_num a, int * lower_is_inf, int * lower_is_open, Z3_rcf_num * lower, int * upper_is_inf, int * upper_is_open, Z3_rcf_num * upper);

   /**
       \brief Return the number of sign conditions of an algebraic number.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_num_sign_conditions', UINT, (_in(CONTEXT), _in(RCF_NUM)))
   */
   unsigned Z3_API Z3_rcf_num_sign_conditions(Z3_context c, Z3_rcf_num a);

   /**
       \brief Extract the sign of a sign condition from an algebraic number.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_sign_condition_sign', INT, (_in(CONTEXT), _in(RCF_NUM), _in(UINT)))
   */
   int Z3_API Z3_rcf_sign_condition_sign(Z3_context c, Z3_rcf_num a, unsigned i);

   /**
       \brief Return the number of sign condition polynomial coefficients of an algebraic number.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_num_sign_condition_coefficients', UINT, (_in(CONTEXT), _in(RCF_NUM), _in(UINT)))
   */
   unsigned Z3_API Z3_rcf_num_sign_condition_coefficients(Z3_context c, Z3_rcf_num a, unsigned i);

   /**
       \brief Extract the j-th polynomial coefficient of the i-th sign condition.

       \pre Z3_rcf_is_algebraic(ctx, a);

       def_API('Z3_rcf_sign_condition_coefficient', RCF_NUM, (_in(CONTEXT), _in(RCF_NUM), _in(UINT), _in(UINT)))
   */
   Z3_rcf_num Z3_API Z3_rcf_sign_condition_coefficient(Z3_context c, Z3_rcf_num a, unsigned i, unsigned j);

    /**@}*/
    /**@}*/

#ifdef __cplusplus
}
#endif // __cplusplus


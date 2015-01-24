/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    z3_fpa.h

Abstract:

    Additional APIs for floating-point arithmetic (FP).

Author:

    Christoph M. Wintersteiger (cwinter) 2013-06-05

Notes:
    
--*/
#ifndef _Z3_FPA_H_
#define _Z3_FPA_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /**
    \defgroup capi C API

    */

    /*@{*/

    /**
        @name Floating-Point API
        */
    /*@{*/

    /**
        \brief Create the RoundingMode sort.

        \param c logical context
     
        def_API('Z3_mk_fpa_rounding_mode_sort', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_rounding_mode_sort(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode.

        \param c logical context
     
        def_API('Z3_mk_fpa_round_nearest_ties_to_even', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_even(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the NearestTiesToEven rounding mode.

        \param c logical context

        def_API('Z3_mk_fpa_rne', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_rne(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode.

        \param c logical context
     
        def_API('Z3_mk_fpa_round_nearest_ties_to_away', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_away(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the NearestTiesToAway rounding mode.

        \param c logical context

        def_API('Z3_mk_fpa_rna', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_rna(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the TowardPositive rounding mode.

        \param c logical context
     
        def_API('Z3_mk_fpa_round_toward_positive', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_positive(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the TowardPositive rounding mode.

        \param c logical context

        def_API('Z3_mk_fpa_rtp', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_rtp(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the TowardNegative rounding mode.
     
        \param c logical context

        def_API('Z3_mk_fpa_round_toward_negative', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_negative(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the TowardNegative rounding mode.

        \param c logical context

        def_API('Z3_mk_fpa_rtn', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_rtn(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the TowardZero rounding mode.

        \param c logical context
     
        def_API('Z3_mk_fpa_round_toward_zero', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_zero(__in Z3_context c);

    /**
        \brief Create a numeral of RoundingMode sort which represents the TowardZero rounding mode.

        \param c logical context

        def_API('Z3_mk_fpa_rtz', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_rtz(__in Z3_context c);

    /**
        \brief Create a FloatingPoint sort.

        \param c logical context
        \param ebits number of exponent bits
        \param sbits number of significand bits

        \remark ebits must be larger than 1 and sbits must be larger than 2.
     
        def_API('Z3_mk_fpa_sort', SORT, (_in(CONTEXT), _in(UINT), _in(UINT)))        
    */
    Z3_sort Z3_API Z3_mk_fpa_sort(__in Z3_context c, __in unsigned ebits, __in unsigned sbits);

    /**
        \brief Create the half-precision (16-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_half', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_half(__in Z3_context c);

    /**
        \brief Create the half-precision (16-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_16', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_16(__in Z3_context c);

    /**
        \brief Create the single-precision (32-bit) FloatingPoint sort.

        \param c logical context.       

        def_API('Z3_mk_fpa_sort_single', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_single(__in Z3_context c);

    /**
        \brief Create the single-precision (32-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_32', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_32(__in Z3_context c);

    /**
        \brief Create the double-precision (64-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_double', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_double(__in Z3_context c);

    /**
        \brief Create the double-precision (64-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_64', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_64(__in Z3_context c);

    /**
        \brief Create the quadruple-precision (128-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_quadruple', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_quadruple(__in Z3_context c);

    /**
        \brief Create the quadruple-precision (128-bit) FloatingPoint sort.

        \param c logical context

        def_API('Z3_mk_fpa_sort_128', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_128(__in Z3_context c);

    /**
        \brief Create a floating-point NaN of sort s.

        \param c logical context
        \param s target sort 
     
        def_API('Z3_mk_fpa_nan', AST, (_in(CONTEXT),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_nan(__in Z3_context c, __in Z3_sort s);

    /**
        \brief Create a floating-point infinity of sort s.

        \param c logical context
        \param s target sort 
        \param negative indicates whether the result should be negative
     
        When \c negative is true, -oo will be generated instead of +oo.

        def_API('Z3_mk_fpa_inf', AST, (_in(CONTEXT),_in(SORT),_in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_fpa_inf(__in Z3_context c, __in Z3_sort s, __in Z3_bool negative);

    /**
        \brief Create a floating-point zero of sort s.

        \param c logical context
        \param s target sort
        \param negative indicates whether the result should be negative

        When \c negative is true, -zero will be generated instead of +zero.

        def_API('Z3_mk_fpa_zero', AST, (_in(CONTEXT),_in(SORT),_in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_fpa_zero(__in Z3_context c, __in Z3_sort s, __in Z3_bool negative);

    /**
        \brief Create an expression of FloatingPoint sort from three bit-vector expressions.

	This is the operator named `fp' in the SMT FP theory definition.
        Note that \c sign is required to be a bit-vector of size 1. Significand and exponent 
        are required to be greater than 1 and 2 respectively. The FloatingPoint sort 
        of the resulting expression is automatically determined from the bit-vector sizes
        of the arguments.

        \param c logical context
        \param sgn sign         
        \param exp exponent
        \param sig significand

        def_API('Z3_mk_fpa_fp', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_fp(__in Z3_context c, __in Z3_ast sgn, __in Z3_ast exp, __in Z3_ast sig);

    /**
        \brief Create a numeral of FloatingPoint sort from a float.

        This function is used to create numerals that fit in a float value.
        It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

        \param c logical context
        \param v value
        \param ty sort

        ty must be a FloatingPoint sort

        \sa Z3_mk_numeral

        def_API('Z3_mk_fpa_numeral_float', AST, (_in(CONTEXT), _in(FLOAT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_numeral_float(__in Z3_context c, __in float v, __in Z3_sort ty);

    /**
        \brief Create a numeral of FloatingPoint sort from a double. 
       
        This function is used to create numerals that fit in a double value.
        It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

        \param c logical context
        \param v value
        \param ty sort

        ty must be a FloatingPoint sort

        \sa Z3_mk_numeral

        def_API('Z3_mk_fpa_numeral_double', AST, (_in(CONTEXT), _in(DOUBLE), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_numeral_double(__in Z3_context c, __in double v, __in Z3_sort ty);

    /**
        \brief Create a numeral of FloatingPoint sort from a signed integer.

        \param c logical context
        \param v value
        \param ty result sort

        ty must be a FloatingPoint sort

        \sa Z3_mk_numeral

        def_API('Z3_mk_fpa_numeral_int', AST, (_in(CONTEXT), _in(INT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_numeral_int(__in Z3_context c, __in signed v, Z3_sort ty);

    /**
        \brief Create a numeral of FloatingPoint sort from a sign bit and two integers.

        \param c logical context
        \param sgn sign bit (true == negative)
        \param sig significand
        \param exp exponent
        \param ty result sort

        ty must be a FloatingPoint sort

        \sa Z3_mk_numeral

        def_API('Z3_mk_fpa_numeral_int_uint', AST, (_in(CONTEXT), _in(BOOL), _in(INT), _in(UINT), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_numeral_int_uint(__in Z3_context c, __in Z3_bool sgn, __in signed exp, __in unsigned sig, Z3_sort ty);

    /**
        \brief Create a numeral of FloatingPoint sort from a sign bit and two 64-bit integers.

        \param c logical context
        \param sgn sign bit (true == negative)
        \param sig significand
        \param exp exponent
        \param ty result sort

        ty must be a FloatingPoint sort

        \sa Z3_mk_numeral

        def_API('Z3_mk_fpa_numeral_int64_uint64', AST, (_in(CONTEXT), _in(BOOL), _in(INT64), _in(UINT64), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_numeral_int64_uint64(__in Z3_context c, __in Z3_bool sgn, __in __int64 exp, __in __uint64 sig, Z3_sort ty);

    /**
        \brief Floating-point absolute value

        \param c logical context
        \param t term of FloatingPoint sort
     
        def_API('Z3_mk_fpa_abs', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_abs(__in Z3_context c, __in Z3_ast t);
   
    /**
        \brief Floating-point negation

        \param c logical context
        \param t term of FloatingPoint sort
     
        def_API('Z3_mk_fpa_neg', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_neg(__in Z3_context c, __in Z3_ast t);
   
    /**
        \brief Floating-point addition

        \param c logical context
        \param rm term of RoundingMode sort
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        rm must be of RoundingMode sort, t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_add', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_add(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Floating-point subtraction

        \param c logical context
        \param rm term of RoundingMode sort
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        rm must be of RoundingMode sort, t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_sub', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_sub(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point multiplication

        \param c logical context
        \param rm term of RoundingMode sort
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        rm must be of RoundingMode sort, t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_mul', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_mul(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point division

        \param c logical context
        \param rm term of RoundingMode sort
        \param t1 term of FloatingPoint sort.
        \param t2 term of FloatingPoint sort

        The nodes rm must be of RoundingMode sort t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_div', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_div(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);    
   
    /**
        \brief Floating-point fused multiply-add.

        \param c logical context
        \param rm term of RoundingMode sort
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sor
        \param t3 term of FloatingPoint sort

        The result is round((t1 * t2) + t3)

        rm must be of RoundingMode sort, t1, t2, and t3 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_fma', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_fma(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2, __in Z3_ast t3);
   
    /**
        \brief Floating-point square root

        \param c logical context
        \param rm term of RoundingMode sort
        \param t term of FloatingPoint sort

        rm must be of RoundingMode sort, t must have FloatingPoint sort.
     
        def_API('Z3_mk_fpa_sqrt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_sqrt(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t);
   
    /**
        \brief Floating-point remainder

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_rem', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_rem(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Floating-point roundToIntegral. Rounds a floating-point number to 
        the closest integer, again represented as a floating-point number.

        \param c logical context
        \param rm term of RoundingMode sort
        \param t term of FloatingPoint sort

        t must be of FloatingPoint sort.

        def_API('Z3_mk_fpa_round_to_integral', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_to_integral(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t);

    /**
        \brief Minimum of floating-point numbers.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1, t2 must have the same FloatingPoint sort.

        def_API('Z3_mk_fpa_min', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_min(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Maximum of floating-point numbers.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1, t2 must have the same FloatingPoint sort.

        def_API('Z3_mk_fpa_max', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_max(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
     /**
        \brief Floating-point less than or equal.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_leq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_leq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

     /**
        \brief Floating-point less than.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_lt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_lt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
        
    /**
        \brief Floating-point greater than or equal.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_geq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_geq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Floating-point greater than.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        t1 and t2 must have the same FloatingPoint sort.
     
        def_API('Z3_mk_fpa_gt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_gt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Floating-point equality.

        \param c logical context
        \param t1 term of FloatingPoint sort
        \param t2 term of FloatingPoint sort

        Note that this is IEEE 754 equality (as opposed to SMT-LIB =).

        t1 and t2 must have the same FloatingPoint sort.

        def_API('Z3_mk_fpa_eq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_eq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Predicate indicating whether t is a normal floating-point number.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.
     
        def_API('Z3_mk_fpa_is_normal', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_normal(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a subnormal floating-point number.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.
     
        def_API('Z3_mk_fpa_is_subnormal', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_subnormal(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a floating-point number with zero value, i.e., +zero or -zero.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.
     
        def_API('Z3_mk_fpa_is_zero', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_zero(__in Z3_context c, __in Z3_ast t);

   /**
        \brief Predicate indicating whether t is a floating-point number representing +oo or -oo.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.
     
        def_API('Z3_mk_fpa_is_infinite', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_infinite(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a NaN.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.
     
        def_API('Z3_mk_fpa_is_nan', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_nan(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a negative floating-point number.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.

        def_API('Z3_mk_fpa_is_negative', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_is_negative(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a positive floating-point number.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort.

        def_API('Z3_mk_fpa_is_positive', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_is_positive(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Conversion of a single IEEE 754-2008 bit-vector into a floating-point number.

        Produces a term that represents the conversion of a bit-vector term bv to a 
        floating-point term of sort s.

        \param c logical context
        \param bv a bit-vector term
        \param s floating-point sort

        s must be a FloatingPoint sort, t must be of bit-vector sort, and the bit-vector 
        size of bv must be equal to ebits+sbits of s. The format of the bit-vector is 
        as defined by the IEEE 754-2008 interchange format.
     
        def_API('Z3_mk_fpa_to_fp_bv', AST, (_in(CONTEXT),_in(AST),_in(SORT)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_to_fp_bv(__in Z3_context c, __in Z3_ast bv, __in Z3_sort s);

    /**
        \brief Conversion of a FloatingPoint term into another term of different FloatingPoint sort.
        
        Produces a term that represents the conversion of a floating-point term t to a
        floating-point term of sort s. If necessary, the result will be rounded according
        to rounding mode rm.

        \param c logical context    
        \param rm term of RoundingMode sort
        \param t term of FloatingPoint sort
        \param s floating-point sort

        s must be a FloatingPoint sort, rm must be of RoundingMode sort, t must be of floating-point sort.

        def_API('Z3_mk_fpa_to_fp_float', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_fp_float(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t, __in Z3_sort s);

    /**
        \brief Conversion of a term of real sort into a term of FloatingPoint sort.

        Produces a term that represents the conversion of term t of real sort into a
        floating-point term of sort s. If necessary, the result will be rounded according
        to rounding mode rm.

        \param c logical context    
        \param rm term of RoundingMode sort
        \param t term of Real sort
        \param s floating-point sort

        s must be a FloatingPoint sort, rm must be of RoundingMode sort, t must be of real sort.

        def_API('Z3_mk_fpa_to_fp_real', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_fp_real(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t, __in Z3_sort s);

    /**
        \brief Conversion of a 2's complement signed bit-vector term into a term of FloatingPoint sort.

        Produces a term that represents the conversion of the bit-vector term t into a
        floating-point term of sort s. The bit-vector t is taken to be in signed 
        2's complement format. If necessary, the result will be rounded according
        to rounding mode rm.

        \param c logical context
        \param rm term of RoundingMode sort
        \param t term of bit-vector sort
        \param s floating-point sort

        s must be a FloatingPoint sort, rm must be of RoundingMode sort, t must be of bit-vector sort.

        def_API('Z3_mk_fpa_to_fp_signed', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_fp_signed(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t, __in Z3_sort s);

    /**
        \brief Conversion of a 2's complement unsigned bit-vector term into a term of FloatingPoint sort.

        Produces a term that represents the conversion of the bit-vector term t into a
        floating-point term of sort s. The bit-vector t is taken to be in unsigned
        2's complement format. If necessary, the result will be rounded according
        to rounding mode rm.

        \param c logical context
        \param rm term of RoundingMode sort
        \param t term of bit-vector sort
        \param s floating-point sort

        s must be a FloatingPoint sort, rm must be of RoundingMode sort, t must be of bit-vector sort.

        def_API('Z3_mk_fpa_to_fp_unsigned', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_fp_unsigned(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t, __in Z3_sort s);

    /**
        \brief Conversion of a floating-point term into an unsigned bit-vector.

        Produces a term that represents the conversion of the floating-poiunt term t into a
        bit-vector term of size sz in unsigned 2's complement format. If necessary, the result 
		will be rounded according to rounding mode rm.

        \param c logical context
        \param rm term of RoundingMode sort
        \param t term of FloatingPoint sort
        \param sz size of the resulting bit-vector

        def_API('Z3_mk_fpa_to_ubv', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(UINT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_ubv(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t, __in unsigned sz);

    /**
        \brief Conversion of a floating-point term into a signed bit-vector.

        Produces a term that represents the conversion of the floating-poiunt term t into a
        bit-vector term of size sz in signed 2's complement format. If necessary, the result 
		will be rounded according to rounding mode rm.

        \param c logical context
        \param rm term of RoundingMode sort
        \param t term of FloatingPoint sort
        \param sz size of the resulting bit-vector

        def_API('Z3_mk_fpa_to_sbv', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(UINT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_sbv(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t, __in unsigned sz);

    /**
        \brief Conversion of a floating-point term into a real-numbered term.

        Produces a term that represents the conversion of the floating-poiunt term t into a
        real number. Note that this type of conversion will often result in non-linear 
        constraints over real terms.

        \param c logical context        
        \param t term of FloatingPoint sort

        def_API('Z3_mk_fpa_to_real', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_real(__in Z3_context c, __in Z3_ast t);


    /**
        @name Z3-specific floating-point extensions
    */
    /*@{*/

    /**
        \brief Retrieves the number of bits reserved for the exponent in a FloatingPoint sort.

		\param c logical context
        \param s FloatingPoint sort

        def_API('Z3_fpa_get_ebits', UINT, (_in(CONTEXT),_in(SORT)))
    */
    unsigned Z3_API Z3_fpa_get_ebits(__in Z3_context c, __in Z3_sort s);

    /**
        \brief Retrieves the number of bits reserved for the significand in a FloatingPoint sort.

		\param c logical context
        \param s FloatingPoint sort

        def_API('Z3_fpa_get_sbits', UINT, (_in(CONTEXT),_in(SORT)))
    */
    unsigned Z3_API Z3_fpa_get_sbits(__in Z3_context c, __in Z3_sort s);

    /**
        \brief Retrieves the sign of a floating-point literal.

		\param c logical context
        \param t a floating-point numeral
		\param sgn sign

        Remarks: sets \c sgn to 0 if the literal is NaN or positive and to 1 otherwise.

        def_API('Z3_fpa_get_numeral_sign', BOOL, (_in(CONTEXT), _in(AST), _out(INT)))
    */
    Z3_bool Z3_API Z3_fpa_get_numeral_sign(__in Z3_context c, __in Z3_ast t, __out int * sgn);

    /**
        \brief Return the significand value of a floating-point numeral as a string.

		\param c logical context
        \param t a floating-point numeral

        Remarks: The significand s is always 0 < s < 2.0; the resulting string is long
        enough to represent the real significand precisely.

        def_API('Z3_fpa_get_numeral_significand_string', STRING, (_in(CONTEXT), _in(AST)))
    */
    Z3_string Z3_API Z3_fpa_get_numeral_significand_string(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Return the exponent value of a floating-point numeral as a string

		\param c logical context
        \param t a floating-point numeral

        def_API('Z3_fpa_get_numeral_exponent_string', STRING, (_in(CONTEXT), _in(AST)))
    */
    Z3_string Z3_API Z3_fpa_get_numeral_exponent_string(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Return the exponent value of a floating-point numeral as a signed 64-bit integer

        \param c logical context
        \param t a floating-point numeral
		\param n exponent

        def_API('Z3_fpa_get_numeral_exponent_int64', BOOL, (_in(CONTEXT), _in(AST), _out(INT64)))
    */
    Z3_bool Z3_API Z3_fpa_get_numeral_exponent_int64(__in Z3_context c, __in Z3_ast t, __out __int64 * n);

    /**
        \brief Conversion of a floating-point term into a bit-vector term in IEEE 754-2008 format.

        \param c logical context
        \param t term of FloatingPoint sort

        t must have FloatingPoint sort. The size of the resulting bit-vector is automatically 
        determined. 
        
        Note that IEEE 754-2008 allows multiple different representations of NaN. This conversion 
        knows only one NaN and it will always produce the same bit-vector represenatation of 
        that NaN. 

        def_API('Z3_mk_fpa_to_ieee_bv', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_ieee_bv(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Conversion of a real-sorted significand and an integer-sorted exponent into a term of FloatingPoint sort.

        Produces a term that represents the conversion of sig * 2^exp into a 
        floating-point term of sort s. If necessary, the result will be rounded
        according to rounding mode rm.

        \param c logical context     
        \param rm term of RoundingMode sort
        \param exp exponent term of Int sort
        \param sig significand term of Real sort        
        \param s FloatingPoint sort

        s must be a FloatingPoint sort, rm must be of RoundingMode sort, exp must be of int sort, sig must be of real sort.

        def_API('Z3_mk_fpa_to_fp_int_real', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_fp_int_real(__in Z3_context c, __in Z3_ast rm, __in Z3_ast exp, __in Z3_ast sig, __in Z3_sort s);

    /*@}*/

    /*@}*/
    /*@}*/

#ifdef __cplusplus
};
#endif // __cplusplus

#endif

/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    z3_fpa.h

Abstract:

    Additional APIs for floating-point arithmetic (FPA).

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
        \brief Create a rounding mode sort.

        \param c logical context.
     
        def_API('Z3_mk_fpa_rounding_mode_sort', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_rounding_mode_sort(__in Z3_context c);

    /**
        \brief Create a numeral of rounding mode sort which represents the NearestTiesToEven rounding mode.

        \param c logical context.
     
        def_API('Z3_mk_fpa_round_nearest_ties_to_even', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_even(__in Z3_context c);

    /**
        \brief Create a numeral of rounding mode sort which represents the NearestTiesToAway rounding mode.

        \param c logical context.
     
        def_API('Z3_mk_fpa_round_nearest_ties_to_away', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_away(__in Z3_context c);

    /**
        \brief Create a numeral of rounding mode sort which represents the TowardPositive rounding mode.

        \param c logical context.
     
        def_API('Z3_mk_fpa_round_toward_positive', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_positive(__in Z3_context c);    

    /**
        \brief Create a numeral of rounding mode sort which represents the TowardNegative rounding mode.
     
        \param c logical context.

        def_API('Z3_mk_fpa_round_toward_negative', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_negative(__in Z3_context c);    

    /**
        \brief Create a numeral of rounding mode sort which represents the TowardZero rounding mode.

        \param c logical context.
     
        def_API('Z3_mk_fpa_round_toward_zero', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_zero(__in Z3_context c);



    /**
        \brief Create a floating point sort.

        \param c logical context.
        \param ebits number of exponent bits
        \param sbits number of significand bits

        \remark ebits must be larger than 1 and sbits must be larger than 2.
     
        def_API('Z3_mk_fpa_sort', SORT, (_in(CONTEXT), _in(UINT), _in(UINT)))        
    */
    Z3_sort Z3_API Z3_mk_fpa_sort(__in Z3_context c, __in unsigned ebits, __in unsigned sbits);

    /**
        \brief Create the half-precision (16-bit) floating point sort.

        \param c logical context.
        \param ebits number of exponent bits
        \param sbits number of significand bits

        \remark ebits must be larger than 1 and sbits must be larger than 2.

        def_API('Z3_mk_fpa_sort_half', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_half(__in Z3_context c);

    /**
    \brief Create the half-precision (16-bit) floating point sort.

    \param c logical context.
    \param ebits number of exponent bits
    \param sbits number of significand bits

    \remark ebits must be larger than 1 and sbits must be larger than 2.

    def_API('Z3_mk_fpa_sort_16', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_16(__in Z3_context c);

    /**
        \brief Create the single-precision (32-bit) floating point sort.

        \param c logical context.
        \param ebits number of exponent bits
        \param sbits number of significand bits

        \remark ebits must be larger than 1 and sbits must be larger than 2.

        def_API('Z3_mk_fpa_sort_single', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_single(__in Z3_context c);

    /**
    \brief Create the single-precision (32-bit) floating point sort.

    \param c logical context.
    \param ebits number of exponent bits
    \param sbits number of significand bits

    \remark ebits must be larger than 1 and sbits must be larger than 2.

    def_API('Z3_mk_fpa_sort_32', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_32(__in Z3_context c);

    /**
        \brief Create the double-precision (64-bit) floating point sort.

        \param c logical context.
        \param ebits number of exponent bits
        \param sbits number of significand bits

        \remark ebits must be larger than 1 and sbits must be larger than 2.

        def_API('Z3_mk_fpa_sort_double', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_double(__in Z3_context c);

    /**
    \brief Create the double-precision (64-bit) floating point sort.

    \param c logical context.
    \param ebits number of exponent bits
    \param sbits number of significand bits

    \remark ebits must be larger than 1 and sbits must be larger than 2.

    def_API('Z3_mk_fpa_sort_64', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_64(__in Z3_context c);

    /**
        \brief Create the quadruple-precision (128-bit) floating point sort.

        \param c logical context.
        \param ebits number of exponent bits
        \param sbits number of significand bits

        \remark ebits must be larger than 1 and sbits must be larger than 2.

        def_API('Z3_mk_fpa_sort_quadruple', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_quadruple(__in Z3_context c);

    /**
    \brief Create the quadruple-precision (128-bit) floating point sort.

    \param c logical context.
    \param ebits number of exponent bits
    \param sbits number of significand bits

    \remark ebits must be larger than 1 and sbits must be larger than 2.

    def_API('Z3_mk_fpa_sort_128', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_sort_128(__in Z3_context c);

    /**
        \brief Create a NaN of sort s.

        \param c logical context.
        \param s target sort 
     
        def_API('Z3_mk_fpa_nan', AST, (_in(CONTEXT),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_nan(__in Z3_context c, __in Z3_sort s);

    /**
        \brief Create a floating point infinity of sort s.

        \param c logical context.
        \param s target sort 
        \param negative indicates whether the result should be negative
     
        When \c negative is true, -oo will be generated instead of +oo.

        def_API('Z3_mk_fpa_inf', AST, (_in(CONTEXT),_in(SORT),_in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_fpa_inf(__in Z3_context c, __in Z3_sort s, __in Z3_bool negative);

    /**
    \brief Create a floating point zero of sort s.

    \param c logical context.
    \param s target sort
    \param negative indicates whether the result should be negative

    When \c negative is true, -zero will be generated instead of +zero.

    def_API('Z3_mk_fpa_zero', AST, (_in(CONTEXT),_in(SORT),_in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_fpa_zero(__in Z3_context c, __in Z3_sort s, __in Z3_bool negative);

    /**
       \brief Create a numeral of floating point sort from a double. 
       
       This function can be use to create numerals that fit in a double value.
       It is slightly faster than #Z3_mk_numeral since it is not necessary to parse a string.

       \params c logical context.
       \params v value.
       \params ty sort.

       ty must be a floating point sort

       \sa Z3_mk_numeral

       def_API('Z3_mk_fpa_numeral_double', AST, (_in(CONTEXT), _in(DOUBLE), _in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_numeral_double(__in Z3_context c, __in double v, __in Z3_sort ty);

    /**
        \brief Floating-point absolute value

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_abs', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_abs(__in Z3_context c, __in Z3_ast t);
   
    /**
        \brief Floating-point negation

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_neg', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_neg(__in Z3_context c, __in Z3_ast t);
   
    /**
        \brief Floating-point addition

        \param c logical context.
        \param rm rounding mode
        \param t1 floating-point term.
        \param t2 floating-point term.

        rm must be of FPA rounding mode sort, t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_add', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_add(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Floating-point subtraction

        \param c logical context.
        \param rm rounding mode
        \param t1 floating-point term.
        \param t2 floating-point term.

        rm must be of FPA rounding mode sort, t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_sub', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_sub(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point multiplication

        \param c logical context.
        \param rm rounding mode
        \param t1 floating-point term.
        \param t2 floating-point term.

        rm must be of FPA rounding mode sort, t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_mul', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_mul(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point division

        \param c logical context.
        \param rm rounding mode
        \param t1 floating-point term.
        \param t2 floating-point term.

        The nodes rm must be of FPA rounding mode sort t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_div', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_div(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);    
   
    /**
        \brief Floating-point fused multiply-add.

        \param c logical context.
        \param rm rounding mode
        \param t1 floating-point term.
        \param t2 floating-point term.

        The result is round((t1 * t2) + t3)

        rm must be of FPA rounding mode sort, t1, t2, and t3 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_fma', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_fma(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2, __in Z3_ast t3);
   
    /**
        \brief Floating-point square root

        \param c logical context.
        \param rm rounding mode
        \param t floating-point term.

        rm must be of FPA rounding mode sort, t must have floating point sort.
     
        def_API('Z3_mk_fpa_sqrt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_sqrt(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t);
   
    /**
        \brief Floating-point remainder

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_rem', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_rem(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point equality

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        Note that this is IEEE 754 equality (as opposed to SMT-LIB =).

        t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_eq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_eq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
     /**
        \brief Floating-point less than or equal        

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_le', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_le(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

     /**
        \brief Floating-point less-than

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_lt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_lt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    
    /**
        \brief Floating-point greater than or equal

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_ge', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_ge(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Floating-point greater-than

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1 and t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_gt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_gt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Predicate indicating whether t is a normal floating point number

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_normal', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_normal(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a subnormal floating point number

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_subnormal', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_subnormal(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a floating point number with zero value, i.e., +0 or -0.

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_zero', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_zero(__in Z3_context c, __in Z3_ast t);

   /**
        \brief Predicate indicating whether t is a floating point number representing +Inf or -Inf

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_inf', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_inf(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a NaN

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_nan', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_nan(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Minimum of floating point numbers

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1, t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_min', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_min(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Maximum of floating point numbers

        \param c logical context.
        \param t1 floating-point term.
        \param t2 floating-point term.

        t1, t2 must have the same floating point sort.
     
        def_API('Z3_mk_fpa_max', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_max(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Conversion of a floating point number to another floating-point sort s.

        Produces a term that represents the conversion of a floating-point term t to a different
        floating point sort s. If necessary, rounding according to rm is applied. 

        \param c logical context.
        \param s floating-point sort.
        \param rm rounding mode.
        \param t floating-point term.        

        s must be a floating point sort, rm must have rounding mode sort, and t must have floating point sort.
     
        def_API('Z3_mk_fpa_convert', AST, (_in(CONTEXT),_in(SORT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_convert(__in Z3_context c, __in Z3_sort s, __in Z3_ast rm, __in Z3_ast t);

    /**
        \brief Conversion of a floating point term to a bit-vector term in IEEE754 format.

        \param c logical context.
        \param t floating-point term.

        t must have floating point sort. The size of the resulting bit-vector is automatically determined.

        def_API('Z3_mk_fpa_to_ieee_bv', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_to_ieee_bv(__in Z3_context c, __in Z3_ast t);


    /*@}*/
    /*@}*/

#ifdef __cplusplus
};
#endif // __cplusplus

#endif

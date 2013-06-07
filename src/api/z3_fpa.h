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
        \brief Create a rounding mode sort.
     
        def_API('Z3_mk_fpa_rounding_mode_sort', SORT, (_in(CONTEXT),))
    */
    Z3_sort Z3_API Z3_mk_fpa_rounding_mode_sort(__in Z3_context c);

    /**
        \brief Create a numeral of rounding mode sort which represents the NearestTiesToEven rounding mode.
     
        def_API('Z3_mk_fpa_round_nearest_ties_to_even', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_even(__in Z3_context c);

    /**
        \brief Create a numeral of rounding mode sort which represents the NearestTiesToAway rounding mode.
     
        def_API('Z3_mk_fpa_round_nearest_ties_to_away', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_nearest_ties_to_away(__in Z3_context c);

    /**
        \brief Create a numeral of rounding mode sort which represents the TowardPositive rounding mode.
     
        def_API('Z3_mk_fpa_round_toward_positive', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_positive(__in Z3_context c);    

    /**
        \brief Create a numeral of rounding mode sort which represents the TowardNegative rounding mode.
     
        def_API('Z3_mk_fpa_round_toward_negative', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_negative(__in Z3_context c);    

    /**
        \brief Create a numeral of rounding mode sort which represents the TowardZero rounding mode.
     
        def_API('Z3_mk_fpa_round_toward_zero', AST, (_in(CONTEXT),))
    */
    Z3_ast Z3_API Z3_mk_fpa_round_toward_zero(__in Z3_context c);

    /**
        \brief Create a floating point sort.
     
        def_API('Z3_mk_fpa_sort', SORT, (_in(CONTEXT), _in(UINT), _in(UINT)))

        \remark ebits must be larger than 1 and sbits must be larger than 2.
    */
    Z3_sort Z3_API Z3_mk_fpa_sort(__in Z3_context c, __in unsigned ebits, __in unsigned sbits);

    /**
        \brief Create a NaN of sort s.
     
        def_API('Z3_mk_fpa_nan', AST, (_in(CONTEXT),_in(SORT)))
    */
    Z3_ast Z3_API Z3_mk_fpa_nan(__in Z3_context c, __in Z3_sort s);

    /**
        \brief Create a floating point infinity of sort s.
     
        When \c negative is true, -Inf will be generated instead of +Inf.

        def_API('Z3_mk_fpa_inf', AST, (_in(CONTEXT),_in(SORT),_in(BOOL)))
    */
    Z3_ast Z3_API Z3_mk_fpa_inf(__in Z3_context c, __in Z3_sort s, __in Z3_bool negative);
  
    /**
        \brief Floating-point absolute value

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_abs', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_abs(__in Z3_context c, __in Z3_ast t);
   
    /**
        \brief Floating-point negation

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_neg', AST, (_in(CONTEXT),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_neg(__in Z3_context c, __in Z3_ast t);
   
    /**
        \brief Floating-point addition

        rm must be of FPA rounding mode sort, t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_add', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_add(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Floating-point subtraction

        rm must be of FPA rounding mode sort, t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_sub', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_sub(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point multiplication

        rm must be of FPA rounding mode sort, t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_mul', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_mul(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point division

        The nodes rm must be of FPA rounding mode sort t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_div', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_div(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2);    
   
    /**
        \brief Floating-point fused multiply-add.

        The result is round((t1 * t2) + t3)

        rm must be of FPA rounding mode sort, t1, t2, and t3 must have floating point sort.
     
        def_API('Z3_mk_fpa_fma', AST, (_in(CONTEXT),_in(AST),_in(AST),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_fma(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t1, __in Z3_ast t2, __in Z3_ast t3);
   
    /**
        \brief Floating-point square root

        rm must be of FPA rounding mode sort, t must have floating point sort.
     
        def_API('Z3_mk_fpa_sqrt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_sqrt(__in Z3_context c, __in Z3_ast rm, __in Z3_ast t);
   
    /**
        \brief Floating-point remainder

        t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_rem', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */
    Z3_ast Z3_API Z3_mk_fpa_rem(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);   
   
    /**
        \brief Floating-point equality

        Note that this is IEEE 754 equality (as opposed to SMT-LIB =).

        t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_eq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_eq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
     /**
        \brief Floating-point less-than or equal        

        t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_leq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_leq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

     /**
        \brief Floating-point less-than

        t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_lt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_lt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
    
    
    /**
        \brief Floating-point greater-than or equal        

        t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_geq', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_geq(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Floating-point greater-than

        t1 and t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_gt', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_gt(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Predicate indicating whether t is a normal floating point number

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_normal', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_normal(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a subnormal floating point number

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_subnormal', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_subnormal(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a floating point number with zero value, i.e., +0 or -0.

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_zero', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_zero(__in Z3_context c, __in Z3_ast t);

   /**
        \brief Predicate indicating whether t is a floating point number representing +Inf or -Inf

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_inf', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_inf(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Predicate indicating whether t is a NaN

        t must have floating point sort.
     
        def_API('Z3_mk_fpa_is_nan', AST, (_in(CONTEXT),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_is_nan(__in Z3_context c, __in Z3_ast t);

    /**
        \brief Minimum of floating point numbers

        t1, t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_min', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_min(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);
   
    /**
        \brief Maximum of floating point numbers

        t1, t2 must have floating point sort.
     
        def_API('Z3_mk_fpa_max', AST, (_in(CONTEXT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_max(__in Z3_context c, __in Z3_ast t1, __in Z3_ast t2);

    /**
        \brief Conversion of a floating point number to sort s.

        s must be a floating point sort, rm must have rounding mode sort, and t must have floating point sort.
     
        def_API('Z3_mk_fpa_convert', AST, (_in(CONTEXT),_in(SORT),_in(AST),_in(AST)))
    */      
    Z3_ast Z3_API Z3_mk_fpa_convert(__in Z3_context c, __in Z3_sort s, __in Z3_ast rm, __in Z3_ast t);
   
#ifdef __cplusplus
};
#endif // __cplusplus

#endif

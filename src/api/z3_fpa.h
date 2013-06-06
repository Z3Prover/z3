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
  
#ifdef __cplusplus
};
#endif // __cplusplus

#endif

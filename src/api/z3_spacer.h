/*++
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    z3_spacer.h

Abstract:

    Spacer API

Author:

    Arie Gurfinkel (arie)

Notes:

--*/
#pragma once

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /**@{*/

    /** @name Spacer facilities */
    /**@{*/
    /**
        \brief Pose a query against the asserted rules at the given level.

        \code
           query ::= (exists (bound-vars) query)
                 |  literals
        \endcode

        query returns
        - \c Z3_L_FALSE if the query is unsatisfiable.
        - \c Z3_L_TRUE if the query is satisfiable. Obtain the answer by calling #Z3_fixedpoint_get_answer.
        - \c Z3_L_UNDEF if the query was interrupted, timed out or otherwise failed.

        def_API('Z3_fixedpoint_query_from_lvl', LBOOL, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST), _in(UINT)))
    */
    Z3_lbool Z3_API Z3_fixedpoint_query_from_lvl (Z3_context c,Z3_fixedpoint d, Z3_ast query, unsigned lvl);

     /**
       \brief Retrieve a bottom-up (from query) sequence of ground facts

       The previous call to #Z3_fixedpoint_query must have returned \c Z3_L_TRUE.

       def_API('Z3_fixedpoint_get_ground_sat_answer', AST, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_ast Z3_API Z3_fixedpoint_get_ground_sat_answer(Z3_context c,Z3_fixedpoint d);

    /**
       \brief Obtain the list of rules along the counterexample trace.

       def_API('Z3_fixedpoint_get_rules_along_trace', AST_VECTOR, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_ast_vector Z3_API Z3_fixedpoint_get_rules_along_trace(Z3_context c,Z3_fixedpoint d);

    /**
       \brief Obtain the list of rules along the counterexample trace.

       def_API('Z3_fixedpoint_get_rule_names_along_trace', SYMBOL, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_symbol Z3_API Z3_fixedpoint_get_rule_names_along_trace(Z3_context c,Z3_fixedpoint d);

    /**
       \brief Add an invariant for the predicate \c pred.
       Add an assumed invariant of predicate \c pred.

       Note: this functionality is Spacer specific.

       def_API('Z3_fixedpoint_add_invariant', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL), _in(AST)))
    */
    void Z3_API Z3_fixedpoint_add_invariant(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred, Z3_ast property);


    /**
       Retrieve reachable states of a predicate.
       Note: this functionality is Spacer specific.

       def_API('Z3_fixedpoint_get_reachable', AST, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL)))
     */
    Z3_ast Z3_API Z3_fixedpoint_get_reachable(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred);

    /**
       \brief Project variables given a model

       def_API('Z3_qe_model_project', AST, (_in(CONTEXT), _in(MODEL), _in(UINT), _in_array(2, APP), _in(AST)))
    */
    Z3_ast Z3_API Z3_qe_model_project
      (Z3_context c,
       Z3_model m,
       unsigned num_bounds,
       Z3_app const bound[],
       Z3_ast body);


    /**
       \brief Project variables given a model

       def_API('Z3_qe_model_project_skolem', AST, (_in(CONTEXT), _in(MODEL), _in(UINT), _in_array(2, APP), _in(AST), _in(AST_MAP)))
    */
    Z3_ast Z3_API Z3_qe_model_project_skolem
      (Z3_context c,
       Z3_model m,
       unsigned num_bounds,
       Z3_app const bound[],
       Z3_ast body,
       Z3_ast_map map);

    /**
       \brief Extrapolates a model of a formula

       def_API('Z3_model_extrapolate', AST, (_in(CONTEXT), _in(MODEL), _in(AST)))
    */
    Z3_ast Z3_API Z3_model_extrapolate
      (Z3_context c,
       Z3_model m,
       Z3_ast fml);

    /**
       \brief Best-effort quantifier elimination

       def_API ('Z3_qe_lite', AST, (_in(CONTEXT), _in(AST_VECTOR), _in(AST)))
    */
    Z3_ast Z3_API Z3_qe_lite
      (Z3_context c,
       Z3_ast_vector vars,
       Z3_ast body);

    /**@}*/
    /**@}*/

#ifdef __cplusplus
}
#endif // __cplusplus


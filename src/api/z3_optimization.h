/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    z3_optimization.h

Abstract:

    Optimization facilities

Author:

    Christoph M. Wintersteiger (cwinter) 2015-12-03

Notes:

--*/
#ifndef Z3_OPTIMIZATION_H_
#define Z3_OPTIMIZATION_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /*@{*/

    /** @name Optimization facilities */
    /*@{*/
    /**
       \brief Create a new optimize context.

       \remark User must use #Z3_optimize_inc_ref and #Z3_optimize_dec_ref to manage optimize objects.
       Even if the context was created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_optimize', OPTIMIZE, (_in(CONTEXT), ))
    */
    Z3_optimize Z3_API Z3_mk_optimize(Z3_context c);

    /**
       \brief Increment the reference counter of the given optimize context

       def_API('Z3_optimize_inc_ref', VOID, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    void Z3_API Z3_optimize_inc_ref(Z3_context c, Z3_optimize d);

    /**
       \brief Decrement the reference counter of the given optimize context.

       def_API('Z3_optimize_dec_ref', VOID, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    void Z3_API Z3_optimize_dec_ref(Z3_context c, Z3_optimize d);

    /**
       \brief Assert hard constraint to the optimization context.

       def_API('Z3_optimize_assert', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(AST)))
    */
    void Z3_API Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a);

    /**
       \brief Assert soft constraint to the optimization context.
       \param c - context
       \param o - optimization context
       \param a - formula
       \param weight - a positive weight, penalty for violating soft constraint
       \param id - optional identifier to group soft constraints

       def_API('Z3_optimize_assert_soft', UINT, (_in(CONTEXT), _in(OPTIMIZE), _in(AST), _in(STRING), _in(SYMBOL)))
    */
    unsigned Z3_API Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a, Z3_string weight, Z3_symbol id);


    /**
       \brief Add a maximization constraint.
       \param c - context
       \param o - optimization context
       \param a - arithmetical term
       def_API('Z3_optimize_maximize', UINT, (_in(CONTEXT), _in(OPTIMIZE), _in(AST)))
    */
    unsigned Z3_API Z3_optimize_maximize(Z3_context c, Z3_optimize o, Z3_ast t);

    /**
       \brief Add a minimization constraint.
       \param c - context
       \param o - optimization context
       \param a - arithmetical term

       def_API('Z3_optimize_minimize', UINT, (_in(CONTEXT), _in(OPTIMIZE), _in(AST)))
    */
    unsigned Z3_API Z3_optimize_minimize(Z3_context c, Z3_optimize o, Z3_ast t);


    /**
       \brief Create a backtracking point.

       The optimize solver contains a set of rules, added facts and assertions.
       The set of rules, facts and assertions are restored upon calling #Z3_optimize_pop.

       \sa Z3_optimize_pop

       def_API('Z3_optimize_push', VOID, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    void Z3_API Z3_optimize_push(Z3_context c, Z3_optimize d);

    /**
       \brief Backtrack one level.

       \sa Z3_optimize_push

       \pre The number of calls to pop cannot exceed calls to push.

       def_API('Z3_optimize_pop', VOID, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    void Z3_API Z3_optimize_pop(Z3_context c, Z3_optimize d);

    /**
       \brief Check consistency and produce optimal values.
       \param c - context
       \param o - optimization context

       def_API('Z3_optimize_check', INT, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_lbool Z3_API Z3_optimize_check(Z3_context c, Z3_optimize o);


    /**
       \brief Retrieve a string that describes the last status returned by #Z3_optimize_check.

       Use this method when #Z3_optimize_check returns Z3_L_UNDEF.

       def_API('Z3_optimize_get_reason_unknown', STRING, (_in(CONTEXT), _in(OPTIMIZE) ))
    */
    Z3_string Z3_API Z3_optimize_get_reason_unknown(Z3_context c, Z3_optimize d);

    /**
       \brief Retrieve the model for the last #Z3_optimize_check

       The error handler is invoked if a model is not available because
       the commands above were not invoked for the given optimization
       solver, or if the result was \c Z3_L_FALSE.

       def_API('Z3_optimize_get_model', MODEL, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_model Z3_API Z3_optimize_get_model(Z3_context c, Z3_optimize o);

    /**
       \brief Set parameters on optimization context.

       \param c - context
       \param o - optimization context
       \param p - parameters

       def_API('Z3_optimize_set_params', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(PARAMS)))
    */
    void Z3_API Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p);

    /**
       \brief Return the parameter description set for the given optimize object.

       \param c - context
       \param o - optimization context

       def_API('Z3_optimize_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_param_descrs Z3_API Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o);

    /**
       \brief Retrieve lower bound value or approximation for the i'th optimization objective.

       \param c - context
       \param o - optimization context
       \param idx - index of optimization objective

       def_API('Z3_optimize_get_lower', AST, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT)))
    */
    Z3_ast Z3_API Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned idx);

    /**
       \brief Retrieve upper bound value or approximation for the i'th optimization objective.

       \param c - context
       \param o - optimization context
       \param idx - index of optimization objective

       def_API('Z3_optimize_get_upper', AST, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT)))
    */
    Z3_ast Z3_API Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned idx);

    /**
       \brief Print the current context as a string.
       \param c - context.
       \param o - optimization context.

       def_API('Z3_optimize_to_string', STRING, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_string Z3_API Z3_optimize_to_string(Z3_context c, Z3_optimize o);


    /**
       \brief Return a string containing a description of parameters accepted by optimize.

       def_API('Z3_optimize_get_help', STRING, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_string Z3_API Z3_optimize_get_help(Z3_context c, Z3_optimize t);

    /**
       \brief Retrieve statistics information from the last call to #Z3_optimize_check

       def_API('Z3_optimize_get_statistics', STATS, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_stats Z3_API Z3_optimize_get_statistics(Z3_context c, Z3_optimize d);
    /*@}*/
    /*@}*/

#ifdef __cplusplus
}
#endif // __cplusplus

#endif
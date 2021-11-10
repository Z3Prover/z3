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
#pragma once

/**
   \brief callback functions for models.
 */
typedef void Z3_model_eh(void* ctx);

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /**@{*/

    /** @name Optimization facilities */
    /**@{*/
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

       \sa Z3_optimize_assert_soft
       \sa Z3_optimize_assert_and_track

       def_API('Z3_optimize_assert', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(AST)))
    */
    void Z3_API Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a);


    /**
       \brief Assert tracked hard constraint to the optimization context.

       \sa Z3_optimize_assert
       \sa Z3_optimize_assert_soft

       def_API('Z3_optimize_assert_and_track', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(AST), _in(AST)))
    */
    void Z3_API Z3_optimize_assert_and_track(Z3_context c, Z3_optimize o, Z3_ast a, Z3_ast t);

    /**
       \brief Assert soft constraint to the optimization context.
       \param c - context
       \param o - optimization context
       \param a - formula
       \param weight - a positive weight, penalty for violating soft constraint
       \param id - optional identifier to group soft constraints

       \sa Z3_optimize_assert
       \sa Z3_optimize_assert_and_track

       def_API('Z3_optimize_assert_soft', UINT, (_in(CONTEXT), _in(OPTIMIZE), _in(AST), _in(STRING), _in(SYMBOL)))
    */
    unsigned Z3_API Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a, Z3_string weight, Z3_symbol id);

    /**
       \brief Add a maximization constraint.
       \param c - context
       \param o - optimization context
       \param t - arithmetical term

       \sa Z3_optimize_minimize

       def_API('Z3_optimize_maximize', UINT, (_in(CONTEXT), _in(OPTIMIZE), _in(AST)))
    */
    unsigned Z3_API Z3_optimize_maximize(Z3_context c, Z3_optimize o, Z3_ast t);

    /**
       \brief Add a minimization constraint.
       \param c - context
       \param o - optimization context
       \param t - arithmetical term

       \sa Z3_optimize_maximize

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
       \param num_assumptions - number of additional assumptions
       \param assumptions - the additional assumptions

       \sa Z3_optimize_get_reason_unknown
       \sa Z3_optimize_get_model
       \sa Z3_optimize_get_statistics
       \sa Z3_optimize_get_unsat_core

       def_API('Z3_optimize_check', INT, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT), _in_array(2, AST)))
    */
    Z3_lbool Z3_API Z3_optimize_check(Z3_context c, Z3_optimize o, unsigned num_assumptions, Z3_ast const assumptions[]);


    /**
       \brief Retrieve a string that describes the last status returned by #Z3_optimize_check.

       Use this method when #Z3_optimize_check returns \c Z3_L_UNDEF.

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
       \brief Retrieve the unsat core for the last #Z3_optimize_check
       The unsat core is a subset of the assumptions \c a.

       def_API('Z3_optimize_get_unsat_core', AST_VECTOR, (_in(CONTEXT), _in(OPTIMIZE)))       
     */
    Z3_ast_vector Z3_API Z3_optimize_get_unsat_core(Z3_context c, Z3_optimize o);

    /**
       \brief Set parameters on optimization context.

       \param c - context
       \param o - optimization context
       \param p - parameters

       \sa Z3_optimize_get_help
       \sa Z3_optimize_get_param_descrs

       def_API('Z3_optimize_set_params', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(PARAMS)))
    */
    void Z3_API Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p);

    /**
       \brief Return the parameter description set for the given optimize object.

       \param c - context
       \param o - optimization context

       \sa Z3_optimize_get_help
       \sa Z3_optimize_set_params

       def_API('Z3_optimize_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_param_descrs Z3_API Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o);

    /**
       \brief Retrieve lower bound value or approximation for the i'th optimization objective.

       \param c - context
       \param o - optimization context
       \param idx - index of optimization objective

       \sa Z3_optimize_get_upper
       \sa Z3_optimize_get_lower_as_vector
       \sa Z3_optimize_get_upper_as_vector

       def_API('Z3_optimize_get_lower', AST, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT)))
    */
    Z3_ast Z3_API Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned idx);

    /**
       \brief Retrieve upper bound value or approximation for the i'th optimization objective.

       \param c - context
       \param o - optimization context
       \param idx - index of optimization objective

       \sa Z3_optimize_get_lower
       \sa Z3_optimize_get_lower_as_vector
       \sa Z3_optimize_get_upper_as_vector

       def_API('Z3_optimize_get_upper', AST, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT)))
    */
    Z3_ast Z3_API Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned idx);


    /**
       \brief Retrieve lower bound value or approximation for the i'th optimization objective.
              The returned vector is of length 3. It always contains numerals.
              The three numerals are coefficients \c a, \c b, \c c and encode the result of
              #Z3_optimize_get_lower \ccode{a * infinity + b + c * epsilon}.
              
       \param c - context
       \param o - optimization context
       \param idx - index of optimization objective

       \sa Z3_optimize_get_lower
       \sa Z3_optimize_get_upper
       \sa Z3_optimize_get_upper_as_vector

       def_API('Z3_optimize_get_lower_as_vector', AST_VECTOR, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT)))
    */
    Z3_ast_vector Z3_API Z3_optimize_get_lower_as_vector(Z3_context c, Z3_optimize o, unsigned idx);

    /**
       \brief Retrieve upper bound value or approximation for the i'th optimization objective.

       \param c - context
       \param o - optimization context
       \param idx - index of optimization objective

       \sa Z3_optimize_get_lower
       \sa Z3_optimize_get_upper
       \sa Z3_optimize_get_lower_as_vector

       def_API('Z3_optimize_get_upper_as_vector', AST_VECTOR, (_in(CONTEXT), _in(OPTIMIZE), _in(UINT)))
    */
    Z3_ast_vector Z3_API Z3_optimize_get_upper_as_vector(Z3_context c, Z3_optimize o, unsigned idx);


    /**
       \brief Print the current context as a string.
       \param c - context.
       \param o - optimization context.

       \sa Z3_optimize_from_file
       \sa Z3_optimize_from_string

       def_API('Z3_optimize_to_string', STRING, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_string Z3_API Z3_optimize_to_string(Z3_context c, Z3_optimize o);

    /**
       \brief Parse an SMT-LIB2 string with assertions,
       soft constraints and optimization objectives.
       Add the parsed constraints and objectives to the optimization context.

       \param c - context.
       \param o - optimize context.
       \param s - string containing SMT2 specification.

       \sa Z3_optimize_from_file
       \sa Z3_optimize_to_string

       def_API('Z3_optimize_from_string', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(STRING)))
    */
    void Z3_API Z3_optimize_from_string(Z3_context c, Z3_optimize o, Z3_string s);

    /**
       \brief Parse an SMT-LIB2 file with assertions,
       soft constraints and optimization objectives.
       Add the parsed constraints and objectives to the optimization context.

       \param c - context.
       \param o - optimize context.
       \param s - path to file containing SMT2 specification.

       \sa Z3_optimize_from_string
       \sa Z3_optimize_to_string

       def_API('Z3_optimize_from_file', VOID, (_in(CONTEXT), _in(OPTIMIZE), _in(STRING)))
    */
    void Z3_API Z3_optimize_from_file(Z3_context c, Z3_optimize o, Z3_string s);

    /**
       \brief Return a string containing a description of parameters accepted by optimize.

       \sa Z3_optimize_get_param_descrs
       \sa Z3_optimize_set_params

       def_API('Z3_optimize_get_help', STRING, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_string Z3_API Z3_optimize_get_help(Z3_context c, Z3_optimize t);

    /**
       \brief Retrieve statistics information from the last call to #Z3_optimize_check

       def_API('Z3_optimize_get_statistics', STATS, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_stats Z3_API Z3_optimize_get_statistics(Z3_context c, Z3_optimize d);

    /**
       \brief Return the set of asserted formulas on the optimization context.

       def_API('Z3_optimize_get_assertions', AST_VECTOR, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_ast_vector Z3_API Z3_optimize_get_assertions(Z3_context c, Z3_optimize o);

    /**
       \brief Return objectives on the optimization context.
       If the objective function is a max-sat objective it is returned
       as a Pseudo-Boolean (minimization) sum of the form \ccode{(+ (if f1 w1 0) (if f2 w2 0) ...)}
       If the objective function is entered as a maximization objective, then return
       the corresponding minimization objective. In this way the resulting objective
       function is always returned as a minimization objective.

       def_API('Z3_optimize_get_objectives', AST_VECTOR, (_in(CONTEXT), _in(OPTIMIZE)))
    */
    Z3_ast_vector Z3_API Z3_optimize_get_objectives(Z3_context c, Z3_optimize o);


    /**
       \brief register a model event handler for new models.
     */
    void Z3_API Z3_optimize_register_model_eh(
        Z3_context   c, 
        Z3_optimize  o,
        Z3_model     m,
        void*        ctx,
        Z3_model_eh  model_eh);


    /**@}*/
    /**@}*/

#ifdef __cplusplus
}
#endif // __cplusplus


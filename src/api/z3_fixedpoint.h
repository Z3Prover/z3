/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    z3_fixedpoint.h

Abstract:

    Fixedpoint API

Author:

    Christoph M. Wintersteiger (cwinter) 2015-12-03

Notes:

--*/
#ifndef Z3_FIXEDPOINT_H_
#define Z3_FIXEDPOINT_H_

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

    /** \defgroup capi C API */
    /*@{*/

    /** @name Fixedpoint facilities */
    /*@{*/
    /**
       \brief Create a new fixedpoint context.

       \remark User must use #Z3_fixedpoint_inc_ref and #Z3_fixedpoint_dec_ref to manage fixedpoint objects.
       Even if the context was created using #Z3_mk_context instead of #Z3_mk_context_rc.

       def_API('Z3_mk_fixedpoint', FIXEDPOINT, (_in(CONTEXT), ))
    */
    Z3_fixedpoint Z3_API Z3_mk_fixedpoint(Z3_context c);

    /**
       \brief Increment the reference counter of the given fixedpoint context

       def_API('Z3_fixedpoint_inc_ref', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    void Z3_API Z3_fixedpoint_inc_ref(Z3_context c, Z3_fixedpoint d);

    /**
       \brief Decrement the reference counter of the given fixedpoint context.

       def_API('Z3_fixedpoint_dec_ref', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    void Z3_API Z3_fixedpoint_dec_ref(Z3_context c, Z3_fixedpoint d);

    /**
       \brief Add a universal Horn clause as a named rule.
       The \c horn_rule should be of the form:

       \code
           horn_rule ::= (forall (bound-vars) horn_rule)
                      |  (=> atoms horn_rule)
                      |  atom
       \endcode

       def_API('Z3_fixedpoint_add_rule', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST), _in(SYMBOL)))
    */
    void Z3_API Z3_fixedpoint_add_rule(Z3_context c, Z3_fixedpoint d, Z3_ast rule, Z3_symbol name);

    /**
       \brief Add a Database fact.

       \param c - context
       \param d - fixed point context
       \param r - relation signature for the row.
       \param num_args - number of columns for the given row.
       \param args - array of the row elements.

       The number of arguments \c num_args should be equal to the number
       of sorts in the domain of \c r. Each sort in the domain should be an integral
      (bit-vector, Boolean or or finite domain sort).

       The call has the same effect as adding a rule where \c r is applied to the arguments.

       def_API('Z3_fixedpoint_add_fact', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL), _in(UINT), _in_array(3, UINT)))
    */
    void Z3_API Z3_fixedpoint_add_fact(Z3_context c, Z3_fixedpoint d,
                                       Z3_func_decl r,
                                       unsigned num_args, unsigned args[]);

    /**
       \brief Assert a constraint to the fixedpoint context.

       The constraints are used as background axioms when the fixedpoint engine uses the PDR mode.
       They are ignored for standard Datalog mode.

       def_API('Z3_fixedpoint_assert', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST)))
    */
    void Z3_API Z3_fixedpoint_assert(Z3_context c, Z3_fixedpoint d, Z3_ast axiom);

    /**
        \brief Pose a query against the asserted rules.

        \code
           query ::= (exists (bound-vars) query)
                 |  literals
        \endcode

        query returns
        - Z3_L_FALSE if the query is unsatisfiable.
        - Z3_L_TRUE if the query is satisfiable. Obtain the answer by calling #Z3_fixedpoint_get_answer.
        - Z3_L_UNDEF if the query was interrupted, timed out or otherwise failed.

        def_API('Z3_fixedpoint_query', INT, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST)))
    */
    Z3_lbool Z3_API Z3_fixedpoint_query(Z3_context c, Z3_fixedpoint d, Z3_ast query);

    /**
        \brief Pose multiple queries against the asserted rules.

        The queries are encoded as relations (function declarations).

        query returns
        - Z3_L_FALSE if the query is unsatisfiable.
        - Z3_L_TRUE if the query is satisfiable. Obtain the answer by calling #Z3_fixedpoint_get_answer.
        - Z3_L_UNDEF if the query was interrupted, timed out or otherwise failed.

        def_API('Z3_fixedpoint_query_relations', INT, (_in(CONTEXT), _in(FIXEDPOINT), _in(UINT), _in_array(2, FUNC_DECL)))
    */
    Z3_lbool Z3_API Z3_fixedpoint_query_relations(
        Z3_context c, Z3_fixedpoint d,
        unsigned num_relations, Z3_func_decl const relations[]);

    /**
       \brief Retrieve a formula that encodes satisfying answers to the query.


       When used in Datalog mode, the returned answer is a disjunction of conjuncts.
       Each conjunct encodes values of the bound variables of the query that are satisfied.
       In PDR mode, the returned answer is a single conjunction.

       When used in Datalog mode the previous call to Z3_fixedpoint_query must have returned Z3_L_TRUE.
       When used with the PDR engine, the previous call must have been either Z3_L_TRUE or Z3_L_FALSE.

       def_API('Z3_fixedpoint_get_answer', AST, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_ast Z3_API Z3_fixedpoint_get_answer(Z3_context c, Z3_fixedpoint d);

    /**
       \brief Retrieve a string that describes the last status returned by #Z3_fixedpoint_query.

       Use this method when #Z3_fixedpoint_query returns Z3_L_UNDEF.

       def_API('Z3_fixedpoint_get_reason_unknown', STRING, (_in(CONTEXT), _in(FIXEDPOINT) ))
    */
    Z3_string Z3_API Z3_fixedpoint_get_reason_unknown(Z3_context c, Z3_fixedpoint d);

    /**
       \brief Update a named rule.
       A rule with the same name must have been previously created.

       def_API('Z3_fixedpoint_update_rule', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST), _in(SYMBOL)))
    */
    void Z3_API Z3_fixedpoint_update_rule(Z3_context c, Z3_fixedpoint d, Z3_ast a, Z3_symbol name);

    /**
       \brief Query the PDR engine for the maximal levels properties are known about predicate.

       This call retrieves the maximal number of relevant unfoldings
       of \c pred with respect to the current exploration state.
       Note: this functionality is PDR specific.

       def_API('Z3_fixedpoint_get_num_levels', UINT, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL)))
    */
    unsigned Z3_API Z3_fixedpoint_get_num_levels(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred);

    /**
       Retrieve the current cover of \c pred up to \c level unfoldings.
       Return just the delta that is known at \c level. To
       obtain the full set of properties of \c pred one should query
       at \c level+1 , \c level+2 etc, and include \c level=-1.

       Note: this functionality is PDR specific.

       def_API('Z3_fixedpoint_get_cover_delta', AST, (_in(CONTEXT), _in(FIXEDPOINT), _in(INT), _in(FUNC_DECL)))
     */
    Z3_ast Z3_API Z3_fixedpoint_get_cover_delta(Z3_context c, Z3_fixedpoint d, int level, Z3_func_decl pred);

    /**
       \brief Add property about the predicate \c pred.
       Add a property of predicate \c pred at \c level.
       It gets pushed forward when possible.

       Note: level = -1 is treated as the fixedpoint. So passing -1 for the \c level
       means that the property is true of the fixed-point unfolding with respect to \c pred.

       Note: this functionality is PDR specific.

       def_API('Z3_fixedpoint_add_cover', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(INT), _in(FUNC_DECL), _in(AST)))
    */
    void Z3_API Z3_fixedpoint_add_cover(Z3_context c, Z3_fixedpoint d, int level, Z3_func_decl pred, Z3_ast property);

    /**
       \brief Retrieve statistics information from the last call to #Z3_fixedpoint_query.

       def_API('Z3_fixedpoint_get_statistics', STATS, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_stats Z3_API Z3_fixedpoint_get_statistics(Z3_context c, Z3_fixedpoint d);

    /**
       \brief Register relation as Fixedpoint defined.
       Fixedpoint defined relations have least-fixedpoint semantics.
       For example, the relation is empty if it does not occur
       in a head or a fact.

       def_API('Z3_fixedpoint_register_relation', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL)))
    */
    void Z3_API Z3_fixedpoint_register_relation(Z3_context c, Z3_fixedpoint d, Z3_func_decl f);

    /**
       \brief Configure the predicate representation.

       It sets the predicate to use a set of domains given by the list of symbols.
       The domains given by the list of symbols must belong to a set
       of built-in domains.

       def_API('Z3_fixedpoint_set_predicate_representation', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL), _in(UINT), _in_array(3, SYMBOL)))
    */
    void Z3_API Z3_fixedpoint_set_predicate_representation(
        Z3_context c,
        Z3_fixedpoint d,
        Z3_func_decl f,
        unsigned num_relations,
        Z3_symbol const relation_kinds[]);

    /**
       \brief Retrieve set of rules from fixedpoint context.

       def_API('Z3_fixedpoint_get_rules', AST_VECTOR, (_in(CONTEXT),_in(FIXEDPOINT)))
     */
    Z3_ast_vector Z3_API Z3_fixedpoint_get_rules(
        Z3_context c,
        Z3_fixedpoint f);

    /**
       \brief Retrieve set of background assertions from fixedpoint context.

       def_API('Z3_fixedpoint_get_assertions', AST_VECTOR, (_in(CONTEXT),_in(FIXEDPOINT)))
     */
    Z3_ast_vector Z3_API Z3_fixedpoint_get_assertions(
        Z3_context c,
        Z3_fixedpoint f);

    /**
       \brief Set parameters on fixedpoint context.

       def_API('Z3_fixedpoint_set_params', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(PARAMS)))
    */
    void Z3_API Z3_fixedpoint_set_params(Z3_context c, Z3_fixedpoint f, Z3_params p);

    /**
       \brief Return a string describing all fixedpoint available parameters.

       def_API('Z3_fixedpoint_get_help', STRING, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_string Z3_API Z3_fixedpoint_get_help(Z3_context c, Z3_fixedpoint f);

    /**
       \brief Return the parameter description set for the given fixedpoint object.

       def_API('Z3_fixedpoint_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    Z3_param_descrs Z3_API Z3_fixedpoint_get_param_descrs(Z3_context c, Z3_fixedpoint f);

    /**
       \brief Print the current rules and background axioms as a string.
       \param c - context.
       \param f - fixedpoint context.
       \param num_queries - number of additional queries to print.
       \param queries - additional queries.

       def_API('Z3_fixedpoint_to_string', STRING, (_in(CONTEXT), _in(FIXEDPOINT), _in(UINT), _in_array(2, AST)))
    */
    Z3_string Z3_API Z3_fixedpoint_to_string(
        Z3_context c,
        Z3_fixedpoint f,
        unsigned num_queries,
        Z3_ast queries[]);

    /**
       \brief Parse an SMT-LIB2 string with fixedpoint rules.
       Add the rules to the current fixedpoint context.
       Return the set of queries in the string.

       \param c - context.
       \param f - fixedpoint context.
       \param s - string containing SMT2 specification.

       def_API('Z3_fixedpoint_from_string', AST_VECTOR, (_in(CONTEXT), _in(FIXEDPOINT), _in(STRING)))
    */
    Z3_ast_vector Z3_API Z3_fixedpoint_from_string(Z3_context c,
                                                   Z3_fixedpoint f,
                                                   Z3_string s);

    /**
       \brief Parse an SMT-LIB2 file with fixedpoint rules.
       Add the rules to the current fixedpoint context.
       Return the set of queries in the file.

       \param c - context.
       \param f - fixedpoint context.
       \param s - string containing SMT2 specification.

       def_API('Z3_fixedpoint_from_file', AST_VECTOR, (_in(CONTEXT), _in(FIXEDPOINT), _in(STRING)))
    */
    Z3_ast_vector Z3_API Z3_fixedpoint_from_file(Z3_context c,
                                                 Z3_fixedpoint f,
                                                 Z3_string s);

    /**
       \brief Create a backtracking point.

       The fixedpoint solver contains a set of rules, added facts and assertions.
       The set of rules, facts and assertions are restored upon calling #Z3_fixedpoint_pop.

       \sa Z3_fixedpoint_pop

       def_API('Z3_fixedpoint_push', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    void Z3_API Z3_fixedpoint_push(Z3_context c, Z3_fixedpoint d);

    /**
       \brief Backtrack one backtracking point.

       \sa Z3_fixedpoint_push

       \pre The number of calls to pop cannot exceed calls to push.

       def_API('Z3_fixedpoint_pop', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
    */
    void Z3_API Z3_fixedpoint_pop(Z3_context c, Z3_fixedpoint d);

    /** \brief The following utilities allows adding user-defined domains. */

    typedef void Z3_fixedpoint_reduce_assign_callback_fptr(
        void*, Z3_func_decl,
        unsigned, Z3_ast const [],
        unsigned, Z3_ast const []);

    typedef void Z3_fixedpoint_reduce_app_callback_fptr(
        void*, Z3_func_decl,
        unsigned, Z3_ast const [],
        Z3_ast*);


    /** \brief Initialize the context with a user-defined state. */
    void Z3_API Z3_fixedpoint_init(Z3_context c, Z3_fixedpoint d, void* state);

    /**
       \brief Register a callback to destructive updates.

       Registers are identified with terms encoded as fresh constants,
    */
    void Z3_API Z3_fixedpoint_set_reduce_assign_callback(
        Z3_context c ,Z3_fixedpoint d, Z3_fixedpoint_reduce_assign_callback_fptr cb);

    /** \brief Register a callback for buildling terms based on the relational operators. */
    void Z3_API Z3_fixedpoint_set_reduce_app_callback(
        Z3_context c, Z3_fixedpoint d, Z3_fixedpoint_reduce_app_callback_fptr cb);

    /*@}*/
    /*@}*/

#ifdef __cplusplus
}
#endif // __cplusplus

#endif

/*++
Regression for recursive QBMC proof reconstruction.
--*/
#include "api/z3.h"
#include "api/api_context.h"
#include "ast/proofs/proof_checker.h"
#include "util/debug.h"
#include "util/obj_hashtable.h"
#include <cstdio>

void tst_api_qbmc_recursive() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "proof", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(ctx, [](Z3_context, Z3_error_code) {});
    Z3_fixedpoint fp = Z3_mk_fixedpoint(ctx);
    Z3_fixedpoint_inc_ref(ctx, fp);
    Z3_params params = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, params);
    Z3_params_set_symbol(ctx, params, Z3_mk_string_symbol(ctx, "engine"), Z3_mk_string_symbol(ctx, "qbmc"));
    for (char const* name : {"xform.inline_eager", "xform.inline_linear", "xform.slice",
                             "xform.subsumption_checker", "xform.coalesce_rules"})
        Z3_params_set_bool(ctx, params, Z3_mk_string_symbol(ctx, name), false);
    Z3_params_set_uint(ctx, params, Z3_mk_string_symbol(ctx, "xform.unfold_rules"), 0);
    Z3_fixedpoint_set_params(ctx, fp, params);
    char const* program = R"(
(declare-rel numeric-goal ())
(declare-rel numeric-left (Int))
(declare-rel numeric-right (Int))
(declare-rel numeric-leaf (Int))
(declare-var x Int)
(rule (! (numeric-leaf 0) :named recursive-base))
(rule (! (=> (and (numeric-leaf x) (< x 3)) (numeric-leaf (+ x 1))) :named recursive-successor))
(rule (! (=> (numeric-leaf 3) numeric-goal) :named recursive-goal))
(query numeric-goal)
)";
    Z3_ast_vector queries = Z3_fixedpoint_from_string(ctx, fp, program);
    ENSURE(Z3_get_error_code(ctx) == Z3_OK);
    ENSURE(Z3_ast_vector_size(ctx, queries) == 1);
    Z3_ast_vector_inc_ref(ctx, queries);
    Z3_lbool result = Z3_fixedpoint_query(ctx, fp, Z3_ast_vector_get(ctx, queries, 0));
    ENSURE(Z3_get_error_code(ctx) == Z3_OK);
    ENSURE(result == Z3_L_TRUE);
    Z3_ast answer = Z3_fixedpoint_get_answer(ctx, fp);
    ENSURE(answer != nullptr);
    {
        ast_manager& m = mk_c(ctx)->m();
        ENSURE(m.is_proof(to_expr(answer)));
        proof_checker checker(m);
        expr_ref_vector side_conditions(m);
        ENSURE(checker.check(to_app(to_expr(answer)), side_conditions));
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        for (expr* condition : side_conditions) {
            Z3_solver_push(ctx, solver);
            expr_ref negated(m.mk_not(condition), m);
            Z3_solver_assert(ctx, solver, reinterpret_cast<Z3_ast>(negated.get()));
            ENSURE(Z3_get_error_code(ctx) == Z3_OK);
            Z3_lbool check = Z3_solver_check(ctx, solver);
            ENSURE(Z3_get_error_code(ctx) == Z3_OK);
            if (check != Z3_L_FALSE) {
                std::fprintf(stderr, "QBMC proof side condition (negation result %d): %s\n", static_cast<int>(check), Z3_ast_to_string(ctx, reinterpret_cast<Z3_ast>(condition)));
            }
            ENSURE(check == Z3_L_FALSE);
            Z3_solver_pop(ctx, solver, 1);
        }
        // Assert the original clauses and the synthetic query bridge, then
        // independently justify every asserted proof leaf against them.
        Z3_ast_vector rules = Z3_fixedpoint_get_rules(ctx, fp);
        ENSURE(Z3_get_error_code(ctx) == Z3_OK);
        Z3_ast_vector_inc_ref(ctx, rules);
        for (unsigned i = 0; i < Z3_ast_vector_size(ctx, rules); ++i)
            Z3_solver_assert(ctx, solver, Z3_ast_vector_get(ctx, rules, i));
        expr_ref bridge(m.mk_implies(to_expr(Z3_ast_vector_get(ctx, queries, 0)),
                                     m.get_fact(to_app(to_expr(answer)))), m);
        Z3_solver_assert(ctx, solver, reinterpret_cast<Z3_ast>(bridge.get()));
        ENSURE(Z3_solver_check(ctx, solver) == Z3_L_TRUE);
        ptr_vector<expr> pending;
        obj_hashtable<expr> visited;
        pending.push_back(to_expr(answer));
        unsigned leaves = 0;
        while (!pending.empty()) {
            expr* node = pending.back(); pending.pop_back();
            if (visited.contains(node)) continue;
            visited.insert(node);
            if (!m.is_proof(node)) continue;
            if (m.is_asserted(node)) {
                ++leaves;
                expr_ref negated(m.mk_not(m.get_fact(to_app(node))), m);
                Z3_solver_push(ctx, solver);
                Z3_solver_assert(ctx, solver, reinterpret_cast<Z3_ast>(negated.get()));
                ENSURE(Z3_solver_check(ctx, solver) == Z3_L_FALSE);
                Z3_solver_pop(ctx, solver, 1);
            }
            for (expr* child : *to_app(node)) pending.push_back(child);
        }
        ENSURE(leaves > 0);
        Z3_ast_vector_dec_ref(ctx, rules);
        Z3_solver_dec_ref(ctx, solver);
    } // checker and side-condition owners must outlive neither the context nor its manager
    Z3_ast_vector_dec_ref(ctx, queries);
    Z3_params_dec_ref(ctx, params);
    Z3_fixedpoint_dec_ref(ctx, fp);
    Z3_del_context(ctx);
}

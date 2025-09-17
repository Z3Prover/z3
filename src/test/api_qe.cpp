/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_qe.cpp

Abstract:

    Test API quantifier elimination functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"

void tst_api_qe() {
    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "model", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Test Z3_qe_lite with simple quantifier elimination
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x");
        Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);

        // Create the formula: exists x. (x > 0)
        Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
        Z3_ast x_gt_zero = Z3_mk_gt(ctx, x, zero);

        // Create AST vector with variables to eliminate
        Z3_ast_vector vars = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, vars, x);

        // Apply quantifier elimination
        Z3_ast result = Z3_qe_lite(ctx, vars, x_gt_zero);
        ENSURE(result != nullptr);
    }

    // Test Z3_qe_lite with multiple variables
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x1");
        Z3_symbol y_sym = Z3_mk_string_symbol(ctx, "y1");
        Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
        Z3_ast y = Z3_mk_const(ctx, y_sym, int_sort);

        // Create the formula: exists x,y. (x + y > 0)
        Z3_ast x_plus_y = Z3_mk_add(ctx, 2, (Z3_ast[]){x, y});
        Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
        Z3_ast x_plus_y_gt_zero = Z3_mk_gt(ctx, x_plus_y, zero);

        Z3_ast_vector vars = Z3_mk_ast_vector(ctx);
        Z3_ast_vector_push(ctx, vars, x);
        Z3_ast_vector_push(ctx, vars, y);

        Z3_ast result = Z3_qe_lite(ctx, vars, x_plus_y_gt_zero);
        ENSURE(result != nullptr);
    }

    // Test Z3_qe_lite with empty variable list
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_ast one = Z3_mk_int(ctx, 1, int_sort);
        Z3_ast two = Z3_mk_int(ctx, 2, int_sort);
        Z3_ast one_eq_two = Z3_mk_eq(ctx, one, two);

        Z3_ast_vector vars = Z3_mk_ast_vector(ctx);

        Z3_ast result = Z3_qe_lite(ctx, vars, one_eq_two);
        ENSURE(result != nullptr);
    }

    // Test Z3_model_extrapolate with a simple model
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x2");
        Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
        Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
        Z3_ast x_geq_zero = Z3_mk_ge(ctx, x, zero);

        // Create a solver and get a model
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        Z3_solver_assert(ctx, solver, x_geq_zero);

        Z3_lbool result = Z3_solver_check(ctx, solver);
        if (result == Z3_L_TRUE) {
            Z3_model model = Z3_solver_get_model(ctx, solver);
            if (model != nullptr) {
                Z3_model_inc_ref(ctx, model);

                // Test extrapolation
                Z3_ast extrapolated = Z3_model_extrapolate(ctx, model, x_geq_zero);
                ENSURE(extrapolated != nullptr);

                Z3_model_dec_ref(ctx, model);
            }
        }

        Z3_solver_dec_ref(ctx, solver);
    }

    // Test Z3_qe_model_project with a simple case
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x3");
        Z3_symbol y_sym = Z3_mk_string_symbol(ctx, "y3");
        Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
        Z3_ast y = Z3_mk_const(ctx, y_sym, int_sort);

        // Create constraint: x + y = 5
        Z3_ast five = Z3_mk_int(ctx, 5, int_sort);
        Z3_ast x_plus_y = Z3_mk_add(ctx, 2, (Z3_ast[]){x, y});
        Z3_ast constraint = Z3_mk_eq(ctx, x_plus_y, five);

        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        Z3_solver_assert(ctx, solver, constraint);

        Z3_lbool check_result = Z3_solver_check(ctx, solver);
        if (check_result == Z3_L_TRUE) {
            Z3_model model = Z3_solver_get_model(ctx, solver);
            if (model != nullptr) {
                Z3_model_inc_ref(ctx, model);

                // Project out x variable
                Z3_app bound[] = {(Z3_app)x};
                Z3_ast projected = Z3_qe_model_project(ctx, model, 1, bound, constraint);
                ENSURE(projected != nullptr);

                Z3_model_dec_ref(ctx, model);
            }
        }

        Z3_solver_dec_ref(ctx, solver);
    }

    // Test Z3_qe_model_project_skolem with Skolem function mapping
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x4");
        Z3_symbol y_sym = Z3_mk_string_symbol(ctx, "y4");
        Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);
        Z3_ast y = Z3_mk_const(ctx, y_sym, int_sort);

        Z3_ast ten = Z3_mk_int(ctx, 10, int_sort);
        Z3_ast x_plus_y = Z3_mk_add(ctx, 2, (Z3_ast[]){x, y});
        Z3_ast constraint = Z3_mk_eq(ctx, x_plus_y, ten);

        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        Z3_solver_assert(ctx, solver, constraint);

        Z3_lbool check_result = Z3_solver_check(ctx, solver);
        if (check_result == Z3_L_TRUE) {
            Z3_model model = Z3_solver_get_model(ctx, solver);
            if (model != nullptr) {
                Z3_model_inc_ref(ctx, model);

                Z3_ast_map skolem_map = Z3_mk_ast_map(ctx);
                Z3_ast_map_inc_ref(ctx, skolem_map);

                // Project with skolem function
                Z3_app bound[] = {(Z3_app)x};
                Z3_ast projected = Z3_qe_model_project_skolem(ctx, model, 1, bound, constraint, skolem_map);
                ENSURE(projected != nullptr);

                Z3_ast_map_dec_ref(ctx, skolem_map);
                Z3_model_dec_ref(ctx, model);
            }
        }

        Z3_solver_dec_ref(ctx, solver);
    }

    // Test Z3_qe_model_project_with_witness
    {
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        Z3_symbol x_sym = Z3_mk_string_symbol(ctx, "x5");
        Z3_ast x = Z3_mk_const(ctx, x_sym, int_sort);

        Z3_ast zero = Z3_mk_int(ctx, 0, int_sort);
        Z3_ast x_gt_zero = Z3_mk_gt(ctx, x, zero);

        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);
        Z3_solver_assert(ctx, solver, x_gt_zero);

        Z3_lbool check_result = Z3_solver_check(ctx, solver);
        if (check_result == Z3_L_TRUE) {
            Z3_model model = Z3_solver_get_model(ctx, solver);
            if (model != nullptr) {
                Z3_model_inc_ref(ctx, model);

                Z3_ast_map witness_map = Z3_mk_ast_map(ctx);
                Z3_ast_map_inc_ref(ctx, witness_map);

                Z3_app bound[] = {(Z3_app)x};
                Z3_ast projected = Z3_qe_model_project_with_witness(ctx, model, 1, bound, x_gt_zero, witness_map);
                ENSURE(projected != nullptr);

                Z3_ast_map_dec_ref(ctx, witness_map);
                Z3_model_dec_ref(ctx, model);
            }
        }

        Z3_solver_dec_ref(ctx, solver);
    }

    Z3_del_context(ctx);
}
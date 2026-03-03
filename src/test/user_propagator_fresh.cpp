/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    user_propagator_fresh.cpp

Abstract:

    Unit test for user propagator mk_fresh callback via C API.
    Checks that the fresh callback is invoked and that there are no memory leaks.

--*/

#include "api/z3.h"
#include "util/memory_manager.h"
#include "util/debug.h"
#include <iostream>

static unsigned g_fresh_count = 0;

static void* test_fresh_eh(void* user_ctx, Z3_context new_ctx) {
    g_fresh_count++;
    return nullptr;
}

static void test_push_eh(void* user_ctx, Z3_solver_callback cb) {}

static void test_pop_eh(void* user_ctx, Z3_solver_callback cb, unsigned num_scopes) {}

static void run_propagator_fresh_once() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);

    Z3_solver_propagate_init(ctx, s, nullptr,
                             test_push_eh,
                             test_pop_eh,
                             test_fresh_eh);

    // Build: forall (x:Int). p(x)
    // This is SAT and triggers model-based quantifier instantiation,
    // which creates an auxiliary context and invokes mk_fresh.
    Z3_sort int_sort = Z3_mk_int_sort(ctx);
    Z3_sort bool_sort = Z3_mk_bool_sort(ctx);
    Z3_sort domain[1] = { int_sort };
    Z3_func_decl p = Z3_mk_func_decl(ctx,
                                      Z3_mk_string_symbol(ctx, "p"),
                                      1, domain, bool_sort);

    Z3_ast var_x = Z3_mk_bound(ctx, 0, int_sort);
    Z3_ast px    = Z3_mk_app(ctx, p, 1, &var_x);

    Z3_sort  bound_sorts[1] = { int_sort };
    Z3_symbol bound_names[1] = { Z3_mk_string_symbol(ctx, "x") };
    Z3_ast forall_px = Z3_mk_forall(ctx, 0,
                                     0, nullptr,
                                     1, bound_sorts, bound_names,
                                     px);

    Z3_solver_assert(ctx, s, forall_px);
    Z3_lbool result = Z3_solver_check(ctx, s);
    // forall x. p(x) is SAT: p can be interpreted as constantly true.
    SASSERT(result == Z3_L_TRUE);
    (void)result;

    Z3_solver_dec_ref(ctx, s);
    Z3_del_context(ctx);
}

/*
 * Test that the mk_fresh callback is invoked when the solver creates an
 * auxiliary context (e.g., for model-based quantifier instantiation), and that
 * no memory is leaked by the C API wrapper allocations made during the callback.
 *
 * When mk_fresh is called, the C API wrapper allocates api::context (~100 KB+)
 * and api_context_obj. If those were leaked, we would see hundreds of KB of
 * growth per run. The test verifies that no such systematic growth occurs.
 */
void tst_user_propagator_fresh() {
    // Warm up global one-time Z3 state (family-id tables, symbol caches, etc.)
    // so that subsequent measurements are not polluted by first-time init costs.
    run_propagator_fresh_once();

    // Measure memory before the actual test run.
    int64_t mem_before = (int64_t)memory::get_allocation_size();

    g_fresh_count = 0;
    run_propagator_fresh_once();

    int64_t mem_after = (int64_t)memory::get_allocation_size();
    int64_t delta = mem_after - mem_before;

    std::cout << "fresh callback invoked " << g_fresh_count << " time(s)\n";
    std::cout << "net memory delta: " << delta << " bytes\n";

    // The fresh callback must have been invoked at least once.
    SASSERT(g_fresh_count > 0);

    // An api::context (allocated in the C API fresh wrapper and stored as
    // m_api_context in theory_user_propagator) is at least ~100 KB as observed
    // in the first-run initialization cost. If it were not freed by
    // ~theory_user_propagator(), delta would be orders of magnitude larger.
    // The threshold of 4096 bytes tolerates minor fluctuations from Z3's
    // internal memory pools while still catching any real per-call leak.
    SASSERT(delta < 4096);
}

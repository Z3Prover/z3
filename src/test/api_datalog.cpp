/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_datalog.cpp

Abstract:

    Test API datalog/fixedpoint functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"

void tst_api_datalog() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Test 1: Z3_mk_finite_domain_sort and size functions
    {
        Z3_symbol name = Z3_mk_string_symbol(ctx, "Domain");
        Z3_sort finite_sort = Z3_mk_finite_domain_sort(ctx, name, 5);
        ENSURE(finite_sort != nullptr);

        uint64_t size;
        bool success = Z3_get_finite_domain_sort_size(ctx, finite_sort, &size);
        ENSURE(success);
        ENSURE(size == 5);

        // Test with non-finite domain sort (should fail)
        Z3_sort int_sort = Z3_mk_int_sort(ctx);
        uint64_t wrong_size;
        bool wrong_success = Z3_get_finite_domain_sort_size(ctx, int_sort, &wrong_size);
        ENSURE(!wrong_success);
    }

    // Test 2: Z3_mk_fixedpoint basic operations
    {
        Z3_fixedpoint fp = Z3_mk_fixedpoint(ctx);
        ENSURE(fp != nullptr);

        Z3_fixedpoint_inc_ref(ctx, fp);
        // Test string conversion (empty fixedpoint)
        Z3_string fp_str = Z3_fixedpoint_to_string(ctx, fp, 0, nullptr);
        ENSURE(fp_str != nullptr);

        // Test statistics
        Z3_stats stats = Z3_fixedpoint_get_statistics(ctx, fp);
        ENSURE(stats != nullptr);

        // Test reason unknown
        Z3_string reason = Z3_fixedpoint_get_reason_unknown(ctx, fp);
        (void)reason; // May be null

        Z3_fixedpoint_dec_ref(ctx, fp);
    }

    Z3_del_context(ctx);
}
/*++
Copyright (c) 2025 Daily Test Coverage Improver

Module Name:

    api_fpa.cpp

Abstract:

    Test API floating-point arithmetic functions

Author:

    Daily Test Coverage Improver 2025-09-17

Notes:

--*/
#include "api/z3.h"
#include "util/trace.h"
#include "util/debug.h"

void tst_api_fpa() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    // Test rounding mode sort creation
    {
        Z3_sort rm_sort = Z3_mk_fpa_rounding_mode_sort(ctx);
        ENSURE(rm_sort != nullptr);
        ENSURE(Z3_get_sort_kind(ctx, rm_sort) == Z3_ROUNDING_MODE_SORT);
    }

    // Test rounding mode constants
    {
        Z3_ast rne = Z3_mk_fpa_round_nearest_ties_to_even(ctx);
        Z3_ast rna = Z3_mk_fpa_round_nearest_ties_to_away(ctx);
        Z3_ast rtp = Z3_mk_fpa_round_toward_positive(ctx);
        Z3_ast rtn = Z3_mk_fpa_round_toward_negative(ctx);
        Z3_ast rtz = Z3_mk_fpa_round_toward_zero(ctx);

        // Test short aliases too
        Z3_ast rne_short = Z3_mk_fpa_rne(ctx);
        Z3_ast rna_short = Z3_mk_fpa_rna(ctx);
        Z3_ast rtp_short = Z3_mk_fpa_rtp(ctx);
        Z3_ast rtn_short = Z3_mk_fpa_rtn(ctx);
        Z3_ast rtz_short = Z3_mk_fpa_rtz(ctx);

        ENSURE(rne != nullptr);
        ENSURE(rna != nullptr);
        ENSURE(rtp != nullptr);
        ENSURE(rtn != nullptr);
        ENSURE(rtz != nullptr);
        ENSURE(rne_short != nullptr);
        ENSURE(rna_short != nullptr);
        ENSURE(rtp_short != nullptr);
        ENSURE(rtn_short != nullptr);
        ENSURE(rtz_short != nullptr);
    }

    // Test floating-point sort creation
    {
        // Standard precision sorts
        Z3_sort fp_half = Z3_mk_fpa_sort_half(ctx);
        Z3_sort fp_16 = Z3_mk_fpa_sort_16(ctx);
        Z3_sort fp_single = Z3_mk_fpa_sort_single(ctx);
        Z3_sort fp_32 = Z3_mk_fpa_sort_32(ctx);
        Z3_sort fp_double = Z3_mk_fpa_sort_double(ctx);
        Z3_sort fp_64 = Z3_mk_fpa_sort_64(ctx);
        Z3_sort fp_quadruple = Z3_mk_fpa_sort_quadruple(ctx);
        Z3_sort fp_128 = Z3_mk_fpa_sort_128(ctx);

        ENSURE(fp_half != nullptr);
        ENSURE(fp_16 != nullptr);
        ENSURE(fp_single != nullptr);
        ENSURE(fp_32 != nullptr);
        ENSURE(fp_double != nullptr);
        ENSURE(fp_64 != nullptr);
        ENSURE(fp_quadruple != nullptr);
        ENSURE(fp_128 != nullptr);

        ENSURE(Z3_get_sort_kind(ctx, fp_single) == Z3_FLOATING_POINT_SORT);
        ENSURE(Z3_get_sort_kind(ctx, fp_double) == Z3_FLOATING_POINT_SORT);

        // Custom precision sorts
        Z3_sort fp11_7 = Z3_mk_fpa_sort(ctx, 11, 7);
        Z3_sort fp8_24 = Z3_mk_fpa_sort(ctx, 8, 24);
        ENSURE(fp11_7 != nullptr);
        ENSURE(fp8_24 != nullptr);
    }

    // Test floating-point constants
    {
        Z3_sort fp_sort = Z3_mk_fpa_sort_single(ctx);

        Z3_ast nan = Z3_mk_fpa_nan(ctx, fp_sort);
        Z3_ast pos_inf = Z3_mk_fpa_inf(ctx, fp_sort, false);
        Z3_ast neg_inf = Z3_mk_fpa_inf(ctx, fp_sort, true);
        Z3_ast pos_zero = Z3_mk_fpa_zero(ctx, fp_sort, false);
        Z3_ast neg_zero = Z3_mk_fpa_zero(ctx, fp_sort, true);

        ENSURE(nan != nullptr);
        ENSURE(pos_inf != nullptr);
        ENSURE(neg_inf != nullptr);
        ENSURE(pos_zero != nullptr);
        ENSURE(neg_zero != nullptr);
    }

    // Test basic numeral creation
    {
        Z3_sort fp_sort = Z3_mk_fpa_sort_single(ctx);
        Z3_sort fp_double = Z3_mk_fpa_sort_double(ctx);

        Z3_ast fp_from_float = Z3_mk_fpa_numeral_float(ctx, 3.14f, fp_sort);
        Z3_ast fp_from_double = Z3_mk_fpa_numeral_double(ctx, 2.71828, fp_double);
        Z3_ast fp_from_int = Z3_mk_fpa_numeral_int(ctx, 42, fp_sort);

        ENSURE(fp_from_float != nullptr);
        ENSURE(fp_from_double != nullptr);
        ENSURE(fp_from_int != nullptr);
    }

    // Test basic arithmetic operations
    {
        Z3_sort fp_sort = Z3_mk_fpa_sort_single(ctx);
        Z3_ast rm = Z3_mk_fpa_rne(ctx);

        Z3_ast fp1 = Z3_mk_fpa_numeral_float(ctx, 3.5f, fp_sort);
        Z3_ast fp2 = Z3_mk_fpa_numeral_float(ctx, 2.5f, fp_sort);

        // Unary operations
        Z3_ast abs_fp = Z3_mk_fpa_abs(ctx, fp1);
        Z3_ast neg_fp = Z3_mk_fpa_neg(ctx, fp1);

        // Binary operations with rounding mode
        Z3_ast add_fp = Z3_mk_fpa_add(ctx, rm, fp1, fp2);
        Z3_ast sub_fp = Z3_mk_fpa_sub(ctx, rm, fp1, fp2);
        Z3_ast mul_fp = Z3_mk_fpa_mul(ctx, rm, fp1, fp2);
        Z3_ast div_fp = Z3_mk_fpa_div(ctx, rm, fp1, fp2);

        // Binary operations without rounding mode
        Z3_ast min_fp = Z3_mk_fpa_min(ctx, fp1, fp2);
        Z3_ast max_fp = Z3_mk_fpa_max(ctx, fp1, fp2);
        Z3_ast rem_fp = Z3_mk_fpa_rem(ctx, fp1, fp2);

        ENSURE(abs_fp != nullptr);
        ENSURE(neg_fp != nullptr);
        ENSURE(add_fp != nullptr);
        ENSURE(sub_fp != nullptr);
        ENSURE(mul_fp != nullptr);
        ENSURE(div_fp != nullptr);
        ENSURE(min_fp != nullptr);
        ENSURE(max_fp != nullptr);
        ENSURE(rem_fp != nullptr);
    }

    // Test comparison operations
    {
        Z3_sort fp_sort = Z3_mk_fpa_sort_single(ctx);
        Z3_ast fp1 = Z3_mk_fpa_numeral_float(ctx, 3.5f, fp_sort);
        Z3_ast fp2 = Z3_mk_fpa_numeral_float(ctx, 2.5f, fp_sort);

        Z3_ast leq = Z3_mk_fpa_leq(ctx, fp1, fp2);
        Z3_ast lt = Z3_mk_fpa_lt(ctx, fp1, fp2);
        Z3_ast geq = Z3_mk_fpa_geq(ctx, fp1, fp2);
        Z3_ast gt = Z3_mk_fpa_gt(ctx, fp1, fp2);
        Z3_ast eq = Z3_mk_fpa_eq(ctx, fp1, fp2);

        ENSURE(leq != nullptr);
        ENSURE(lt != nullptr);
        ENSURE(geq != nullptr);
        ENSURE(gt != nullptr);
        ENSURE(eq != nullptr);
    }

    // Test predicate operations
    {
        Z3_sort fp_sort = Z3_mk_fpa_sort_single(ctx);
        Z3_ast fp = Z3_mk_fpa_numeral_float(ctx, 3.5f, fp_sort);
        Z3_ast nan = Z3_mk_fpa_nan(ctx, fp_sort);
        Z3_ast inf = Z3_mk_fpa_inf(ctx, fp_sort, false);
        Z3_ast zero = Z3_mk_fpa_zero(ctx, fp_sort, false);

        Z3_ast is_normal = Z3_mk_fpa_is_normal(ctx, fp);
        Z3_ast is_subnormal = Z3_mk_fpa_is_subnormal(ctx, fp);
        Z3_ast is_zero = Z3_mk_fpa_is_zero(ctx, zero);
        Z3_ast is_infinite = Z3_mk_fpa_is_infinite(ctx, inf);
        Z3_ast is_nan = Z3_mk_fpa_is_nan(ctx, nan);
        Z3_ast is_negative = Z3_mk_fpa_is_negative(ctx, fp);
        Z3_ast is_positive = Z3_mk_fpa_is_positive(ctx, fp);

        ENSURE(is_normal != nullptr);
        ENSURE(is_subnormal != nullptr);
        ENSURE(is_zero != nullptr);
        ENSURE(is_infinite != nullptr);
        ENSURE(is_nan != nullptr);
        ENSURE(is_negative != nullptr);
        ENSURE(is_positive != nullptr);
    }

    // Test basic conversion operations
    {
        Z3_sort fp_sort = Z3_mk_fpa_sort_single(ctx);
        Z3_ast rm = Z3_mk_fpa_rne(ctx);
        Z3_ast fp = Z3_mk_fpa_numeral_float(ctx, 3.5f, fp_sort);

        // Simple conversions that are likely to work
        Z3_ast real_from_fp = Z3_mk_fpa_to_real(ctx, fp);
        Z3_ast ieee_bv_from_fp = Z3_mk_fpa_to_ieee_bv(ctx, fp);
        Z3_ast ubv_from_fp = Z3_mk_fpa_to_ubv(ctx, rm, fp, 32);

        ENSURE(real_from_fp != nullptr);
        ENSURE(ieee_bv_from_fp != nullptr);
        ENSURE(ubv_from_fp != nullptr);
    }

    Z3_del_context(ctx);
}
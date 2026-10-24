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
#include <cstring>

static Z3_lbool run_fixedpoint(Z3_context ctx, char const* benchmark, Z3_params params) {
    Z3_fixedpoint fp = Z3_mk_fixedpoint(ctx);
    ENSURE(fp != nullptr);
    Z3_fixedpoint_inc_ref(ctx, fp);
    Z3_fixedpoint_set_params(ctx, fp, params);

    Z3_ast_vector queries = Z3_fixedpoint_from_string(ctx, fp, benchmark);
    ENSURE(queries != nullptr);
    ENSURE(Z3_get_error_code(ctx) == Z3_OK);
    ENSURE(Z3_ast_vector_size(ctx, queries) == 1);
    Z3_set_error_handler(ctx, [](Z3_context, Z3_error_code) {});
    Z3_lbool result = Z3_fixedpoint_query(ctx, fp, Z3_ast_vector_get(ctx, queries, 0));
    Z3_error_code error = Z3_get_error_code(ctx);
    ENSURE(error == Z3_OK ||
           (error == Z3_EXCEPTION &&
            std::strcmp(Z3_get_error_msg(ctx, error), "max. resource limit exceeded") == 0));
    Z3_fixedpoint_dec_ref(ctx, fp);
    return result;
}

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

    // Regression test for Spacer model construction on ADT CHCs
    {
        Z3_config cfg2 = Z3_mk_config();
        Z3_context ctx2 = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);

        char const* chc =
            "(declare-datatypes ((L 0)) (((cons (hd Int) (tl L)) (nil))))\n"
            "(declare-rel reva (L L L))\n"
            "(declare-rel fail ())\n"
            "(rule (forall ((a L)) (reva nil a a)))\n"
            "(rule (forall ((x L) (acc L) (r L) (h Int))\n"
            "  (=> (reva x (cons h acc) r)\n"
            "      (reva (cons h x) acc r))))\n"
            "(rule (forall ((B L) (C L) (D L) (E L) (F L))\n"
            "  (=> (and (reva B C D)\n"
            "           (reva D nil E)\n"
            "           (reva C B F)\n"
            "           (not (= E F)))\n"
            "      fail)))\n"
            "(query fail)\n";

        Z3_params params = Z3_mk_params(ctx2);
        Z3_params_inc_ref(ctx2, params);
        Z3_params_set_symbol(ctx2, params, Z3_mk_string_symbol(ctx2, "engine"),
                            Z3_mk_string_symbol(ctx2, "spacer"));
        Z3_params_set_uint(ctx2, params, Z3_mk_string_symbol(ctx2, "spacer.random_seed"), 51);
        Z3_params_set_uint(ctx2, params, Z3_mk_string_symbol(ctx2, "rlimit"), 100000);
        (void)run_fixedpoint(ctx2, chc, params);
        Z3_params_dec_ref(ctx2, params);
        Z3_del_context(ctx2);
    }

    // Regression test for assertion violation in Spacer QE projection (#3845)
    {
        Z3_config cfg3 = Z3_mk_config();
        Z3_context ctx3 = Z3_mk_context(cfg3);
        Z3_del_config(cfg3);

        char const* chc = R"(
(declare-rel a (Int Bool Int Bool))
(declare-rel c (Int Int Bool Bool Int Int Int Int Bool Bool Bool Int Int Bool Bool Int Int Int Int Bool Bool Bool))
(declare-rel d (Bool Bool Bool Int Bool Int Int Bool Bool Int Int Int Int Bool Bool Bool Int Int Bool Bool Int Int Int Int Bool Bool Bool))
(declare-rel e (Int Int Bool Bool Int Int Int Int Bool Bool Bool Bool))
(declare-rel fail ())
(rule (forall ((ef Int) (eaa Int) (eabacad Bool) (eabacg Bool)) (=> eabacad (a eaa eabacg ef eabacad))))
(rule
 (forall ((no Int)
     (naf Int)
     (nphl Bool)
     (nphiacg Bool)
     (nphq Bool)
     (nphiacad Bool)
     (nrsag Int)
     (nrsah Int)
     (nrst Int)
     (nrsai Int)
     (nrsuacg Bool)
     (nrsv Int)
     (nrsw Int)
     (nrsx Int)
     (nrsaj Int)
     (nrsuacad Bool)
     (nyacad Bool)
     (nzeaa Int)
     (nzeabacg Bool)
     (nzef Int)
     (nzeabacad Bool)
     (nyacg Bool))
 (=> (a nzeaa nzeabacg nzef nzeabacad)
  (c naf nzeaa nzeabacg nyacg nrsag nrsah nrst nrsai nrsuacg nphl nphiacg no nzef
  nzeabacad nyacad nrsv nrsw nrsx nrsaj nrsuacad nphq nphiacad))))
(rule
 (forall ((nak Bool)
     (nal Bool)
     (nam Bool)
     (nphl Bool)
     (nphiacg Bool)
     (ninit_invalid_s Int)
     (nao Bool)
     (nphae Bool)
     (nphiacj Bool)
     (nrsag Int)
     (nrsah Int)
     (nrst Int)
     (nrsai Int)
     (nrsuacg Bool)
     (nap Int)
     (nrsaq Int)
     (nrsar Int)
     (nrsas Int)
     (nrs__synapse_5_x Int)
     (nrsuacj Bool)
     (nyacg Bool)
     (nyacj Bool)
     (naf Int)
     (nat Int)
     (nzeaa Int)
     (nzeabacg Bool)
     (nau Int)
     (nzeav Int)
     (nzeabacj Bool)
     (naw Bool))
 (let ((ax (=> nao (< nap 0 nau))))
  (let ((ay (= naw ax)))
  (=> ay (d nak nal nam ninit_invalid_s naw naf nzeaa nzeabacg nyacg nrsag nrsah nrst nrsai
      nrsuacg nphl nphiacg nat nzeav nzeabacj nyacj nrsaq nrsar nrsas nrs__synapse_5_x nrsuacj nphae nphiacj))))))
(rule
 (forall ((naf Int)
     (nzeaa Int)
     (nzeabacg Bool)
     (nyacg Bool)
     (nrsag Int)
     (nrsah Int)
     (nrst Int)
     (nrsai Int)
     (nrsuacg Bool)
     (nphl Bool)
     (nphiacg Bool)
     (no Int)
     (nzef Int)
     (nzeabacad Bool)
     (nyacad Bool)
     (nrsv Int)
     (nrsw Int)
     (nrsx Int)
     (nrsaj Int)
     (nrsuacad Bool)
     (nphq Bool)
     (nphiacad Bool)
     (nak Bool)
     (nal Bool)
     (nam Bool)
     (ninit_invalid_s Int)
     (naw Bool)
     (nat Int)
     (nzeav Int)
     (nzeabacj Bool)
     (nyacj Bool)
     (nrsaq Int)
     (nrsar Int)
     (nrsas Int)
     (nrs__synapse_5_x Int)
     (nrsuacj Bool)
     (nphae Bool)
     (nphiacj Bool))
 (=> (c naf nzeaa nzeabacg nyacg nrsag nrsah nrst nrsai nrsuacg nphl nphiacg no nzef nzeabacad
    nyacad nrsv nrsw nrsx nrsaj nrsuacad nphq nphiacad)
  (d nak nal nam ninit_invalid_s naw no nzef nzeabacad nyacad nrsv nrsw nrsx nrsaj nrsuacad nphq
  nphiacad nat nzeav nzeabacj nyacj nrsaq nrsar nrsas nrs__synapse_5_x nrsuacj nphae nphiacj)
  (e nat nzeav nzeabacj nyacj nrsaq nrsar nrsas nrs__synapse_5_x nrsuacj nphae nphiacj naw))))
(rule
 (forall ((naw Bool)
     (nat Int)
     (nzeav Int)
     (nzeabacj Bool)
     (nyacj Bool)
     (nrsaq Int)
     (nrsar Int)
     (nrsas Int)
     (nrs__synapse_5_x Int)
     (nrsuacj Bool)
     (nphae Bool)
     (nphiacj Bool))
 (=> (e nat nzeav nzeabacj nyacj nrsaq nrsar nrsas nrs__synapse_5_x nrsuacj nphae nphiacj naw)
     fail)))
(query fail)
)";

        Z3_params params = Z3_mk_params(ctx3);
        Z3_params_inc_ref(ctx3, params);
        Z3_params_set_symbol(ctx3, params, Z3_mk_string_symbol(ctx3, "engine"),
                            Z3_mk_string_symbol(ctx3, "spacer"));
        Z3_params_set_bool(ctx3, params, Z3_mk_string_symbol(ctx3, "xform.inline_eager"), false);
        Z3_params_set_bool(ctx3, params, Z3_mk_string_symbol(ctx3, "spacer.native_mbp"), false);
        Z3_params_set_bool(ctx3, params, Z3_mk_string_symbol(ctx3, "spacer.reach_dnf"), false);
        Z3_params_set_uint(ctx3, params, Z3_mk_string_symbol(ctx3, "rlimit"), 100000);
        (void)run_fixedpoint(ctx3, chc, params);
        Z3_params_dec_ref(ctx3, params);
        Z3_del_context(ctx3);
    }

    // Regression test for a reachable error incorrectly reported safe (#11216).
    {
        char const* chc = R"(
(declare-rel Inv (Bool Int))
(declare-rel Err ())
(declare-var b Bool)
(declare-var b1 Bool)
(declare-var x Int)
(declare-var x1 Int)
(declare-var f Int)
(declare-var g Int)
(declare-var h Int)
(declare-var i Int)
(declare-var j Bool)
(declare-var k Bool)
(declare-var l Bool)
(rule (=> (and (= x 0) (not b)) (Inv b x)))
(rule (=> (Inv b x) (Inv b1 x1)))
(rule (=> (and (Inv b x)
               b
               (= (+ (ite l 0 (ite (<= 1 h) 1 f))
                     (ite (<= 1 i) 0 h)
                     (ite l (+ g h f) (ite (<= 1 g) g 0))
                     (ite l (ite (<= 1 i) 0 i)
                            (ite (or k (not (and j (<= 1 g)))) i g)))
                  1))
          Err))
(query Err)
)";
        Z3_params params = Z3_mk_params(ctx);
        Z3_params_inc_ref(ctx, params);
        Z3_params_set_symbol(ctx, params, Z3_mk_string_symbol(ctx, "engine"),
                            Z3_mk_string_symbol(ctx, "spacer"));
        ENSURE(run_fixedpoint(ctx, chc, params) == Z3_L_TRUE);
        Z3_params_dec_ref(ctx, params);
    }

    Z3_del_context(ctx);
}

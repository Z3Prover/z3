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

    // Regression test for Spacer model construction on ADT CHCs
    {
        Z3_config cfg2 = Z3_mk_config();
        Z3_context ctx2 = Z3_mk_context(cfg2);
        Z3_del_config(cfg2);

        char const* chc =
            "(set-logic HORN)\n"
            "(set-option :fp.engine spacer)\n"
            "(set-option :fp.spacer.random_seed 51)\n"
            "(set-option :timeout 2000)\n"
            "(declare-datatypes ((L 0)) (((cons (hd Int) (tl L)) (nil))))\n"
            "(declare-fun reva (L L L) Bool)\n"
            "(assert (forall ((a L)) (reva nil a a)))\n"
            "(assert (forall ((x L) (acc L) (r L) (h Int))\n"
            "  (=> (reva x (cons h acc) r)\n"
            "      (reva (cons h x) acc r))))\n"
            "(assert (forall ((B L) (C L) (D L) (E L) (F L))\n"
            "  (=> (and (reva B C D)\n"
            "           (reva D nil E)\n"
            "           (reva C B F)\n"
            "           (not (= E F)))\n"
            "      false)))\n"
            "(check-sat)\n";

        Z3_string response = Z3_eval_smtlib2_string(ctx2, chc);
        ENSURE(response != nullptr);
        ENSURE(Z3_get_error_code(ctx2) == Z3_OK);
        Z3_del_context(ctx2);
    }

    // Regression test for assertion violation in Spacer QE projection (#3845)
    {
        Z3_config cfg3 = Z3_mk_config();
        Z3_context ctx3 = Z3_mk_context(cfg3);
        Z3_del_config(cfg3);

        char const* chc = R"(
(set-logic HORN)
(set-option :fp.xform.inline_eager false)
(set-option :fp.spacer.native_mbp false)
(set-option :fp.spacer.reach_dnf false)
(declare-fun a (Int Bool Int Bool) Bool)
(declare-fun c (Int Int Bool Bool Int Int Int Int Bool Bool Bool Int Int Bool Bool Int Int Int Int Bool Bool Bool) Bool)
(declare-fun d (Bool Bool Bool Int Bool Int Int Bool Bool Int Int Int Int Bool Bool Bool Int Int Bool Bool Int Int Int Int Bool Bool Bool) Bool)
(declare-fun e (Int Int Bool Bool Int Int Int Int Bool Bool Bool Bool) Bool)
(assert (forall ((ef Int) (eaa Int) (eabacad Bool) (eabacg Bool)) (=> eabacad (a eaa eabacg ef eabacad))))
(assert
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
(assert
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
(assert
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
(assert
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
 (not (e nat nzeav nzeabacj nyacj nrsaq nrsar nrsas nrs__synapse_5_x nrsuacj nphae nphiacj naw))))
(check-sat)
)";

        Z3_string response = Z3_eval_smtlib2_string(ctx3, chc);
        ENSURE(response != nullptr);
        ENSURE(Z3_get_error_code(ctx3) == Z3_OK);
        Z3_del_context(ctx3);
    }

    Z3_del_context(ctx);
}

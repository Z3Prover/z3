
/*++
Copyright (c) 2026 Microsoft Corporation

--*/

#include "api/z3.h"
#include "util/debug.h"
#include <iostream>
#include <string>

static void test_rem_subnormal_divisor() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    char const* spec =
        "(declare-const x (_ FloatingPoint 5 11))\n"
        "(declare-const y (_ FloatingPoint 5 11))\n"
        "(assert (= x ((_ to_fp 5 11) #b1110100000101010)))\n"
        "(assert (= y ((_ to_fp 5 11) #b1000000000010101)))\n"
        "(assert (not (= ((_ fp.to_ieee_bv 16) (fp.rem x y)) #x000a)))\n"
        "(check-sat-using (then fpa2bv simplify bit-blast smt))\n";

    std::string response = Z3_eval_smtlib2_string(ctx, spec);
    if (response.find("unsat") == std::string::npos)
        std::cout << response << "\n";
    ENSURE(response.find("unsat") != std::string::npos);

    Z3_del_context(ctx);
}

void tst_fpa() {
    test_rem_subnormal_divisor();
}

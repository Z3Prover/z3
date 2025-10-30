/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nra_tactic.cpp

Abstract:

    Tactic for NRA

Author:

    Leonardo (leonardo) 2012-03-13

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/nnf_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "qe/qe_tactic.h"
#include "qe/nlqsat.h"
#include "qe/lite/qe_lite_tactic.h"
#include "nlsat/tactic/qfnra_nlsat_tactic.h"

tactic * mk_nra_tactic(ast_manager & m, params_ref const& p) {
    params_ref p1 = p;
    p1.set_uint("seed", 11);
    p1.set_bool("factor", false);
    params_ref p2 = p;
    p2.set_uint("seed", 13);
    p2.set_bool("factor", false);

    tactic* simplify1 = mk_simplify_tactic(m, p);
    tactic* propagate = mk_propagate_values_tactic(m, p);
    tactic* qe_lite = mk_qe_lite_tactic(m);
    tactic* simplify2 = mk_simplify_tactic(m, p);

    tactic* qfnra_main = mk_qfnra_nlsat_tactic(m, p);
    tactic* try_qfnra_main = try_for(qfnra_main, 5000);
    tactic* qfnra_alt1 = mk_qfnra_nlsat_tactic(m, p1);
    tactic* try_qfnra_alt1 = try_for(qfnra_alt1, 10000);
    tactic* qfnra_alt2 = mk_qfnra_nlsat_tactic(m, p2);
    tactic* qfnra_branch = or_else(try_qfnra_main, try_qfnra_alt1, qfnra_alt2);

    tactic* nlqsat = mk_nlqsat_tactic(m, p);
    tactic* smt = mk_smt_tactic(m, p);
    tactic* fallback_branch = or_else(nlqsat, smt);

    probe* qfnra_probe = mk_is_qfnra_probe();
    tactic* conditional = cond(qfnra_probe, qfnra_branch, fallback_branch);

    return and_then(
        simplify1,
        propagate,
        qe_lite,
        simplify2,
        conditional);
}


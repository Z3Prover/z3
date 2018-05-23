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
#include "smt/tactic/smt_tactic.h"
#include "qe/qe_tactic.h"
#include "qe/nlqsat.h"
#include "qe/qe_lite.h"
#include "nlsat/tactic/qfnra_nlsat_tactic.h"

tactic * mk_nra_tactic(ast_manager & m, params_ref const& p) {
    params_ref p1 = p;
    p1.set_uint("seed", 11);
    p1.set_bool("factor", false);
    params_ref p2 = p;
    p2.set_uint("seed", 13);
    p2.set_bool("factor", false);

    return and_then(
        mk_simplify_tactic(m, p),
        mk_propagate_values_tactic(m, p),
        mk_qe_lite_tactic(m),
        cond(mk_is_qfnra_probe(),
             or_else(try_for(mk_qfnra_nlsat_tactic(m, p), 5000),
                     try_for(mk_qfnra_nlsat_tactic(m, p1), 10000),
                     mk_qfnra_nlsat_tactic(m, p2)),
             or_else(mk_nlqsat_tactic(m, p),
                     mk_smt_tactic(p))
             ));
}



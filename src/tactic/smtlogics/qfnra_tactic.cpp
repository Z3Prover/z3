/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_tactic.cpp

Abstract:

    Tactic for QF_NRA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/arith/nla2bv_tactic.h"
#include "nlsat/tactic/qfnra_nlsat_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"

static tactic * mk_qfnra_sat_solver(ast_manager& m, params_ref const& p, unsigned bv_size) {
    params_ref nra2sat_p = p;
    nra2sat_p.set_uint("nla2bv_max_bv_size", p.get_uint("nla2bv_max_bv_size", bv_size));   
    
    return and_then(mk_nla2bv_tactic(m, nra2sat_p),
                    mk_smt_tactic(m),
                    mk_fail_if_undecided_tactic());
}

tactic * mk_qfnra_tactic(ast_manager & m, params_ref const& p) {
    params_ref p0 = p;
    p0.set_bool("inline_vars", true);
    params_ref p1 = p;    
    p1.set_uint("seed", 11);
    p1.set_bool("factor", false);
    params_ref p2 = p;
    p2.set_uint("seed", 13);
    p2.set_bool("factor", false);

    return and_then(mk_simplify_tactic(m, p), 
                    mk_propagate_values_tactic(m, p),
                    or_else(try_for(mk_qfnra_nlsat_tactic(m, p0), 5000),
                            try_for(mk_qfnra_nlsat_tactic(m, p1), 10000),
                            mk_qfnra_sat_solver(m, p, 4),
                            and_then(try_for(mk_smt_tactic(m), 5000), mk_fail_if_undecided_tactic()),
                            mk_qfnra_sat_solver(m, p, 6),
                            mk_qfnra_nlsat_tactic(m, p2)));
}



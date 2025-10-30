/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfidl_tactic.cpp

Abstract:

    Tactic for QF_IDL

Author:

    Leonardo (leonardo) 2012-02-21

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/arith/propagate_ineqs_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/arith/normalize_bounds_tactic.h"
#include "tactic/arith/fix_dl_var_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/arith/lia2pb_tactic.h"
#include "tactic/arith/pb2bv_tactic.h"
#include "tactic/arith/diff_neq_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/aig/aig_tactic.h"
#include "sat/tactic/sat_tactic.h"

#define BIG_PROBLEM 5000

tactic * mk_qfidl_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("blast_distinct", true);
    main_p.set_bool("som", true);

    params_ref lhs_p;
    lhs_p.set_bool("arith_lhs", true);

    params_ref lia2pb_p;
    lia2pb_p.set_uint("lia2pb_max_bits", 4);

    params_ref pb2bv_p;
    pb2bv_p.set_uint("pb2bv_all_clauses_limit", 8);

    params_ref pull_ite_p;
    pull_ite_p.set_bool("pull_cheap_ite", true);
    pull_ite_p.set_bool("local_ctx", true);
    pull_ite_p.set_uint("local_ctx_limit", 10000000);

    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* fix_dl = mk_fix_dl_var_tactic(m);
    tactic* propagate1 = mk_propagate_values_tactic(m);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);
    tactic* phase1 = and_then(simplify1,
                              fix_dl,
                              propagate1,
                              elim_unc);

    tactic* solve_eqs1 = mk_solve_eqs_tactic(m);
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify_with_lhs = using_params(simplify2, lhs_p);
    tactic* propagate2 = mk_propagate_values_tactic(m);
    tactic* normalize_bounds = mk_normalize_bounds_tactic(m);
    tactic* solve_eqs2 = mk_solve_eqs_tactic(m);
    tactic* phase2 = and_then(solve_eqs1,
                              simplify_with_lhs,
                              propagate2,
                              normalize_bounds,
                              solve_eqs2);

    tactic * preamble_st = and_then(phase1, phase2);

    
    
    params_ref bv_solver_p;
    // The cardinality constraint encoding generates a lot of shared if-then-else's that can be flattened.
    // Several of them are simplified to and/or. If we flat them, we increase a lot the memory consumption.
    bv_solver_p.set_bool("flat", false); 
    bv_solver_p.set_bool("som", false); 
    // dynamic psm seems to work well.
    bv_solver_p.set_sym("gc", symbol("dyn_psm"));

    tactic* simplify3 = mk_simplify_tactic(m);
    tactic* propagate3 = mk_propagate_values_tactic(m);
    tactic* solve_eqs3 = mk_solve_eqs_tactic(m);
    tactic* max_sharing = mk_max_bv_sharing_tactic(m);
    tactic* bit_blaster = mk_bit_blaster_tactic(m);
    tactic* aig = mk_aig_tactic();
    tactic* sat = mk_sat_tactic(m);
    tactic* bv_solver_core = and_then(simplify3,
                                      propagate3,
                                      solve_eqs3,
                                      max_sharing,
                                      bit_blaster,
                                      aig,
                                      sat);
    tactic * bv_solver = using_params(bv_solver_core, bv_solver_p);

    tactic * try2bv = 
        and_then(using_params(mk_lia2pb_tactic(m), lia2pb_p),
                 mk_propagate_ineqs_tactic(m),
                 using_params(mk_pb2bv_tactic(m), pb2bv_p),
                 fail_if(mk_not(mk_is_qfbv_probe())),
                 bv_solver);
    
    params_ref diff_neq_p;
    diff_neq_p.set_uint("diff_neq_max_k", 25);

    probe* num_consts = mk_num_consts_probe();
    probe* const_limit = mk_const_probe(static_cast<double>(BIG_PROBLEM));
    probe* few_consts = mk_lt(num_consts, const_limit);
    probe* produce_proofs = mk_produce_proofs_probe();
    probe* produce_unsat = mk_produce_unsat_cores_probe();
    probe* no_proofs = mk_not(produce_proofs);
    probe* no_unsat = mk_not(produce_unsat);
    probe* no_proofs_or_unsat = mk_and(no_proofs, no_unsat);
    probe* small_problem = mk_and(few_consts, no_proofs_or_unsat);

    tactic* diff_neq = mk_diff_neq_tactic(m);
    tactic* diff_neq_with_params = using_params(diff_neq, diff_neq_p);
    tactic* smt_default = mk_smt_tactic(m);
    tactic* branch_solver = or_else(diff_neq_with_params,
                                    try2bv,
                                    smt_default);
    tactic* main_branch = using_params(and_then(preamble_st, branch_solver), main_p);

    tactic * st = cond(small_problem,
                       main_branch,
                       smt_default);
    
    st->updt_params(p);

    return st;
}

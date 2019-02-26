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
#include "smt/tactic/smt_tactic.h"
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

    tactic * preamble_st = and_then(and_then(mk_simplify_tactic(m),
                                             mk_fix_dl_var_tactic(m),
                                             mk_propagate_values_tactic(m),
                                             mk_elim_uncnstr_tactic(m)
                                             ),
                                    and_then(mk_solve_eqs_tactic(m),
                                             using_params(mk_simplify_tactic(m), lhs_p),
                                             mk_propagate_values_tactic(m),
                                             mk_normalize_bounds_tactic(m),
                                             mk_solve_eqs_tactic(m)));

    
    
    params_ref bv_solver_p;
    // The cardinality constraint encoding generates a lot of shared if-then-else's that can be flattened.
    // Several of them are simplified to and/or. If we flat them, we increase a lot the memory consumption.
    bv_solver_p.set_bool("flat", false); 
    bv_solver_p.set_bool("som", false); 
    // dynamic psm seems to work well.
    bv_solver_p.set_sym("gc", symbol("dyn_psm"));

    tactic * bv_solver = using_params(and_then(mk_simplify_tactic(m),
                                               mk_propagate_values_tactic(m),
                                               mk_solve_eqs_tactic(m),
                                               mk_max_bv_sharing_tactic(m),
                                               mk_bit_blaster_tactic(m),
                                               mk_aig_tactic(),
                                               mk_sat_tactic(m)),
                                      bv_solver_p);

    tactic * try2bv = 
        and_then(using_params(mk_lia2pb_tactic(m), lia2pb_p),
                 mk_propagate_ineqs_tactic(m),
                 using_params(mk_pb2bv_tactic(m), pb2bv_p),
                 fail_if(mk_not(mk_is_qfbv_probe())),
                 bv_solver);
    
    params_ref diff_neq_p;
    diff_neq_p.set_uint("diff_neq_max_k", 25);

    tactic * st = cond(mk_and(mk_lt(mk_num_consts_probe(), mk_const_probe(static_cast<double>(BIG_PROBLEM))),
                              mk_and(mk_not(mk_produce_proofs_probe()),
                                     mk_not(mk_produce_unsat_cores_probe()))),
                       using_params(and_then(preamble_st,
                                             or_else(using_params(mk_diff_neq_tactic(m), diff_neq_p),
                                                     try2bv,
                                                     mk_smt_tactic(m))),
                                    main_p),
                       mk_smt_tactic(m));
    
    st->updt_params(p);

    return st;
}

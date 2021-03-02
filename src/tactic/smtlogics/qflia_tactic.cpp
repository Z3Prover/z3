/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qflia_tactic.cpp

Abstract:

    Tactic for QF_LIA

Author:

    Leonardo (leonardo) 2012-02-26

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/arith/propagate_ineqs_tactic.h"
#include "tactic/arith/normalize_bounds_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/arith/add_bounds_tactic.h"
#include "tactic/arith/pb2bv_tactic.h"
#include "tactic/arith/lia2pb_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/aig/aig_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "tactic/arith/bound_manager.h"
#include "tactic/arith/probe_arith.h"

struct quasi_pb_probe : public probe {
    result operator()(goal const & g) override {
        bool found_non_01 = false;
        bound_manager bm(g.m());
        bm(g);
        rational l, u; bool st;
        for (expr * t : bm) {
            if (bm.has_lower(t, l, st) && bm.has_upper(t, u, st) && (l.is_zero() || l.is_one()) && (u.is_zero() || u.is_one()))
                continue;
            if (found_non_01)
                return false;
            found_non_01 = true;
        }
        return true;
    }
};

probe * mk_is_quasi_pb_probe() {
    return mk_and(mk_not(mk_is_unbounded_probe()),
                  alloc(quasi_pb_probe));
}

// Create SMT solver that does not use cuts
static tactic * mk_no_cut_smt_tactic(ast_manager& m, unsigned rs) {
    params_ref solver_p;
    solver_p.set_sym(symbol("smt.logic"), symbol("QF_LIA")); // force smt_setup to use the new solver
    solver_p.set_uint("arith.branch_cut_ratio", 10000000);
    solver_p.set_uint("random_seed", rs);
    return annotate_tactic("no-cut-smt-tactic", using_params(mk_smt_tactic_using(m, false), solver_p));
}

// Create SMT solver that does not use cuts
static tactic * mk_no_cut_no_relevancy_smt_tactic(ast_manager& m, unsigned rs) {
    params_ref solver_p;
    solver_p.set_uint("arith.branch_cut_ratio", 10000000);
    solver_p.set_uint("random_seed", rs);
    solver_p.set_uint("relevancy", 0);
    return annotate_tactic("no-cut-relevancy-tactic", using_params(mk_smt_tactic_using(m, false), solver_p));
}

static tactic * mk_bv2sat_tactic(ast_manager & m) {
    params_ref solver_p;
    // The cardinality constraint encoding generates a lot of shared if-then-else's that can be flattened.
    // Several of them are simplified to and/or. If we flat them, we increase a lot the memory consumption.
    solver_p.set_bool("flat", false); 
    solver_p.set_bool("som", false); 
    // dynamic psm seems to work well.
    solver_p.set_sym("gc", symbol("dyn_psm"));
    
    return using_params(and_then(mk_simplify_tactic(m),
                                 mk_propagate_values_tactic(m),
                                 mk_solve_eqs_tactic(m),
                                 mk_max_bv_sharing_tactic(m),
                                 mk_bit_blaster_tactic(m),
                                 mk_aig_tactic(),
                                 mk_sat_tactic(m, solver_p)),
                        solver_p);
}

#define SMALL_SIZE 80000

static tactic * mk_pb_tactic(ast_manager & m) {
    params_ref pb2bv_p;    
    pb2bv_p.set_uint("pb2bv_all_clauses_limit", 8);

    params_ref bv2sat_p;
    bv2sat_p.set_bool("ite_extra", true);
    
    return annotate_tactic(
        "pb-tactic",
        and_then(fail_if_not(mk_is_pb_probe()),
                 fail_if(mk_produce_proofs_probe()),
                 fail_if(mk_produce_unsat_cores_probe()),
                 or_else(and_then(fail_if(mk_ge(mk_num_exprs_probe(), mk_const_probe(SMALL_SIZE))),
                                  fail_if_not(mk_is_ilp_probe()),
                                  // try_for(mk_mip_tactic(m), 8000),
                                  mk_fail_if_undecided_tactic()),
                         and_then(using_params(mk_pb2bv_tactic(m), pb2bv_p),
                                  fail_if_not(mk_is_qfbv_probe()),
                                  using_params(mk_bv2sat_tactic(m), bv2sat_p)))));
}


static tactic * mk_lia2sat_tactic(ast_manager & m) {
    params_ref pb2bv_p;
    pb2bv_p.set_uint("pb2bv_all_clauses_limit", 8);

    params_ref bv2sat_p;
    bv2sat_p.set_bool("ite_extra", true);
    
    return annotate_tactic(
        "lia2sat-tactic",
        and_then(fail_if(mk_is_unbounded_probe()),
                 fail_if(mk_produce_proofs_probe()),
                 fail_if(mk_produce_unsat_cores_probe()),
                 mk_propagate_ineqs_tactic(m),
                 mk_normalize_bounds_tactic(m),
                 mk_lia2pb_tactic(m),
                 using_params(mk_pb2bv_tactic(m), pb2bv_p),
                 fail_if_not(mk_is_qfbv_probe()),                    
                 using_params(mk_bv2sat_tactic(m), bv2sat_p)));
}

// Try to find a model for an unbounded ILP problem.
// Fails if the problem is no ILP.
static tactic * mk_ilp_model_finder_tactic(ast_manager & m) {
    params_ref add_bounds_p1;
    add_bounds_p1.set_rat("add_bound_lower", rational(-16));
    add_bounds_p1.set_rat("add_bound_upper", rational(15));
    params_ref add_bounds_p2;
    add_bounds_p2.set_rat("add_bound_lower", rational(-32));
    add_bounds_p2.set_rat("add_bound_upper", rational(31));

    return annotate_tactic(
        "ilp-model-finder-tactic",
        and_then(fail_if_not(mk_and(mk_is_ilp_probe(), mk_is_unbounded_probe())),
                 fail_if(mk_produce_proofs_probe()),
                 fail_if(mk_produce_unsat_cores_probe()),
                 mk_propagate_ineqs_tactic(m),
                 or_else(// try_for(mk_mip_tactic(m), 5000),
                     try_for(mk_no_cut_smt_tactic(m, 100), 2000),
                     and_then(using_params(mk_add_bounds_tactic(m), add_bounds_p1),
                              try_for(mk_lia2sat_tactic(m), 5000)),
                     try_for(mk_no_cut_smt_tactic(m, 200), 5000),
                     and_then(using_params(mk_add_bounds_tactic(m), add_bounds_p2),
                              try_for(mk_lia2sat_tactic(m), 10000))
                     // , mk_mip_tactic(m)
                         ),
                 mk_fail_if_undecided_tactic()));
}

static tactic * mk_bounded_tactic(ast_manager & m) {
    return annotate_tactic(
        "bounded-tactic",
        and_then(fail_if(mk_is_unbounded_probe()),
                 or_else(try_for(mk_no_cut_smt_tactic(m, 100), 5000),
                         try_for(mk_no_cut_no_relevancy_smt_tactic(m, 200), 5000),
                         try_for(mk_no_cut_smt_tactic(m, 300), 15000)
                         ),
                 mk_fail_if_undecided_tactic()));
}

tactic * mk_preamble_tactic(ast_manager& m) {

    params_ref pull_ite_p;
    pull_ite_p.set_bool("pull_cheap_ite", true);
    pull_ite_p.set_bool("push_ite_arith", false);
    pull_ite_p.set_bool("local_ctx", true);
    pull_ite_p.set_uint("local_ctx_limit", 10000000);
    pull_ite_p.set_bool("hoist_ite", true);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 30);
    ctx_simp_p.set_uint("max_steps", 5000000);

    params_ref lhs_p;
    lhs_p.set_bool("arith_lhs", true);

    tactic * preamble_st = and_then(mk_simplify_tactic(m),
                                    mk_propagate_values_tactic(m),
                                    using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                                    using_params(mk_simplify_tactic(m), pull_ite_p)
                                    );

    preamble_st = and_then(preamble_st,
                           mk_solve_eqs_tactic(m),
                           mk_elim_uncnstr_tactic(m),
                           using_params(mk_simplify_tactic(m), lhs_p) 
                           );

    return preamble_st;
}

tactic * mk_qflia_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("som", true);
    main_p.set_bool("blast_distinct", true);
    main_p.set_uint("blast_distinct_threshold", 128);
    // main_p.set_bool("push_ite_arith", true);
    


    params_ref quasi_pb_p;
    quasi_pb_p.set_uint("lia2pb_max_bits", 64);
    
    tactic * preamble_st = mk_preamble_tactic(m);

    tactic * st = using_params(and_then(preamble_st,
                                        or_else(mk_ilp_model_finder_tactic(m),
                                                mk_pb_tactic(m),
                                                and_then(fail_if_not(mk_is_quasi_pb_probe()), 
                                                         using_params(mk_lia2sat_tactic(m), quasi_pb_p),
                                                         mk_fail_if_undecided_tactic()),
                                                mk_bounded_tactic(m),
                                                mk_smt_tactic(m))),
                               main_p);

    
    st->updt_params(p);
    return st;
}


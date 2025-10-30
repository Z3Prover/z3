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
#include "tactic/arith/lia2card_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/aig/aig_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "ast/simplifiers/bound_manager.h"
#include "tactic/arith/probe_arith.h"

struct quasi_pb_probe : public probe {
    result operator()(goal const & g) override {
        bool found_non_01 = false;
        bound_manager bm(g.m());
        for (unsigned i = 0; i < g.size(); ++i)
            bm(g.form(i), g.dep(i), g.pr(i));
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
    
    tactic* simplify = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* solve_eqs = mk_solve_eqs_tactic(m);
    tactic* max_sharing = mk_max_bv_sharing_tactic(m);
    tactic* bit_blaster = mk_bit_blaster_tactic(m);
    tactic* aig = mk_aig_tactic();
    tactic* sat = mk_sat_tactic(m, solver_p);
    tactic* core = and_then(simplify,
                            propagate,
                            solve_eqs,
                            max_sharing,
                            bit_blaster,
                            aig,
                            sat);
    return using_params(core, solver_p);
}

#define SMALL_SIZE 80000

static tactic * mk_pb_tactic(ast_manager & m) {
    params_ref pb2bv_p;    
    pb2bv_p.set_uint("pb2bv_all_clauses_limit", 8);

    params_ref bv2sat_p;
    bv2sat_p.set_bool("ite_extra", true);
    
    probe* num_exprs = mk_num_exprs_probe();
    probe* size_limit = mk_const_probe(SMALL_SIZE);
    probe* too_large = mk_ge(num_exprs, size_limit);
    tactic* fail_large = fail_if(too_large);
    tactic* fail_not_ilp = fail_if_not(mk_is_ilp_probe());
    tactic* fail_undecided = mk_fail_if_undecided_tactic();
    tactic* branch1 = and_then(fail_large,
                               fail_not_ilp,
                               fail_undecided);

    tactic* pb2bv = mk_pb2bv_tactic(m);
    tactic* pb2bv_with_params = using_params(pb2bv, pb2bv_p);
    tactic* fail_not_qfbv = fail_if_not(mk_is_qfbv_probe());
    tactic* bv2sat = mk_bv2sat_tactic(m);
    tactic* bv2sat_with_params = using_params(bv2sat, bv2sat_p);
    tactic* branch2 = and_then(pb2bv_with_params,
                               fail_not_qfbv,
                               bv2sat_with_params);

    tactic* core = and_then(fail_if_not(mk_is_pb_probe()),
                            fail_if(mk_produce_proofs_probe()),
                            fail_if(mk_produce_unsat_cores_probe()),
                            or_else(branch1, branch2));

    return annotate_tactic("pb-tactic", core);
}


static tactic * mk_lia2sat_tactic(ast_manager & m) {
    params_ref pb2bv_p;
    pb2bv_p.set_uint("pb2bv_all_clauses_limit", 8);

    params_ref bv2sat_p;
    bv2sat_p.set_bool("ite_extra", true);
    
    tactic* fail_unbounded = fail_if(mk_is_unbounded_probe());
    tactic* fail_proofs = fail_if(mk_produce_proofs_probe());
    tactic* fail_unsat = fail_if(mk_produce_unsat_cores_probe());
    tactic* propagate_ineqs = mk_propagate_ineqs_tactic(m);
    tactic* normalize_bounds = mk_normalize_bounds_tactic(m);
    tactic* lia2pb = mk_lia2pb_tactic(m);
    tactic* pb2bv = mk_pb2bv_tactic(m);
    tactic* pb2bv_with_params = using_params(pb2bv, pb2bv_p);
    tactic* fail_not_qfbv = fail_if_not(mk_is_qfbv_probe());
    tactic* bv2sat = mk_bv2sat_tactic(m);
    tactic* bv2sat_with_params = using_params(bv2sat, bv2sat_p);

    tactic* core = and_then(fail_unbounded,
                            fail_proofs,
                            fail_unsat,
                            propagate_ineqs,
                            normalize_bounds,
                            lia2pb,
                            pb2bv_with_params,
                            fail_not_qfbv,
                            bv2sat_with_params);

    return annotate_tactic("lia2sat-tactic", core);
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

    probe* is_ilp = mk_is_ilp_probe();
    probe* is_unbounded = mk_is_unbounded_probe();
    probe* ilp_unbounded = mk_and(is_ilp, is_unbounded);
    tactic* fail_not_ilp_unbounded = fail_if_not(ilp_unbounded);
    tactic* fail_proofs = fail_if(mk_produce_proofs_probe());
    tactic* fail_unsat = fail_if(mk_produce_unsat_cores_probe());
    tactic* propagate_ineqs = mk_propagate_ineqs_tactic(m);

    tactic* add_bounds1 = mk_add_bounds_tactic(m);
    tactic* add_bounds1_params = using_params(add_bounds1, add_bounds_p1);
    tactic* lia2sat1 = try_for(mk_lia2sat_tactic(m), 5000);
    tactic* branch_bounds1 = and_then(add_bounds1_params, lia2sat1);

    tactic* add_bounds2 = mk_add_bounds_tactic(m);
    tactic* add_bounds2_params = using_params(add_bounds2, add_bounds_p2);
    tactic* lia2sat2 = try_for(mk_lia2sat_tactic(m), 10000);
    tactic* branch_bounds2 = and_then(add_bounds2_params, lia2sat2);

    tactic* branch_no_cut1 = try_for(mk_no_cut_smt_tactic(m, 100), 2000);
    tactic* branch_no_cut2 = try_for(mk_no_cut_smt_tactic(m, 200), 5000);
    tactic* or_branch = or_else(branch_no_cut1,
                                branch_bounds1,
                                branch_no_cut2,
                                branch_bounds2);

    tactic* fail_undecided = mk_fail_if_undecided_tactic();

    tactic* core = and_then(fail_not_ilp_unbounded,
                            fail_proofs,
                            fail_unsat,
                            propagate_ineqs,
                            or_branch,
                            fail_undecided);

    return annotate_tactic("ilp-model-finder-tactic", core);
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

    // only binary integer variables are converted to PB
    params_ref lia2card_p;
    lia2card_p.set_uint("lia2card.max_range", 1);
    lia2card_p.set_uint("lia2card.max_ite_nesting", 1);

    tactic* simplify = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* ctx_simplify = mk_ctx_simplify_tactic(m);
    tactic* ctx_simplify_with_params = using_params(ctx_simplify, ctx_simp_p);
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify_with_pull = using_params(simplify2, pull_ite_p);
    tactic* solve_eqs = mk_solve_eqs_tactic(m);
    tactic* lia2card = mk_lia2card_tactic(m, lia2card_p);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);

    return and_then(
        simplify,
        propagate,
        ctx_simplify_with_params,
        simplify_with_pull,
        solve_eqs,
        lia2card,
        elim_unc);
}

tactic * mk_qflia_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("som", true);
    main_p.set_bool("blast_distinct", true);
    main_p.set_uint("blast_distinct_threshold", 128);
    main_p.set_uint("lia2card.max_range", 1);
    main_p.set_uint("lia2card.max_ite_nesting", 1);
    // main_p.set_bool("push_ite_arith", true);
   
    params_ref quasi_pb_p;
    quasi_pb_p.set_uint("lia2pb_max_bits", 64);

    params_ref lhs_p;
    lhs_p.set_bool("arith_lhs", true);

    tactic* preamble = mk_preamble_tactic(m);
    tactic* simplify_lhs = using_params(mk_simplify_tactic(m), lhs_p);

    tactic* ilp_finder = mk_ilp_model_finder_tactic(m);
    tactic* pb_tac = mk_pb_tactic(m);
    tactic* fail_not_quasi = fail_if_not(mk_is_quasi_pb_probe());
    tactic* lia2sat = mk_lia2sat_tactic(m);
    tactic* lia2sat_with_params = using_params(lia2sat, quasi_pb_p);
    tactic* fail_undecided = mk_fail_if_undecided_tactic();
    tactic* quasi_branch = and_then(fail_not_quasi,
                                    lia2sat_with_params,
                                    fail_undecided);
    tactic* bounded = mk_bounded_tactic(m);
    tactic* smt = mk_smt_tactic(m);

    tactic* branches = or_else(ilp_finder,
                               pb_tac,
                               quasi_branch,
                               bounded,
                               smt);

    tactic* core = and_then(preamble,
                            simplify_lhs,
                            branches);

    tactic* st = using_params(core, main_p);

    
    st->updt_params(p);
    return st;
}

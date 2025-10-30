/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfbv_tactic.cpp

Abstract:

    Tactic for QF_BV based on bit-blasting

Author:

    Leonardo (leonardo) 2012-02-22

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/bv1_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/bv/bv_size_reduction_tactic.h"
#include "tactic/aig/aig_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"

#define MEMLIMIT 300

static tactic * mk_qfbv_preamble(ast_manager& m, params_ref const& p) {

    params_ref solve_eq_p;
    // conservative gaussian elimination.
    solve_eq_p.set_uint("solve_eqs_max_occs", 2);

    params_ref flat_and_or_p = p;
    flat_and_or_p.set_bool("flat_and_or", false);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);
    simp2_p.set_bool("flat", true); // required by som
    simp2_p.set_bool("hoist_mul", false); // required by som
    simp2_p.set_bool("flat_and_or", false);

    params_ref hoist_p;
    hoist_p.set_bool("hoist_mul", true);
    hoist_p.set_bool("som", false);
    hoist_p.set_bool("flat_and_or", false);

    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* simplify1_param = using_params(simplify1, flat_and_or_p);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* propagate_param = using_params(propagate, flat_and_or_p);
    tactic* solve_eqs = mk_solve_eqs_tactic(m);
    tactic* solve_eqs_param = using_params(solve_eqs, solve_eq_p);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);
    tactic* size_reduction = mk_bv_size_reduction_tactic(m);
    tactic* guarded_size = if_no_proofs(if_no_unsat_cores(size_reduction));
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify2_param = using_params(simplify2, simp2_p);
    tactic* simplify3 = mk_simplify_tactic(m);
    tactic* simplify3_param = using_params(simplify3, hoist_p);
    tactic* max_sharing = mk_max_bv_sharing_tactic(m);
    tactic* ackermann = mk_ackermannize_bv_tactic(m,p);
    tactic* guarded_ackermann = if_no_proofs(if_no_unsat_cores(ackermann));

    //
    // Z3 can solve a couple of extra benchmarks by using hoist_mul
    // but the timeout in SMT-COMP is too small.
    // Moreover, it impacted negatively some easy benchmarks.
    // We should decide later, if we keep it or not.
    //
    return and_then(
        simplify1_param,
        propagate_param,
        solve_eqs_param,
        elim_unc,
        guarded_size,
        simplify2_param,
        simplify3_param,
        max_sharing,
        guarded_ackermann
        );
}

static tactic * main_p(tactic* t) {
    params_ref p;
    p.set_bool("elim_and", true);
    p.set_bool("push_ite_bv", true);
    p.set_bool("blast_distinct", true);
    return using_params(t, p);
}


static tactic * mk_qfbv_tactic(ast_manager& m, params_ref const & p, tactic* sat, tactic* smt) {

    params_ref local_ctx_p = p;
    local_ctx_p.set_bool("local_ctx", true);
    local_ctx_p.set_bool("flat", false);
    local_ctx_p.set_bool("flat_and_or", false);

    params_ref solver_p;
    solver_p.set_bool("preprocess", false); // preprocessor of smt::context is not needed.

    tactic* preamble_st = mk_qfbv_preamble(m, p);
    tactic* bv1_blaster = mk_bv1_blaster_tactic(m);
    tactic* smt_with_solver = using_params(smt, solver_p);
    tactic* eq_branch = and_then(bv1_blaster, smt_with_solver);

    tactic* bit_blaster = mk_bit_blaster_tactic(m);
    probe* memory_probe = mk_memory_probe();
    probe* mem_limit = mk_const_probe(MEMLIMIT);
    probe* memory_ok = mk_lt(memory_probe, mem_limit);

    tactic* simplify4 = mk_simplify_tactic(m);
    tactic* solve_eqs4 = mk_solve_eqs_tactic(m);
    tactic* simplify_and_solve = and_then(simplify4, solve_eqs4);
    tactic* simplify_and_solve_with_params = using_params(simplify_and_solve, local_ctx_p);
    tactic* aig = mk_aig_tactic();
    tactic* guarded_aig = if_no_proofs(aig);
    tactic* memory_branch = and_then(simplify_and_solve_with_params, guarded_aig);
    tactic* when_memory = when(memory_ok, memory_branch);

    tactic* bit_branch = and_then(bit_blaster, when_memory, sat);
    tactic* standard_branch = cond(mk_is_qfbv_probe(), bit_branch, smt);

    tactic* combined = cond(mk_is_qfbv_eq_probe(),
                            eq_branch,
                            standard_branch);

    tactic * st = main_p(and_then(preamble_st, combined));

    st->updt_params(p);
    return st;

}


tactic * mk_qfbv_tactic(ast_manager & m, params_ref const & p) {
    tactic* simplify = mk_simplify_tactic(m);
    tactic* smt = mk_smt_tactic(m, p);
    tactic* simplify_then_smt = and_then(simplify, smt);
    probe* produce_proofs = mk_produce_proofs_probe();
    tactic* psat = mk_psat_tactic(m, p);
    tactic * new_sat = cond(produce_proofs,
                            simplify_then_smt,
                            psat);
    return mk_qfbv_tactic(m, p, new_sat, mk_smt_tactic(m, p));

}

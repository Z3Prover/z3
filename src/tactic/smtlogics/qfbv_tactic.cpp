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
#include <cstring>
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/bv1_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/bv/bv_size_reduction_tactic.h"
#include "tactic/bv/bv_divrem_bounds_tactic.h"
#include "tactic/aig/aig_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "sat/sat_solver/inc_sat_solver.h"
#include "ackermannization/ackermannize_bv_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/smtlogics/qfbv_tactic_params.hpp"

// Tuned values are set with set_default_*: a value the user gives, locally or in
// the global module of the key, replaces them. The other values are kept forced.
// som requires flat: when the user sets flat=false, the rewriter turns som off
// (poly_rewriter::updt_params), and with som on it turns hoist_mul off.
//
// Steps are named with scope_tactic: tactic.qfbv.preamble.simp2.flat=false sets flat
// for the second simplify pass only, and tactic.qfbv.preamble.solve_eqs.enabled=false
// skips solve-eqs in the preamble. The keys are declared in qfbv_tactic_params.hpp,
// with the tuned values as their defaults. A scope is placed outside the using_params
// of its step, so that the forced values still win.
tactic * mk_qfbv_preamble(ast_manager& m, params_ref const& p) {
    typedef qfbv_tactic_defaults d;

    params_ref solve_eq_p;
    // conservative gaussian elimination.
    solve_eq_p.set_default_uint("solve_eqs.max_occs", d::preamble_solve_eqs_max_occs);

    params_ref flat_and_or_p = p;
    flat_and_or_p.set_bool("flat_and_or", false);

    // not a copy of p: user values in it would beat user values set later
    // (they reach the step through updt_params)
    params_ref simp2_p;
    simp2_p.set_default_bool("som", d::preamble_simp2_som);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_default_bool("push_ite_bv", d::preamble_simp2_push_ite_bv);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);
    simp2_p.set_default_bool("flat", d::preamble_simp2_flat); // required by som
    simp2_p.set_default_bool("hoist_mul", d::preamble_simp2_hoist_mul); // required by som
    simp2_p.set_bool("flat_and_or", false);

    params_ref hoist_p;
    hoist_p.set_default_bool("hoist_mul", d::preamble_hoist_hoist_mul);
    hoist_p.set_default_bool("som", d::preamble_hoist_som);
    hoist_p.set_bool("flat_and_or", false);

    return scope_tactic("qfbv.preamble",
        and_then(
            using_params(mk_simplify_tactic(m), flat_and_or_p),
            using_params(mk_propagate_values_tactic(m), flat_and_or_p),
            scope_tactic("qfbv.preamble.solve_eqs", using_params(mk_solve_eqs_tactic(m), solve_eq_p)),
            mk_elim_uncnstr_tactic(m),
            mk_bv_divrem_bounds_tactic(m),
            if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
            scope_tactic("qfbv.preamble.simp2", using_params(mk_simplify_tactic(m), simp2_p)),

            //
            // Z3 can solve a couple of extra benchmarks by using hoist_mul
            // but the timeout in SMT-COMP is too small.
            // Moreover, it impacted negatively some easy benchmarks.
            // We should decide later, if we keep it or not.
            //
            scope_tactic("qfbv.preamble.hoist", using_params(mk_simplify_tactic(m), hoist_p)),
            mk_max_bv_sharing_tactic(m),
            if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m,p)))
            ));
}

// The entries of p, in order and with their default flags, without the keys of the
// qfbv scopes (qfbv.* and tactic.qfbv.*). The scopes route those keys from the parameters
// each step receives through updt_params; a copy of them in a using_params inside a
// scope would freeze the values given at construction (a switch could not be cleared).
static void copy_without_scope_keys(params_ref const & p, params_ref & r) {
    for (unsigned i = 0; i < p.size(); ++i) {
        symbol k = p.get_key(i);
        if (k.is_numerical() || (strncmp(k.bare_str(), "qfbv.", 5) != 0 && strncmp(k.bare_str(), "tactic.qfbv.", 12) != 0))
            r.copy_entry(p, k);
    }
}

static tactic * main_p(tactic* t) {
    params_ref p;
    p.set_bool("elim_and", true);
    p.set_default_bool("push_ite_bv", true);
    p.set_bool("blast_distinct", true);
    return using_params(t, p);
}


tactic * mk_qfbv_tactic(ast_manager& m, params_ref const & p, tactic* sat, tactic* smt) {

    params_ref local_ctx_p;
    copy_without_scope_keys(p, local_ctx_p);
    local_ctx_p.set_bool("local_ctx", true);
    local_ctx_p.set_bool("flat", false);
    local_ctx_p.set_bool("flat_and_or", false);

    params_ref solver_p;
    solver_p.set_bool("preprocess", false); // preprocessor of smt::context is not needed.

    tactic* preamble_st = mk_qfbv_preamble(m, p);
    tactic * st = scope_tactic("qfbv", main_p(and_then(preamble_st,
                                  // If the user sets HI_DIV0=false, then the formula may contain uninterpreted function
                                  // symbols. In this case, we should not use the `sat', but instead `smt'. Alternatively,
                                  // the UFs can be eliminated by eager ackermannization in the preamble.
                                  cond(mk_is_qfbv_eq_probe(),
                                       and_then(mk_bv1_blaster_tactic(m),
                                                using_params(smt, solver_p)),
                                       cond(mk_is_qfbv_probe(),
                                            and_then(mk_bit_blaster_tactic(m),
                                                     // aig.max_memory: megabytes allocated by the process
                                                     when(mk_lt(mk_memory_probe(),
                                                                mk_param_probe("aig.max_memory", qfbv_tactic_defaults::aig_max_memory)),
                                                          // the scopes only have enabled rows: inside the
                                                          // using_params, which passes the same parameters
                                                          // to both steps as before
                                                          and_then(using_params(and_then(scope_tactic("qfbv.postblast.simp", mk_simplify_tactic(m)),
                                                                                         scope_tactic("qfbv.postblast.solve_eqs", mk_solve_eqs_tactic(m))),
                                                                                local_ctx_p),
                                                                   scope_tactic("qfbv.postblast.aig", if_no_proofs(mk_aig_tactic())))),
                                                     sat),
                                            smt)))));

    st->updt_params(p);
    return st;

}


tactic * mk_qfbv_tactic(ast_manager & m, params_ref const & p) {
    tactic * new_sat = cond(mk_produce_proofs_probe(),
                            and_then(mk_simplify_tactic(m), mk_smt_tactic(m, p)),
                            mk_psat_tactic(m, p));
    return mk_qfbv_tactic(m, p, new_sat, mk_smt_tactic(m, p));

}

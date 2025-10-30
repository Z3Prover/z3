/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfaufbv_tactic.cpp

Abstract:

    Tactic for QF_AUFBV benchmarks.

Author:

    Leonardo (leonardo) 2012-02-23

Notes:

--*/
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "tactic/bv/bv_size_reduction_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/smtlogics/qfbv_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "ackermannization/ackermannize_bv_tactic.h"

static tactic * mk_qfaufbv_preamble(ast_manager & m, params_ref const & p) {

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);


    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* solve_eqs = mk_solve_eqs_tactic(m);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);
    tactic* size_reduction = mk_bv_size_reduction_tactic(m);
    tactic* guarded_size_reduction = if_no_proofs(if_no_unsat_cores(size_reduction));
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify_with_params = using_params(simplify2, simp2_p);
    tactic* max_sharing = mk_max_bv_sharing_tactic(m);
    tactic* ackermann = mk_ackermannize_bv_tactic(m, p);
    tactic* guarded_ackermann = if_no_proofs(if_no_unsat_cores(ackermann));

    return and_then(simplify1,
                    propagate,
                    solve_eqs,
                    elim_unc,
                    guarded_size_reduction,
                    simplify_with_params,
                    max_sharing,
                    guarded_ackermann);
}

tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);

    tactic * preamble_st = mk_qfaufbv_preamble(m, p);

    tactic* qfbv = mk_qfbv_tactic(m);
    tactic* smt = mk_smt_tactic(m, p);
    probe* qfbv_probe = mk_is_qfbv_probe();
    tactic* branch = cond(qfbv_probe, qfbv, smt);

    tactic * st = using_params(and_then(preamble_st, branch), main_p);
    
    st->updt_params(p);
    return st;
}

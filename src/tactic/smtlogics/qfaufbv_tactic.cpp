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
#include"solve_eqs_tactic.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"bit_blaster_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"ctx_simplify_tactic.h"
#include"sat_tactic.h"
#include"smt_tactic.h"

tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 32);
    ctx_simp_p.set_uint("max_steps", 5000000);

    params_ref solver_p;
    solver_p.set_bool("array.simplify", false); // disable array simplifications at old_simplify module

    tactic * preamble_st = and_then(mk_simplify_tactic(m),
                                    mk_propagate_values_tactic(m),
                                    // using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                                    mk_solve_eqs_tactic(m),
                                    mk_elim_uncnstr_tactic(m),
                                    if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                                    using_params(mk_simplify_tactic(m), simp2_p),
                                    mk_max_bv_sharing_tactic(m)
                                    );

    tactic * st = using_params(and_then(preamble_st,
                                        using_params(mk_smt_tactic(), solver_p)),
                               main_p);
    
    st->updt_params(p);
    return st;
}

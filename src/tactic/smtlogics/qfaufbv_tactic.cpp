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
#include "ackermannization/ackermannize_bv_tactic.h"
#include "smt/tactic/smt_tactic.h"

static tactic * mk_qfaufbv_preamble(ast_manager & m, params_ref const & p) {

    params_ref simp2_p = p;
    simp2_p.set_bool("som", true);
    simp2_p.set_bool("pull_cheap_ite", true);
    simp2_p.set_bool("push_ite_bv", false);
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);


    return and_then(mk_simplify_tactic(m),
                    mk_propagate_values_tactic(m),
                    mk_solve_eqs_tactic(m),
                    mk_elim_uncnstr_tactic(m),
                    // sound to use? if_no_proofs(if_no_unsat_cores(mk_reduce_args_tactic(m))),
                    if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                    using_params(mk_simplify_tactic(m), simp2_p),
                    mk_max_bv_sharing_tactic(m),
                    if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m, p)))
                    );
}

tactic * mk_qfaufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("sort_store", true);

    tactic * preamble_st = mk_qfaufbv_preamble(m, p);

    tactic * st = using_params(and_then(preamble_st, mk_smt_tactic(m)), main_p);
    
    st->updt_params(p);
    return st;
}

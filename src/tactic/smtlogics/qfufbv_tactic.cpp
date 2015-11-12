/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfufbv_tactic.cpp

Abstract:

    Tactic for QF_UFBV

Author:

    Leonardo (leonardo) 2012-02-27

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"solve_eqs_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"smt_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"reduce_args_tactic.h"
#include"qfbv_tactic.h"

tactic * mk_qfufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("blast_distinct", true);

    tactic * preamble_st = and_then(mk_simplify_tactic(m),
                                    mk_propagate_values_tactic(m),
                                    mk_solve_eqs_tactic(m),
                                    mk_elim_uncnstr_tactic(m),
                                    if_no_proofs(if_no_unsat_cores(mk_reduce_args_tactic(m))),
                                    if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
                                    mk_max_bv_sharing_tactic(m)
                                    );

    tactic * st = using_params(and_then(preamble_st,
                                        cond(mk_is_qfbv_probe(),
                                            mk_qfbv_tactic(m),
                                            mk_smt_tactic())),
                               main_p);

    st->updt_params(p);
    return st;
}

/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfuf_tactic.cpp

Abstract:

    Tactic for QF_QFUF benchmarks.

Author:

    Leonardo de Moura (leonardo) 2012-02-21


Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/symmetry_reduce_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"

tactic * mk_qfuf_tactic(ast_manager & m, params_ref const & p) {
    params_ref s2_p;
    s2_p.set_bool("pull_cheap_ite", true);
    s2_p.set_bool("local_ctx", true);
    s2_p.set_uint("local_ctx_limit", 10000000);
    return and_then(mk_simplify_tactic(m, p),
                    mk_propagate_values_tactic(m, p),
                    mk_solve_eqs_tactic(m, p),
                    using_params(mk_simplify_tactic(m, p), s2_p),
                    if_no_proofs(if_no_unsat_cores(mk_symmetry_reduce_tactic(m, p))),
                    mk_smt_tactic(m, p));
}

                    

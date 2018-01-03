/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfnra_nlsat_tactic.h

Abstract:

    Tactic based on nlsat for solving QF_NRA problems

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#include "tactic/tactical.h"

#include "tactic/core/tseitin_cnf_tactic.h"
#include "tactic/arith/degree_shift_tactic.h"
#include "tactic/arith/purify_arith_tactic.h"
#include "nlsat/tactic/nlsat_tactic.h"
#include "tactic/arith/factor_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"

tactic * mk_qfnra_nlsat_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p = p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("blast_distinct", true);
    params_ref purify_p = p;
    purify_p.set_bool("complete", false); // temporary hack, solver does not support uninterpreted functions for encoding (div0 x) applications. So, we replace it application of this kind with an uninterpreted function symbol.

    tactic * factor;
    if (p.get_bool("factor", true))
        factor = mk_factor_tactic(m, p);
    else
        factor = mk_skip_tactic();

    return and_then(and_then(using_params(mk_simplify_tactic(m, p),
                                          main_p),
                             using_params(mk_purify_arith_tactic(m, p),
                                          purify_p),
                             mk_propagate_values_tactic(m, p),
                             mk_solve_eqs_tactic(m, p),
                             using_params(mk_purify_arith_tactic(m, p),
                                          purify_p),
                             mk_elim_uncnstr_tactic(m, p),
                             mk_elim_term_ite_tactic(m, p)),
                    and_then(/* mk_degree_shift_tactic(m, p), */ // may affect full dimensionality detection
                             factor,
                             mk_solve_eqs_tactic(m, p),
                             using_params(mk_purify_arith_tactic(m, p),
                                          purify_p),
                             using_params(mk_simplify_tactic(m, p),
                                          main_p),
                             mk_tseitin_cnf_core_tactic(m, p),
                             using_params(mk_simplify_tactic(m, p),
                                          main_p),
                             mk_nlsat_tactic(m, p)));
}


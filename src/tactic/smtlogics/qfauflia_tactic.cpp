/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qfauflia_tactic.cpp

Abstract:

    Tactic for QF_AUFLIA

Author:

    Leonardo (leonardo) 2012-02-21

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"


tactic * mk_qfauflia_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("som", true);
    main_p.set_bool("sort_store", true);

    params_ref solver_p;
    solver_p.set_bool("array.simplify", false); // disable array simplifications at old_simplify module

    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* solve_eqs = mk_solve_eqs_tactic(m);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic * preamble_st = and_then(simplify1,
                                    propagate,
                                    solve_eqs,
                                    elim_unc,
                                    simplify2
                                    );
    
    tactic * st = and_then(using_params(preamble_st, main_p),
                           using_params(mk_smt_tactic(m), solver_p));
    
    st->updt_params(p);
    return st;
}

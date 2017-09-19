/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qfufnra_tactic.cpp

Abstract:

    Tactic for QF_UFNRA

Author:

    Nikolaj (nbjorner) 2015-05-05

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/nlsat_smt/nl_purify_tactic.h"
#include "tactic/smtlogics/qfufnra_tactic.h"
#include "tactic/arith/purify_arith_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/nnf_tactic.h"
#include "tactic/core/tseitin_cnf_tactic.h"

tactic * mk_qfufnra_tactic(ast_manager & m, params_ref const& p) {
    params_ref main_p = p;
    main_p.set_bool("elim_and", true);
    main_p.set_bool("blast_distinct", true);
    
    return and_then(and_then(using_params(mk_simplify_tactic(m, p), main_p),
                             mk_purify_arith_tactic(m, p),
                             mk_propagate_values_tactic(m, p),
                             mk_solve_eqs_tactic(m, p),
                             mk_elim_uncnstr_tactic(m, p)),
                    and_then(mk_elim_term_ite_tactic(m, p),
                             mk_solve_eqs_tactic(m, p),
                             using_params(mk_simplify_tactic(m, p), main_p),
                             mk_tseitin_cnf_core_tactic(m, p),
                             using_params(mk_simplify_tactic(m, p), main_p),
                             mk_nl_purify_tactic(m, p)));
}



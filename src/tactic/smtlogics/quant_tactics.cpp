/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    quant_tactics.cpp

Abstract:

    Tactics for benchmarks containing quantifiers.
    
Author:

    Leonardo de Moura (leonardo) 2012-02-21.

Revision History:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "qe/qe_tactic.h"
#include "qe/qe_lite.h"
#include "qe/qsat.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "smt/tactic/smt_tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "tactic/arith/probe_arith.h"

static tactic * mk_quant_preprocessor(ast_manager & m, bool disable_gaussian = false) {
    params_ref pull_ite_p;
    pull_ite_p.set_bool("pull_cheap_ite", true);
    pull_ite_p.set_bool("local_ctx", true);
    pull_ite_p.set_uint("local_ctx_limit", 10000000);
    
    params_ref ctx_simp_p;
    ctx_simp_p.set_uint("max_depth", 30);
    ctx_simp_p.set_uint("max_steps", 5000000);

    tactic * solve_eqs;
    if (disable_gaussian) {
        solve_eqs = mk_skip_tactic();
    }
    else {
        solve_eqs = when(mk_not(mk_has_pattern_probe()), mk_solve_eqs_tactic(m));
    }
 
    // remark: investigate if gaussian elimination is useful when patterns are not provided.
    return and_then(mk_simplify_tactic(m), 
                    mk_propagate_values_tactic(m),
                    using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                    using_params(mk_simplify_tactic(m), pull_ite_p),
                    solve_eqs,
                    mk_elim_uncnstr_tactic(m),
                    mk_simplify_tactic(m));    
}

static tactic * mk_no_solve_eq_preprocessor(ast_manager & m) {
    return mk_quant_preprocessor(m, true);
}

tactic * mk_ufnia_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = and_then(mk_no_solve_eq_preprocessor(m),
                           mk_qe_lite_tactic(m, p),
                           mk_smt_tactic());
    st->updt_params(p);
    return st;
}

tactic * mk_uflra_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = and_then(mk_quant_preprocessor(m),
                           mk_smt_tactic());
    st->updt_params(p);
    return st;
}

tactic * mk_auflia_tactic(ast_manager & m, params_ref const & p) {
    params_ref qi_p;
    qi_p.set_str("qi.cost", "0");
    TRACE("qi_cost", qi_p.display(tout); tout << "\n" << qi_p.get_str("qi.cost", "<null>") << "\n";);
    tactic * st = and_then(mk_no_solve_eq_preprocessor(m),
                           or_else(and_then(fail_if(mk_gt(mk_num_exprs_probe(), mk_const_probe(static_cast<double>(128)))),
                                            using_params(mk_smt_tactic(), qi_p),
                                            mk_fail_if_undecided_tactic()),
                                   mk_smt_tactic()));
    st->updt_params(p);
    return st;
}

tactic * mk_auflira_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = and_then(mk_quant_preprocessor(m),
                           mk_smt_tactic());
    st->updt_params(p);
    return st;
}

tactic * mk_aufnira_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = and_then(mk_quant_preprocessor(m),
                           mk_smt_tactic());
    st->updt_params(p);
    return st;
}

tactic * mk_lra_tactic(ast_manager & m, params_ref const & p) {
    tactic * st = and_then(mk_quant_preprocessor(m),
                           mk_qe_lite_tactic(m, p),
                           cond(mk_has_quantifier_probe(), 
                                cond(mk_is_lira_probe(),
                                     or_else(mk_qsat_tactic(m, p),
                                             and_then(mk_qe_tactic(m), mk_smt_tactic())),
                                     mk_smt_tactic()),
                                mk_smt_tactic()));
    st->updt_params(p);
    return st;
}

tactic * mk_lia_tactic(ast_manager & m, params_ref const & p) {
    return mk_lra_tactic(m, p);
}

tactic * mk_lira_tactic(ast_manager & m, params_ref const & p) {
    return mk_lra_tactic(m, p);
}


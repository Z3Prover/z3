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
#include "qe/lite/qe_lite_tactic.h"
#include "qe/qsat.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "tactic/arith/probe_arith.h"
#include "tactic/smtlogics/smt_tactic.h"

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
        probe* has_pattern = mk_has_pattern_probe();
        probe* no_pattern = mk_not(has_pattern);
        tactic* solve_eqs_core = mk_solve_eqs_tactic(m);
        solve_eqs = when(no_pattern, solve_eqs_core);
    }
 
    // remark: investigate if gaussian elimination is useful when patterns are not provided.
    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* ctx_simplify = mk_ctx_simplify_tactic(m);
    tactic* ctx_simplify_with_params = using_params(ctx_simplify, ctx_simp_p);
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify_with_pull_ite = using_params(simplify2, pull_ite_p);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);
    tactic* simplify3 = mk_simplify_tactic(m);

    return and_then(simplify1, 
                    propagate,
                    ctx_simplify_with_params,
                    simplify_with_pull_ite,
                    solve_eqs,
                    elim_unc,
                    simplify3);    
}

static tactic * mk_no_solve_eq_preprocessor(ast_manager & m) {
    return mk_quant_preprocessor(m, true);
}

tactic * mk_ufnia_tactic(ast_manager & m, params_ref const & p) {
    tactic* preprocessor = mk_no_solve_eq_preprocessor(m);
    tactic* qe = mk_qe_lite_tactic(m, p);
    tactic* smt = mk_smt_tactic(m);
    tactic * st = and_then(preprocessor,
                           qe,
                           smt);
    st->updt_params(p);
    return st;
}

tactic * mk_uflra_tactic(ast_manager & m, params_ref const & p) {
    tactic* preprocessor = mk_quant_preprocessor(m);
    tactic* smt = mk_smt_tactic(m);
    tactic * st = and_then(preprocessor,
                           smt);
    st->updt_params(p);
    return st;
}

tactic * mk_auflia_tactic(ast_manager & m, params_ref const & p) {
    params_ref qi_p;
    qi_p.set_str("qi.cost", "0");
    TRACE(qi_cost, qi_p.display(tout); tout << "\n" << qi_p.get_str("qi.cost", "<null>") << "\n";);
    tactic* preprocessor = mk_no_solve_eq_preprocessor(m);
    probe* num_exprs = mk_num_exprs_probe();
    probe* limit_probe = mk_const_probe(static_cast<double>(128));
    probe* gt_probe = mk_gt(num_exprs, limit_probe);
    tactic* fail_guard = fail_if(gt_probe);
    tactic* smt_with_params = using_params(mk_smt_tactic(m), qi_p);
    tactic* fail_undecided = mk_fail_if_undecided_tactic();
    tactic* guarded_branch = and_then(fail_guard, smt_with_params, fail_undecided);
    tactic* default_smt = mk_smt_tactic(m);
    tactic* branch = or_else(guarded_branch, default_smt);
    tactic * st = and_then(preprocessor, branch);
    st->updt_params(p);
    return st;
}

tactic * mk_auflira_tactic(ast_manager & m, params_ref const & p) {
    tactic* preprocessor = mk_quant_preprocessor(m);
    tactic* smt = mk_smt_tactic(m);
    tactic * st = and_then(preprocessor,
                           smt);
    st->updt_params(p);
    return st;
}

tactic * mk_aufnira_tactic(ast_manager & m, params_ref const & p) {
    tactic* preprocessor = mk_quant_preprocessor(m);
    tactic* smt = mk_smt_tactic(m);
    tactic * st = and_then(preprocessor,
                           smt);
    st->updt_params(p);
    return st;
}

tactic * mk_lra_tactic(ast_manager & m, params_ref const & p) {
    tactic* preprocessor = mk_quant_preprocessor(m);
    tactic* qe = mk_qe_lite_tactic(m, p);

    probe* has_quant_probe = mk_has_quantifier_probe();
    probe* is_lira_probe = mk_is_lira_probe();

    tactic* qsat = mk_qsat_tactic(m, p);
    tactic* smt_for_qsat = mk_smt_tactic(m);
    tactic* qsat_branch = or_else(qsat, smt_for_qsat);

    tactic* smt_after_lira = mk_smt_tactic(m);
    tactic* lira_branch = cond(is_lira_probe, qsat_branch, smt_after_lira);

    tactic* smt_no_quant = mk_smt_tactic(m);
    tactic* quant_branch = cond(has_quant_probe, lira_branch, smt_no_quant);

    tactic * st = and_then(preprocessor,
                           qe,
                           quant_branch);
    st->updt_params(p);
    return st;
}

tactic * mk_lia_tactic(ast_manager & m, params_ref const & p) {
    return mk_lra_tactic(m, p);
}

tactic * mk_lira_tactic(ast_manager & m, params_ref const & p) {
    return mk_lra_tactic(m, p);
}

/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    qflia_tactic.cpp

Abstract:

    Tactic for QF_NIA

Author:

    Leonardo (leonardo) 2012-02-28

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "tactic/arith/nla2bv_tactic.h"
#include "tactic/arith/lia2card_tactic.h"
#include "tactic/arith/card2bv_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/core/cofactor_term_ite_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "nlsat/tactic/qfnra_nlsat_tactic.h"

static tactic * mk_qfnia_bv_solver(ast_manager & m, params_ref const & p_ref) {
    params_ref p = p_ref;
    p.set_bool("flat", false);
    p.set_bool("hi_div0", true); 
    p.set_bool("elim_and", true);
    p.set_bool("blast_distinct", true);
    
    params_ref simp2_p = p;
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    params_ref mem_p = p;
    mem_p.set_uint("max_memory", 100);
    mem_p.set_uint("max_conflicts", 500);

    
    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify_with_params = using_params(simplify2, simp2_p);
    tactic* max_sharing = mk_max_bv_sharing_tactic(m);
    tactic* bit_blaster = mk_bit_blaster_tactic(m);
    tactic* bit_blaster_with_params = using_params(bit_blaster, mem_p);
    tactic* sat = mk_sat_tactic(m, mem_p);

    tactic * r = using_params(and_then(simplify1,
                                       propagate,
                                       simplify_with_params,
                                       max_sharing,
                                       bit_blaster_with_params,
                                       sat),
                              p);
    return r;
}

static tactic * mk_qfnia_preamble(ast_manager & m, params_ref const & p_ref) {
    params_ref pull_ite_p = p_ref;
    pull_ite_p.set_bool("pull_cheap_ite", true);
    pull_ite_p.set_bool("local_ctx", true);
    pull_ite_p.set_uint("local_ctx_limit", 10000000);
    
    params_ref ctx_simp_p = p_ref;
    ctx_simp_p.set_uint("max_depth", 30);
    ctx_simp_p.set_uint("max_steps", 5000000);
    

    params_ref elim_p = p_ref;
    elim_p.set_uint("max_memory",20);
    
    tactic* simplify1 = mk_simplify_tactic(m);
    tactic* propagate = mk_propagate_values_tactic(m);
    tactic* ctx_simplify = mk_ctx_simplify_tactic(m);
    tactic* ctx_simplify_with_params = using_params(ctx_simplify, ctx_simp_p);
    tactic* simplify2 = mk_simplify_tactic(m);
    tactic* simplify_with_pull_ite = using_params(simplify2, pull_ite_p);
    tactic* elim_unc = mk_elim_uncnstr_tactic(m);
    tactic* lia2card = mk_lia2card_tactic(m);
    tactic* card2bv = mk_card2bv_tactic(m, p_ref);
    tactic* cofactor = mk_cofactor_term_ite_tactic(m);
    tactic* cofactor_with_params = using_params(cofactor, elim_p);

    return and_then(simplify1, 
                    propagate,
                    ctx_simplify_with_params,
                    simplify_with_pull_ite,
                    elim_unc,
                    lia2card, 
                    card2bv,
                    skip_if_failed(cofactor_with_params));
}

static tactic * mk_qfnia_sat_solver(ast_manager & m, params_ref const & p) {
    params_ref nia2sat_p = p;
    nia2sat_p.set_uint("nla2bv_max_bv_size", 64);  
    params_ref simp_p = p;
    simp_p.set_bool("hoist_mul", true); // hoist multipliers to create smaller circuits.

    tactic* simplify = mk_simplify_tactic(m);
    tactic* simplify_with_params = using_params(simplify, simp_p);
    tactic* nla2bv = mk_nla2bv_tactic(m, nia2sat_p);
    tactic* bv_solver = mk_qfnia_bv_solver(m, p);
    tactic* guarded_bv_solver = skip_if_failed(bv_solver);
    tactic* fail_if_undecided = mk_fail_if_undecided_tactic();

    return and_then(simplify_with_params,
                    nla2bv,
                    guarded_bv_solver,
                    fail_if_undecided);
}

static tactic * mk_qfnia_nlsat_solver(ast_manager & m, params_ref const & p) {
    params_ref simp_p = p;
    simp_p.set_bool("som", true); // expand into sums of monomials
    simp_p.set_bool("factor", false);

    return and_then(using_params(mk_simplify_tactic(m), simp_p),
                    try_for(mk_qfnra_nlsat_tactic(m, simp_p), 3000),
                    mk_fail_if_undecided_tactic());
}

static tactic * mk_qfnia_smt_solver(ast_manager& m, params_ref const& p) {
    params_ref simp_p = p;
    simp_p.set_bool("som", true); // expand into sums of monomials
    return and_then(
        using_params(mk_simplify_tactic(m), simp_p), 
        mk_smt_tactic(m));
}

tactic * mk_qfnia_tactic(ast_manager & m, params_ref const & p) {
    tactic* report = mk_report_verbose_tactic("(qfnia-tactic)", 10);
    tactic* preamble = mk_qfnia_preamble(m, p);

    tactic* sat_solver = mk_qfnia_sat_solver(m, p);
    tactic* smt_solver1 = mk_qfnia_smt_solver(m, p);
    tactic* smt_solver_try = try_for(mk_qfnia_smt_solver(m, p), 2000);
    tactic* nlsat_solver = mk_qfnia_nlsat_solver(m, p);

    tactic* branch = or_else(sat_solver,
                             smt_solver_try,
                             nlsat_solver,        
                             smt_solver1);

    return and_then(report,
                    preamble,
                    branch);
}

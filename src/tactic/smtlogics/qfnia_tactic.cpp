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
#include"tactical.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"solve_eqs_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"smt_tactic.h"
#include"bit_blaster_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"sat_tactic.h"
#include"nla2bv_tactic.h"
#include"ctx_simplify_tactic.h"
#include"cofactor_term_ite_tactic.h"

tactic * mk_qfnia_bv_solver(ast_manager & m, params_ref const & p_ref) {
    params_ref p = p_ref;
    p.set_bool("flat", false);
    p.set_bool("hi_div0", true); 
    p.set_bool("elim_and", true);
    p.set_bool("blast_distinct", true);
    
    params_ref simp2_p = p;
    simp2_p.set_bool("local_ctx", true);
    simp2_p.set_uint("local_ctx_limit", 10000000);

    
    tactic * r = using_params(and_then(mk_simplify_tactic(m),
                                       mk_propagate_values_tactic(m),
                                       using_params(mk_simplify_tactic(m), simp2_p),
                                       mk_max_bv_sharing_tactic(m),
                                       mk_bit_blaster_tactic(m),
                                       mk_sat_tactic(m)),
                              p);
    return r;
}

tactic * mk_qfnia_premable(ast_manager & m, params_ref const & p_ref) {
    params_ref pull_ite_p = p_ref;
    pull_ite_p.set_bool("pull_cheap_ite", true);
    pull_ite_p.set_bool("local_ctx", true);
    pull_ite_p.set_uint("local_ctx_limit", 10000000);
    
    params_ref ctx_simp_p = p_ref;
    ctx_simp_p.set_uint("max_depth", 30);
    ctx_simp_p.set_uint("max_steps", 5000000);
    
    params_ref simp_p = p_ref;
    simp_p.set_bool("hoist_mul", true);

    params_ref elim_p = p_ref;
    elim_p.set_uint("max_memory",20);
    
    return
        and_then(mk_simplify_tactic(m), 
                 mk_propagate_values_tactic(m),
                 using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                 using_params(mk_simplify_tactic(m), pull_ite_p),
                 mk_elim_uncnstr_tactic(m),
                 skip_if_failed(using_params(mk_cofactor_term_ite_tactic(m), elim_p)),
                 using_params(mk_simplify_tactic(m), simp_p));    
}

tactic * mk_qfnia_sat_solver(ast_manager & m, params_ref const & p) {
    params_ref nia2sat_p = p;
    nia2sat_p.set_uint("nla2bv_max_bv_size", 64);   

    return and_then(mk_nla2bv_tactic(m, nia2sat_p),
                    mk_qfnia_bv_solver(m, p),
                    mk_fail_if_undecided_tactic());
}

tactic * mk_qfnia_tactic(ast_manager & m, params_ref const & p) {
    return and_then(mk_qfnia_premable(m, p),
                    or_else(mk_qfnia_sat_solver(m, p),
                            mk_smt_tactic()));
}

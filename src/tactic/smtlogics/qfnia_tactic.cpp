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
#include "smt/tactic/smt_tactic.h"
#include "tactic/bv/bit_blaster_tactic.h"
#include "tactic/bv/max_bv_sharing_tactic.h"
#include "sat/tactic/sat_tactic.h"
#include "tactic/arith/nla2bv_tactic.h"
#include "tactic/arith/lia2card_tactic.h"
#include "tactic/arith/card2bv_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/core/cofactor_term_ite_tactic.h"
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

    
    tactic * r = using_params(and_then(mk_simplify_tactic(m),
                                       mk_propagate_values_tactic(m),
                                       using_params(mk_simplify_tactic(m), simp2_p),
                                       mk_max_bv_sharing_tactic(m),
                                       using_params(mk_bit_blaster_tactic(m), mem_p),
                                       mk_sat_tactic(m)),
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
    
    return
        and_then(mk_simplify_tactic(m), 
                 mk_propagate_values_tactic(m),
                 using_params(mk_ctx_simplify_tactic(m), ctx_simp_p),
                 using_params(mk_simplify_tactic(m), pull_ite_p),
                 mk_elim_uncnstr_tactic(m),
                 mk_lia2card_tactic(m), 
			     mk_card2bv_tactic(m, p_ref),
                 skip_if_failed(using_params(mk_cofactor_term_ite_tactic(m), elim_p)));
}

static tactic * mk_qfnia_sat_solver(ast_manager & m, params_ref const & p) {
    params_ref nia2sat_p = p;
    nia2sat_p.set_uint("nla2bv_max_bv_size", 64);  
    params_ref simp_p = p;
    simp_p.set_bool("hoist_mul", true); // hoist multipliers to create smaller circuits.

    return and_then(using_params(mk_simplify_tactic(m), simp_p),
                    mk_nla2bv_tactic(m, nia2sat_p),
                    skip_if_failed(mk_qfnia_bv_solver(m, p)),
                    mk_fail_if_undecided_tactic());
}

static tactic * mk_qfnia_nlsat_solver(ast_manager & m, params_ref const & p) {
    params_ref nia2sat_p = p;
    nia2sat_p.set_uint("nla2bv_max_bv_size", 64);  
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
    return and_then(
        mk_report_verbose_tactic("(qfnia-tactic)", 10),
        mk_qfnia_preamble(m, p),
        or_else(mk_qfnia_sat_solver(m, p),
                 try_for(mk_qfnia_smt_solver(m, p), 2000),
                 mk_qfnia_nlsat_solver(m, p),        
                 mk_qfnia_smt_solver(m, p))
                    )
        ;
}


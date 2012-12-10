/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    ufbv_tactic.cpp

Abstract:

    General purpose tactic for UFBV benchmarks.

Author:

    Christoph (cwinter) 2012-10-24

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"propagate_values_tactic.h"
#include"solve_eqs_tactic.h"
#include"distribute_forall_tactic.h"
#include"der_tactic.h"
#include"reduce_args_tactic.h"
#include"smt_tactic.h"
#include"nnf_tactic.h"
#include"macro_finder_tactic.h"
#include"ufbv_rewriter_tactic.h"
#include"quasi_macros_tactic.h"
#include"ufbv_tactic.h"


tactic * mk_der_fp_tactic(ast_manager & m, params_ref const & p) {
    return repeat(and_then(mk_der_tactic(m), mk_simplify_tactic(m, p)));
}

tactic * mk_ufbv_preprocessor_tactic(ast_manager & m, params_ref const & p) {
    params_ref no_elim_and(p);
    no_elim_and.set_bool("elim_and", false);

    return and_then(
		mk_trace_tactic("ufbv_pre"),
                and_then(mk_simplify_tactic(m, p),
                         mk_propagate_values_tactic(m, p),
                         and_then(using_params(mk_macro_finder_tactic(m, no_elim_and), no_elim_and), 
				  mk_simplify_tactic(m, p)),
                         and_then(mk_snf_tactic(m, p), mk_simplify_tactic(m, p)),			 
                         mk_elim_and_tactic(m, p),
                         mk_solve_eqs_tactic(m, p),
                         and_then(mk_der_fp_tactic(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_distribute_forall_tactic(m, p), mk_simplify_tactic(m, p))),
                and_then(and_then(mk_reduce_args_tactic(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_macro_finder_tactic(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_ufbv_rewriter_tactic(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_quasi_macros_tactic(m, p), mk_simplify_tactic(m, p)),
                         and_then(mk_der_fp_tactic(m, p), mk_simplify_tactic(m, p)),
                         mk_simplify_tactic(m, p)),
		mk_trace_tactic("ufbv_post"));
}

tactic * mk_ufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p(p);    
    main_p.set_bool("mbqi", true);
    main_p.set_uint("mbqi.max_iterations", UINT_MAX);
    main_p.set_bool("elim_and", true);

    tactic * t = and_then(repeat(mk_ufbv_preprocessor_tactic(m, main_p), 2),
                          mk_smt_tactic_using(false, main_p));
    
    t->updt_params(p);

    return t;
}

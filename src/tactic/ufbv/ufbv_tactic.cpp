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
#include "tactic/tactical.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/propagate_values_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/core/distribute_forall_tactic.h"
#include "tactic/core/der_tactic.h"
#include "tactic/core/reduce_args_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/core/nnf_tactic.h"
#include "tactic/ufbv/macro_finder_tactic.h"
#include "tactic/ufbv/ufbv_rewriter_tactic.h"
#include "tactic/ufbv/quasi_macros_tactic.h"
#include "tactic/ufbv/ufbv_tactic.h"


static tactic * mk_der_fp_tactic(ast_manager & m, params_ref const & p) {
    tactic * der = mk_der_tactic(m);
    tactic * simplify = mk_simplify_tactic(m, p);
    tactic * seq = and_then(der, simplify);
    tactic * result = repeat(seq, 5);
    return result;
}

static tactic * mk_ufbv_preprocessor_tactic(ast_manager & m, params_ref const & p) {
    params_ref no_elim_and(p);
    no_elim_and.set_bool("elim_and", false);

    tactic * trace_pre = mk_trace_tactic("ufbv_pre");

    tactic * simplify1 = mk_simplify_tactic(m, p);
    tactic * propagate_values = mk_propagate_values_tactic(m, p);

    tactic * macro_no_elim = mk_macro_finder_tactic(m, no_elim_and);
    tactic * macro_with_params = using_params(macro_no_elim, no_elim_and);
    tactic * unsat_guard = if_no_unsat_cores(macro_with_params);
    tactic * proofs_guard = if_no_proofs(unsat_guard);
    tactic * simplify_after_guard = mk_simplify_tactic(m, p);
    tactic * guard_chain = and_then(proofs_guard, simplify_after_guard);

    tactic * snf_tac = mk_snf_tactic(m, p);
    tactic * simplify_after_snf = mk_simplify_tactic(m, p);
    tactic * snf_chain = and_then(snf_tac, simplify_after_snf);

    tactic * elim_and_tac = mk_elim_and_tactic(m, p);
    tactic * solve_eqs_tac = mk_solve_eqs_tactic(m, p);

    tactic * der_fp_tac = mk_der_fp_tactic(m, p);
    tactic * simplify_after_der = mk_simplify_tactic(m, p);
    tactic * der_chain = and_then(der_fp_tac, simplify_after_der);

    tactic * distribute_forall = mk_distribute_forall_tactic(m, p);
    tactic * simplify_after_distribute = mk_simplify_tactic(m, p);
    tactic * distribute_chain = and_then(distribute_forall, simplify_after_distribute);

    tactic * preprocess_seq = and_then(
        simplify1,
        propagate_values,
        guard_chain,
        snf_chain,
        elim_and_tac,
        solve_eqs_tac,
        der_chain,
        distribute_chain);

    tactic * reduce_args_tac = mk_reduce_args_tactic(m, p);
    tactic * simplify_after_reduce = mk_simplify_tactic(m, p);
    tactic * reduce_chain = and_then(reduce_args_tac, simplify_after_reduce);

    tactic * macro_finder_tac = mk_macro_finder_tactic(m, p);
    tactic * simplify_after_macro = mk_simplify_tactic(m, p);
    tactic * macro_chain = and_then(macro_finder_tac, simplify_after_macro);

    tactic * ufbv_rewriter_tac = mk_ufbv_rewriter_tactic(m, p);
    tactic * simplify_after_ufbv = mk_simplify_tactic(m, p);
    tactic * ufbv_chain = and_then(ufbv_rewriter_tac, simplify_after_ufbv);

    tactic * quasi_macros_tac = mk_quasi_macros_tactic(m, p);
    tactic * simplify_after_quasi = mk_simplify_tactic(m, p);
    tactic * quasi_chain = and_then(quasi_macros_tac, simplify_after_quasi);

    tactic * post_simplify_seq = and_then(
        reduce_chain,
        macro_chain,
        ufbv_chain,
        quasi_chain);
    tactic * guarded_post_simplify = if_no_unsat_cores(post_simplify_seq);

    tactic * der_fp_tac2 = mk_der_fp_tactic(m, p);
    tactic * simplify_after_der2 = mk_simplify_tactic(m, p);
    tactic * der_chain2 = and_then(der_fp_tac2, simplify_after_der2);

    tactic * simplify_final = mk_simplify_tactic(m, p);
    tactic * trace_post = mk_trace_tactic("ufbv_post");

    tactic * result = and_then(
        trace_pre,
        preprocess_seq,
        guarded_post_simplify,
        der_chain2,
        simplify_final,
        trace_post);
    return result;
}

tactic * mk_ufbv_tactic(ast_manager & m, params_ref const & p) {
    params_ref main_p(p);    
    main_p.set_bool("mbqi", true);
    main_p.set_uint("mbqi.max_iterations", UINT_MAX);
    main_p.set_bool("elim_and", true);

    tactic * t = and_then(repeat(mk_ufbv_preprocessor_tactic(m, main_p), 2),
                          mk_smt_tactic_using(m, false, main_p));
    
    t->updt_params(p);

    return t;
}

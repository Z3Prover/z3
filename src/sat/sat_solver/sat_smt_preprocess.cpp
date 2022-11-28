/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    sat_smt_preprocess.cpp

Abstract:

    SAT pre-process

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-28

--*/

#include "sat/sat_params.hpp"
#include "sat/sat_solver/sat_smt_preprocess.h"
#include "ast/simplifiers/bit_blaster.h"
#include "ast/simplifiers/max_bv_sharing.h"
#include "ast/simplifiers/card2bv.h"
#include "ast/simplifiers/propagate_values.h"
#include "ast/simplifiers/rewriter_simplifier.h"
#include "ast/simplifiers/solve_eqs.h"
#include "ast/simplifiers/eliminate_predicates.h"

void init_preprocess(ast_manager& m, params_ref const& p, seq_simplifier& s, dependent_expr_state& st) {
    params_ref simp1_p = p;
    simp1_p.set_bool("som", true);
    simp1_p.set_bool("pull_cheap_ite", true);
    simp1_p.set_bool("push_ite_bv", false);
    simp1_p.set_bool("local_ctx", true);
    simp1_p.set_uint("local_ctx_limit", 10000000);
    simp1_p.set_bool("flat", true); // required by som
    simp1_p.set_bool("hoist_mul", false); // required by som
    simp1_p.set_bool("elim_and", true);
    simp1_p.set_bool("blast_distinct", true);
    simp1_p.set_bool("flat_and_or", false);
    
    params_ref simp2_p = p;
    simp2_p.set_bool("flat", false);
    simp2_p.set_bool("flat_and_or", false);
    
    sat_params sp(p);
    if (sp.euf()) {
        s.add_simplifier(alloc(rewriter_simplifier, m, p, st));
        s.add_simplifier(alloc(propagate_values, m, p, st));
        //
        // add: 
        // solve_eqs
        // elim_predicates
        // elim_uncnstr
        // euf_completion?
        //
        // add: make it externally configurable
        // 
    }
    else {
        s.add_simplifier(alloc(rewriter_simplifier, m, p, st));
        s.add_simplifier(alloc(propagate_values, m, p, st));
        s.add_simplifier(alloc(card2bv, m, p, st));
        s.add_simplifier(alloc(rewriter_simplifier, m, simp1_p, st));
        s.add_simplifier(mk_max_bv_sharing(m, p, st));
        s.add_simplifier(alloc(bit_blaster, m, p, st));
        s.add_simplifier(alloc(rewriter_simplifier, m, simp2_p, st));
    }    
}


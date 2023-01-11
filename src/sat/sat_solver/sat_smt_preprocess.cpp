/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    sat_smt_preprocess.cpp

Abstract:

    SAT pre-process

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-28

--*/


#include "ast/simplifiers/bit_blaster.h"
#include "ast/simplifiers/max_bv_sharing.h"
#include "ast/simplifiers/card2bv.h"
#include "ast/simplifiers/propagate_values.h"
#include "ast/simplifiers/rewriter_simplifier.h"
#include "ast/simplifiers/solve_eqs.h"
#include "ast/simplifiers/bv_slice.h"
#include "ast/simplifiers/eliminate_predicates.h"
#include "ast/simplifiers/elim_unconstrained.h"
#include "ast/simplifiers/pull_nested_quantifiers.h"
#include "ast/simplifiers/distribute_forall.h"
#include "ast/simplifiers/refine_inj_axiom.h"
#include "ast/simplifiers/elim_bounds.h"
#include "ast/simplifiers/bit2int.h"
#include "ast/simplifiers/bv_elim.h"
#include "ast/simplifiers/push_ite.h"
#include "ast/simplifiers/elim_term_ite.h"
#include "ast/simplifiers/flatten_clauses.h"
#include "ast/simplifiers/cnf_nnf.h"
#include "sat/sat_params.hpp"
#include "smt/params/smt_params.h"
#include "sat/sat_solver/sat_smt_preprocess.h"
#include "qe/lite/qe_lite.h"

void init_preprocess(ast_manager& m, params_ref const& p, seq_simplifier& s, dependent_expr_state& st) {
    
    sat_params sp(p);
    smt_params smtp(p);
    if (sp.euf() || sp.smt()) {
        s.add_simplifier(alloc(rewriter_simplifier, m, p, st));
        if (smtp.m_propagate_values) s.add_simplifier(alloc(propagate_values, m, p, st));
        if (smtp.m_solve_eqs) s.add_simplifier(alloc(euf::solve_eqs, m, st));
        if (smtp.m_elim_unconstrained) s.add_simplifier(alloc(elim_unconstrained, m, st));
        if (smtp.m_nnf_cnf) s.add_simplifier(alloc(cnf_nnf_simplifier, m, p, st));
        if (smtp.m_macro_finder || smtp.m_quasi_macros) s.add_simplifier(alloc(eliminate_predicates, m, st));
        if (smtp.m_qe_lite) s.add_simplifier(mk_qe_lite_simplifer(m, p, st));
        if (smtp.m_pull_nested_quantifiers) s.add_simplifier(alloc(pull_nested_quantifiers_simplifier, m, p, st));
        if (smtp.m_max_bv_sharing) s.add_simplifier(mk_max_bv_sharing(m, p, st));
        if (smtp.m_refine_inj_axiom) s.add_simplifier(alloc(refine_inj_axiom_simplifier, m, p, st));
        if (smtp.m_bv_size_reduce) s.add_simplifier(alloc(bv::slice, m, st));
        if (smtp.m_distribute_forall) s.add_simplifier(alloc(distribute_forall_simplifier, m, p, st));
        if (smtp.m_eliminate_bounds) s.add_simplifier(alloc(elim_bounds_simplifier, m, p, st));
        if (smtp.m_simplify_bit2int) s.add_simplifier(alloc(bit2int_simplifier, m, p, st));
        if (smtp.m_bb_quantifiers) s.add_simplifier(alloc(bv::elim_simplifier, m, p, st));
        if (smtp.m_eliminate_term_ite && smtp.m_lift_ite != lift_ite_kind::LI_FULL) s.add_simplifier(alloc(elim_term_ite_simplifier, m, p, st));        
        if (smtp.m_lift_ite != lift_ite_kind::LI_NONE) s.add_simplifier(alloc(push_ite_simplifier, m, p, st, smtp.m_lift_ite == lift_ite_kind::LI_CONSERVATIVE));
        if (smtp.m_ng_lift_ite != lift_ite_kind::LI_NONE) s.add_simplifier(alloc(ng_push_ite_simplifier, m, p, st, smtp.m_ng_lift_ite == lift_ite_kind::LI_CONSERVATIVE));
        s.add_simplifier(alloc(flatten_clauses, m, p, st));
        
        //
        // add: 
        // euf_completion?
        //
        // add: make it externally programmable
        // 
#if 0
    if (!invoke(m_apply_quasi_macros)) return;
#endif

    }
    else {
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

        s.add_simplifier(alloc(rewriter_simplifier, m, p, st));
        s.add_simplifier(alloc(propagate_values, m, p, st));
        s.add_simplifier(alloc(card2bv, m, p, st));
        s.add_simplifier(alloc(rewriter_simplifier, m, simp1_p, st));
        s.add_simplifier(mk_max_bv_sharing(m, p, st));
        s.add_simplifier(alloc(bit_blaster_simplifier, m, p, st));
        s.add_simplifier(alloc(rewriter_simplifier, m, simp2_p, st));
    }    
}


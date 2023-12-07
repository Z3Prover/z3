/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    solver_preprocess.cpp

Abstract:

    pre-process initialization module for solver

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-28

Notes:

 - port various pre-processing to simplifiers
   - qe-lite, fm-elimination, ite-lifting, other from asserted_formulas
--*/


#include "ast/rewriter/rewriter_def.h"
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
#include "ast/simplifiers/bound_simplifier.h"
#include "ast/simplifiers/cnf_nnf.h"
#include "smt/params/smt_params.h"
#include "solver/solver_preprocess.h"
#include "qe/lite/qe_lite_tactic.h"

void init_preprocess(ast_manager& m, params_ref const& p, then_simplifier& s, dependent_expr_state& st) {

    auto mk_bound_simplifier = [&]() {
        auto* s1 = alloc(bound_simplifier, m, p, st);
        auto* s2 = alloc(then_simplifier, m, p, st);
        s2->add_simplifier(alloc(rewriter_simplifier, m, p, st));
        s2->add_simplifier(alloc(propagate_values, m, p, st));
        s2->add_simplifier(alloc(euf::solve_eqs, m, st));
        auto* r = alloc(if_change_simplifier, m, p, st);
        r->add_simplifier(s1);
        r->add_simplifier(s2);
        return r;
    };
    smt_params smtp(p);
    s.add_simplifier(alloc(rewriter_simplifier, m, p, st));
    if (smtp.m_propagate_values) s.add_simplifier(alloc(propagate_values, m, p, st));
    if (smtp.m_solve_eqs) s.add_simplifier(alloc(euf::solve_eqs, m, st));
    if (smtp.m_elim_unconstrained) s.add_simplifier(alloc(elim_unconstrained, m, st));
    if (smtp.m_nnf_cnf) s.add_simplifier(alloc(cnf_nnf_simplifier, m, p, st));
    if (smtp.m_macro_finder || smtp.m_quasi_macros) s.add_simplifier(alloc(eliminate_predicates, m, st));
    if (smtp.m_qe_lite) s.add_simplifier(mk_qe_lite_simplifier(m, p, st));
    if (smtp.m_pull_nested_quantifiers) s.add_simplifier(alloc(pull_nested_quantifiers_simplifier, m, p, st));
    if (smtp.m_max_bv_sharing) s.add_simplifier(mk_max_bv_sharing(m, p, st));
    if (smtp.m_refine_inj_axiom) s.add_simplifier(alloc(refine_inj_axiom_simplifier, m, p, st));
    if (smtp.m_bv_size_reduce) s.add_simplifier(alloc(bv::slice, m, st));
    if (smtp.m_distribute_forall) s.add_simplifier(alloc(distribute_forall_simplifier, m, p, st));
    if (smtp.m_bound_simplifier) s.add_simplifier(mk_bound_simplifier());
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

}


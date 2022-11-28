/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    card2bv.cpp

Abstract:

    convert cardinality constraints to bit-vectors

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/


#include "ast/simplifiers/card2bv.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/pb2bv_rewriter.h"

card2bv::card2bv(ast_manager& m, params_ref const& p, dependent_expr_state& fmls) :
    dependent_expr_simplifier(m, fmls), m_params(p) {}

void card2bv::reduce() {
    th_rewriter rw1(m, m_params);
    pb2bv_rewriter rw2(m, m_params);
                        
    expr_ref new_f1(m), new_f2(m);
    proof_ref new_pr(m);
    for (unsigned idx = m_qhead; !m_fmls.inconsistent() && idx < m_fmls.size(); idx++) {
        auto [f, d] = m_fmls[idx]();
        rw1(f, new_f1);        
        rw2(false, new_f1, new_f2, new_pr);        
        if (new_f2 != f) {
            TRACE("card2bv", tout << "Rewriting " << new_f1 << "\n" << new_f2 << "\n");
            m_fmls.update(idx, dependent_expr(m, new_f2, d));
            ++m_stats.m_num_rewrites;
        }
    }
    
    expr_ref_vector fmls(m);
    rw2.flush_side_constraints(fmls);
    for (expr* e : fmls)
        m_fmls.add(dependent_expr(m, e, nullptr));

    func_decl_ref_vector const& fns = rw2.fresh_constants();
    for (func_decl* f : fns)
        m_fmls.model_trail().hide(f);    

     advance_qhead();
}

void card2bv::collect_statistics(statistics& st) const {
    st.update("card2bv-rewrites", m_stats.m_num_rewrites);
}

void card2bv::collect_param_descrs(param_descrs& r) {
    r.insert("keep_cardinality_constraints", CPK_BOOL, "(default: true) retain cardinality constraints for solver");
    pb2bv_rewriter rw(m, m_params);
    rw.collect_param_descrs(r);
}

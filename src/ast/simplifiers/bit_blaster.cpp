/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster.cpp

Abstract:

    Apply bit-blasting

Author:

    Leonardo (leonardo) 2011-10-25

--*/

#include "ast/simplifiers/bit_blaster.h"


void bit_blaster::updt_params(params_ref const & p) {
    m_params.append(p);
    m_rewriter.updt_params(m_params);
}

void bit_blaster::collect_param_descrs(param_descrs & r) {
    insert_max_memory(r);
    insert_max_steps(r);
    r.insert("blast_mul", CPK_BOOL, "(default: true) bit-blast multipliers (and dividers, remainders).");
    r.insert("blast_add", CPK_BOOL, "(default: true) bit-blast adders.");
    r.insert("blast_quant", CPK_BOOL, "(default: false) bit-blast quantified variables.");
    r.insert("blast_full", CPK_BOOL, "(default: false) bit-blast any term with bit-vector sort, this option will make E-matching ineffective in any pattern containing bit-vector terms.");
}

void bit_blaster::reduce() {                            
    m_rewriter.start_rewrite();
    expr_ref   new_curr(m);
    proof_ref  new_pr(m);
    bool change = false;
    for (unsigned idx = m_qhead; idx < m_fmls.size(); idx++) {
        if (m_fmls.inconsistent())
            break;
        auto [curr, d] = m_fmls[idx]();
        m_rewriter(curr, new_curr, new_pr);
        m_num_steps += m_rewriter.get_num_steps();
        if (curr != new_curr) {
            change = true;                    
            TRACE("bit_blaster", tout << mk_pp(curr, m) << " -> " << new_curr << "\n";);
            m_fmls.update(idx, dependent_expr(m, new_curr, d));
        }
    }
    
    if (change) {
        obj_map<func_decl, expr*> const2bits;
        ptr_vector<func_decl> newbits;            
        m_rewriter.end_rewrite(const2bits, newbits);
        for (auto* f : newbits)
            m_fmls.model_trail().hide(f);
        for (auto const& [f, v] : const2bits) 
            m_fmls.model_trail().push(f, v, nullptr, {});
    }
    m_rewriter.cleanup();
    
    advance_qhead(m_fmls.size());
}


void bit_blaster::collect_statistics(statistics& st) const {
    st.update("bit-blaster-num-steps", m_num_steps);
}

void bit_blaster::push() {
    m_rewriter.push();
    dependent_expr_simplifier::push();
}

void bit_blaster::pop(unsigned n) {
    dependent_expr_simplifier::pop(n);
    m_rewriter.pop(n);
}

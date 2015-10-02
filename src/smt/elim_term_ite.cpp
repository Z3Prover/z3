/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    elim_term_ite.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-12.

Revision History:

--*/
#include"elim_term_ite.h"
#include"ast_smt2_pp.h"

void elim_term_ite::operator()(expr * n,                        
                               expr_ref_vector & new_defs,        
                               proof_ref_vector & new_def_proofs,
                               expr_ref & r,                     
                               proof_ref & pr) {

    m_coarse_proofs.reset();
    m_new_defs       = &new_defs;
    m_new_def_proofs = &new_def_proofs;
    reduce_core(n);
    expr * r2;
    proof * pr2;
    get_cached(n, r2, pr2);
    r = r2;
    switch (m.proof_mode()) {
    case PGM_DISABLED:
        pr = m.mk_undef_proof();
        break;
    case PGM_COARSE:
        remove_duplicates(m_coarse_proofs);
        pr = n == r2 ? m.mk_oeq_reflexivity(n) : m.mk_apply_defs(n, r, m_coarse_proofs.size(), m_coarse_proofs.c_ptr());
        break;
    case PGM_FINE:
        pr = pr2 == 0 ? m.mk_oeq_reflexivity(n) : pr2;
        break;
    }
    m_coarse_proofs.reset();
}

void elim_term_ite::reduce_core(expr * n) {
    m_todo.reset();
    if (!is_cached(n)) {
        m_todo.push_back(n);
        while (!m_todo.empty()) {
            expr * n = m_todo.back();
            if (is_cached(n)) {
                m_todo.pop_back();
            }
            else if (visit_children(n)) {
                m_todo.pop_back();
                reduce1(n);
            }
        }
    }
}

bool elim_term_ite::visit_children(expr * n) {
    bool visited = true;
    unsigned j;
    switch(n->get_kind()) {
    case AST_VAR:
        return true;
    case AST_APP:
        j = to_app(n)->get_num_args();
        while (j > 0) {
            --j;
            visit(to_app(n)->get_arg(j), visited);
        }
        return visited;
    case AST_QUANTIFIER: 
        visit(to_quantifier(n)->get_expr(), visited);
        return visited;
    default:
        UNREACHABLE();
        return true;
    }
}

void elim_term_ite::reduce1(expr * n) {
    switch (n->get_kind()) {
    case AST_VAR:
        cache_result(n, n, 0);
        break;
    case AST_APP:
        reduce1_app(to_app(n));
        break;
    case AST_QUANTIFIER:
        reduce1_quantifier(to_quantifier(n));
        break;
    default:
        UNREACHABLE();
    }
}

void elim_term_ite::reduce1_app(app * n) {
    m_args.reset();
    
    func_decl * decl = n->get_decl();
    proof_ref p1(m);
    get_args(n, m_args, p1);
    if (!m.fine_grain_proofs())
        p1 = 0;

    expr_ref r(m);
    r = m.mk_app(decl, m_args.size(), m_args.c_ptr());
    if (m.is_term_ite(r)) {
        expr_ref   new_def(m);
        proof_ref  new_def_pr(m);
        app_ref   new_r(m);
        proof_ref  new_pr(m);
        if (m_defined_names.mk_name(r, new_def, new_def_pr, new_r, new_pr)) {
            CTRACE("elim_term_ite_bug", new_def.get() == 0, tout << mk_ismt2_pp(r, m) << "\n";);
            SASSERT(new_def.get() != 0);
            m_new_defs->push_back(new_def);
            if (m.fine_grain_proofs()) {
                m_new_def_proofs->push_back(new_def_pr);
                new_pr = m.mk_transitivity(p1, new_pr);
            }
            else {
                // [Leo] This looks fishy... why do we add 0 into m_coarse_proofs when fine_grain_proofs are disabled? 
                new_pr = 0;
                if (m.proofs_enabled())
                    m_coarse_proofs.push_back(new_pr);
            }
        }
        else {
            SASSERT(new_def.get() == 0);
            if (!m.fine_grain_proofs())
                new_pr = 0;
        }
        cache_result(n, new_r, new_pr);
    }
    else {
        cache_result(n, r, p1);
    }
}

void elim_term_ite::reduce1_quantifier(quantifier * q) {
    expr *  new_body;
    proof * new_body_pr;
    get_cached(q->get_expr(), new_body, new_body_pr);
    
    quantifier * new_q = m.update_quantifier(q, new_body);
    proof *      p     = q == new_q ? 0 : m.mk_oeq_quant_intro(q, new_q, new_body_pr);   
    cache_result(q, new_q, p);
}




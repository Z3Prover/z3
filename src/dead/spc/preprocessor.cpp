/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    preprocessor.cpp

Abstract:

    Preprocessor

Author:

    Leonardo de Moura (leonardo) 2008-01-17.

Revision History:

--*/
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"preprocessor.h"
#include"for_each_expr.h"
#include"num_occurs.h"

preprocessor::preprocessor(ast_manager & m, defined_names & d, simplifier & s, preprocessor_params & p):
    m_params(p),
    m_manager(m),
    m_simp(s),
    m_nnf(m, d, p),
    m_cnf(m, d, p),
    m_der(m),
    m_push_app_ite(s, p.m_lift_ite == LI_CONSERVATIVE),
    m_cnf_todo(m),
    m_cnf_todo_prs(m),
    m_push_todo(m),
    m_push_todo_prs(m) {
    switch (m_params.m_cnf_mode) {
    case CNF_QUANT: 
        if (m_params.m_nnf_mode == NNF_SKOLEM)
            m_params.m_nnf_mode = NNF_QUANT;
        break;
    case CNF_OPPORTUNISTIC:
        if (m_params.m_nnf_mode == NNF_SKOLEM)
            m_params.m_nnf_mode = NNF_QUANT;
        break;
    case CNF_FULL:
        m_params.m_nnf_mode = NNF_FULL;
        break;
    default:
        break;
    }
}

#ifdef _TRACE
struct num_occurs_pp {
    
    ast_manager &  m_manager;
    std::ostream & m_out;
    num_occurs     m_occurs;

    num_occurs_pp(ast_manager & m, std::ostream & out, expr * root):
        m_manager(m),
        m_out(out) {
        m_occurs(root);
    }
    void operator()(var * n) {}
    void operator()(app * n) { 
        unsigned val = m_occurs.get_num_occs(n);
        if (val > 1 && m_manager.is_bool(n))
            m_out << "#" << n->get_id() << " -> " << val << " " << n->get_ref_count() << "\n";
    }
    void operator()(quantifier * n) {}
};
#endif

void preprocessor::operator()(expr * e, proof * in_pr, expr_ref_vector & result, proof_ref_vector & result_prs) {
    m_cnf_todo.reset();
    m_cnf_todo_prs.reset();
    
    expr_ref   r1(m_manager);
    proof_ref  pr1(m_manager);
    m_simp(e, r1, pr1);
    in_pr = m_manager.mk_modus_ponens(in_pr, pr1);
    
    expr_ref   r2(m_manager);
    proof_ref  pr2(m_manager);
    m_nnf(r1, m_cnf_todo, m_cnf_todo_prs, r2, pr2);
    in_pr = m_manager.mk_modus_ponens(in_pr, pr2);

    TRACE("preprocessor", tout << mk_ll_pp(r2, m_manager);
          num_occurs_pp proc(m_manager, tout, r2);
          for_each_expr(proc, r2););
    
    m_cnf_todo.push_back(r2);
    m_cnf_todo_prs.push_back(in_pr);

    unsigned sz = m_cnf_todo.size();
    for (unsigned i = 0; i < sz; i++) {
        m_push_todo.reset();
        m_push_todo_prs.reset();

        expr * e = m_cnf_todo.get(i);
        if (m_params.m_lift_ite != LI_NONE) {
            m_push_app_ite(e, r1, pr1);
        }
        else {
            r1  = e;
            pr1 = 0;
        }

        TRACE("preprocessor", tout << mk_ll_pp(r1, m_manager););
        
        expr_ref aux(r1, m_manager);
        m_simp(aux, r1, pr2);
        pr1 = m_manager.mk_transitivity(pr1, pr2);

        TRACE("preprocessor", tout << mk_ll_pp(r1, m_manager););

        aux = r1;
        m_der(aux, r1, pr2);
        pr1 = m_manager.mk_transitivity(pr1, pr2);

        TRACE("preprocessor", tout << mk_ll_pp(r1, m_manager););

        if (m_manager.proofs_enabled())
            in_pr = m_manager.mk_modus_ponens(m_cnf_todo_prs.get(i), pr1);
        else
            in_pr = 0;

        aux = r1;
        m_cnf(aux, m_push_todo, m_push_todo_prs, r1, pr1);
        m_push_todo.push_back(r1);

        TRACE("preprocessor", tout << mk_ll_pp(r1, m_manager););

        if (m_manager.proofs_enabled()) {
            in_pr = m_manager.mk_modus_ponens(in_pr, pr1);
            m_push_todo_prs.push_back(in_pr);
        }

        unsigned sz2 = m_push_todo.size();
        for (unsigned j = 0; j < sz2; j++) {
            expr * e = m_push_todo.get(j);
            m_simp(e, r1, pr1);
            
            TRACE("preprocessor", tout << mk_ll_pp(r1, m_manager););

            if (m_manager.proofs_enabled())
                in_pr = m_manager.mk_modus_ponens(m_push_todo_prs.get(j), pr1);
            else
                in_pr = 0;
            push_assertion(m_manager, r1, in_pr, result, result_prs);
        }
    }
}

/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    q_proof_checker.cpp

Abstract:

    Plugin for checking quantifier instantiations

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07

--*/

#include "ast/rewriter/var_subst.h"
#include "sat/smt/q_proof_checker.h"
#include "sat/smt/q_solver.h"

namespace q {
        
    expr_ref_vector proof_checker::clause(app* jst) {
        expr_ref_vector result(m);
        for (expr* arg : *jst) 
            if (!is_bind(arg))
                result.push_back(arg);
        return result;
    }

    expr_ref_vector proof_checker::binding(app* jst) {
        expr_ref_vector result(m);
        for (expr* arg : *jst) 
            if (is_bind(arg))
                result.push_back(to_app(arg)->get_arg(0));
        return result;        
    }
    
    void proof_checker::vc(app* jst, expr_ref_vector& clause) {
        expr* q = nullptr;
        if (!is_inst(jst))
            return;
        SASSERT(clause.size() >= 2);
        VERIFY(m.is_not(clause.get(0), q) && is_forall(q));
        auto inst = binding(jst);
        expr_ref qi = instantiate(m, to_quantifier(q), inst.begin());
        clause[0] = m.mk_not(qi);
    }

    bool proof_checker::is_inst(expr* jst) {
        return is_app(jst) && to_app(jst)->get_name() == m_inst && m.mk_proof_sort() == jst->get_sort();
    }

    bool proof_checker::is_bind(expr* e) {
        return is_app(e) && to_app(e)->get_name() == m_bind  && m.mk_proof_sort() == e->get_sort();
    }

    
}

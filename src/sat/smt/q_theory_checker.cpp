/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    q_theory_checker.cpp

Abstract:

    Plugin for checking quantifier instantiations

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07

--*/

#include "ast/rewriter/var_subst.h"
#include "sat/smt/q_theory_checker.h"
#include "sat/smt/q_solver.h"

namespace q {
        
    expr_ref_vector theory_checker::clause(app* jst) {
        expr_ref_vector result(m);
        for (expr* arg : *jst) 
            if (m.is_bool(arg))
                result.push_back(mk_not(m, arg));
        return result;
    }

    expr_ref_vector theory_checker::binding(app* jst) {
        expr_ref_vector result(m);
        for (expr* arg : *jst) 
            if (is_bind(arg)) {
                result.append(to_app(arg)->get_num_args(), to_app(arg)->get_args());
                break;
            }
        return result;        
    }
    
    bool theory_checker::vc(app* jst, expr_ref_vector const& clause0, expr_ref_vector& v) {
        expr* q = nullptr;
        if (!is_inst(jst))
            return false;
        auto clause1 = clause(jst);
        if (clause1.size() < 2)
            return false;
        bool universal = m.is_not(clause1.get(0), q) && is_forall(q);
        if (!universal) {
            q = clause1.get(0);
            if (!is_exists(q))
                return false;
        }
        auto inst = binding(jst);
        if (inst.size() < to_quantifier(q)->get_num_decls())
            return false;
        expr_ref qi = instantiate(m, to_quantifier(q), inst.begin());
        clause1[0] = universal ? m.mk_not(qi) : qi.get();
        v.reset();
        v.append(clause1);
        expr* n = nullptr;
        return universal ? qi == clause1.get(1) : m.is_not(clause1.get(1), n) && n == qi;
    }

    bool theory_checker::is_inst(expr* jst) {
        return is_app(jst) && to_app(jst)->get_name() == m_inst && m.mk_proof_sort() == jst->get_sort();
    }

    bool theory_checker::is_bind(expr* e) {
        return is_app(e) && to_app(e)->get_name() == m_bind  && m.mk_proof_sort() == e->get_sort();
    }

    
}

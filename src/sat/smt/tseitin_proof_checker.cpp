/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    tseitin_proof_checker.cpp

Abstract:

    Plugin for checking quantifier instantiations

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07


--*/

#include "sat/smt/tseitin_proof_checker.h"

namespace tseitin {

        
    expr_ref_vector proof_checker::clause(app* jst) {
        expr_ref_vector result(m);
        result.append(jst->get_num_args(), jst->get_args());
        return result;
    }
        
    bool proof_checker::check(app* jst) {
        expr* main_expr = nullptr;
        unsigned max_depth = 0;
        for (expr* arg : *jst) {
            if (get_depth(arg) > max_depth) {
                main_expr = arg;
                max_depth = get_depth(arg);
            }
        }
        if (!main_expr)
            return false;

        expr* a;
        if (m.is_not(main_expr, a)) {
            for (expr* arg : *jst)
                if (equiv(a, arg))
                    return true;
            
            if (m.is_and(a))
                for (expr* arg1 : *to_app(a))
                    for (expr* arg2 : *jst)
                        if (equiv(arg1, arg2))
                            return true;
            
            if (m.is_or(a))
                return false;
            if (m.is_implies(a))
                return false;
            if (m.is_eq(a))
                return false;
            if (m.is_ite(a))
                return false;
            if (m.is_distinct(a))
                return false;
        }
        return false;
    }

    bool proof_checker::equiv(expr* a, expr* b) {
        if (a == b)
            return true;
        expr* x, *y, *z, *u;
        if (m.is_eq(a, x, y) && m.is_eq(b, z, u))
            return x == u && y == z;
        return false;
    }


}

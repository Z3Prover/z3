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
            unsigned arg_depth = get_depth(arg);
            if (arg_depth > max_depth) {
                main_expr = arg;
                max_depth = arg_depth;
            }
            if (arg_depth == max_depth && m.is_not(main_expr)) 
                main_expr = arg;            
        }

        if (!main_expr)
            return false;

        expr* a;

        // (or (and a b) (not a) (not b))
        if (m.is_and(main_expr)) {            
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                if (m.is_not(arg, arg))
                    mark(arg);
            for (expr* arg : *to_app(main_expr)) {
                if (!is_marked(arg))
                    return false;
            }
            return true;
        }

        // (or (or a b) (not a))
        if (m.is_or(main_expr)) {            
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                if (m.is_not(arg, arg))
                    mark(arg);
            for (expr* arg : *to_app(main_expr)) {
                if (is_marked(arg))
                    return true;
            }
            return false;
        }
        
        if (m.is_not(main_expr, a)) {
            
            // (or (not a) a')
            for (expr* arg : *jst)
                if (equiv(a, arg))
                    return true;
            
            // (or (not (and a b)) a)
            if (m.is_and(a)) {
                scoped_mark sm(*this);
                for (expr* arg : *jst)
                    mark(arg);
                for (expr* arg : *to_app(a))
                    if (is_marked(arg))
                        return true;              
            }
            
            // (or (not (or a b) a b))
            if (m.is_or(a)) {
                scoped_mark sm(*this);
                for (expr* arg : *jst)
                    mark(arg);
                for (expr* arg : *to_app(a))
                    if (!is_marked(arg))
                        return false;
                return true;
            }

#if 0
            if (m.is_implies(a))
                return false;
            if (m.is_eq(a))
                return false;
            if (m.is_ite(a))
                return false;
            if (m.is_distinct(a))
                return false;
#endif
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

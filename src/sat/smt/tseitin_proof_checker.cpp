/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    tseitin_proof_checker.cpp

Abstract:

    Plugin for checking quantifier instantiations

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-07


--*/

#include "ast/ast_pp.h"
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

        expr* a, * x, * y, *z;

        // (or (and a b) (not a) (not b))
        // (or (and (not a) b) a (not b))
        if (m.is_and(main_expr)) {            
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                complement_mark(arg);

            for (expr* arg : *to_app(main_expr)) {
                if (!is_complement(arg))
                    return false;
            }
            return true;
        }

        // (or (or a b) (not a))
        if (m.is_or(main_expr)) {            
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                complement_mark(arg);
            for (expr* arg : *to_app(main_expr)) 
                if (is_complement(arg))
                    return true;            
            return false;
        }
        // (or (= a b) a b)
        // (or (= a b) (not a) (not b))
        // (or (= (not a) b) a (not b))
        if (m.is_eq(main_expr, x, y) && m.is_bool(x)) {
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                complement_mark(arg);
            if (is_marked(x) && is_marked(y))
                return true;
            if (is_complement(x) && is_complement(y))
                return true;
        }

        // (or (if a b c) (not b) (not c))
        // (or (if a b c) a (not c))
        // (or (if a b c) (not a) (not b))
        if (m.is_ite(main_expr, x, y, z) && m.is_bool(z)) {
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                complement_mark(arg);
            if (is_marked(x) && is_complement(z))
                return true;
            if (is_complement(x) && is_complement(y))
                return true;
            if (is_complement(y) && is_complement(z))
                return true;
            IF_VERBOSE(0, verbose_stream() << mk_pp(main_expr, m) << "\n");
        }
        

        // (or (=> a b) a)
        // (or (=> a b) (not b))
        if (m.is_implies(main_expr, x, y)) {
            scoped_mark sm(*this);
            for (expr* arg : *jst)
                complement_mark(arg);
            if (is_marked(x))
                return true;
            if (is_complement(y))
                return true;
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

            // (or (not (= a b) (not a) b)
            if (m.is_eq(a, x, y) && m.is_bool(x)) {
                scoped_mark sm(*this);                
                for (expr* arg : *jst)
                    complement_mark(arg);
                if (is_marked(x) && is_complement(y))
                    return true;
                if (is_marked(y) & is_complement(x))
                    return true;
            }

            // (or (not (if a b c)) (not a) b)
            // (or (not (if a b c)) a c)
            if (m.is_ite(a, x, y, z) && m.is_bool(z)) {
                scoped_mark sm(*this);
                for (expr* arg : *jst)
                    complement_mark(arg);
                if (is_complement(x) && is_marked(y))
                    return true;
                if (is_marked(x) && is_marked(z))
                    return true;
                if (is_marked(y) && is_marked(z))
                    return true;
            }   

            // (or (not (=> a b)) b (not a))
            if (m.is_implies(a, x, y)) {
                scoped_mark sm(*this);
                for (expr* arg : *jst)
                    complement_mark(arg);
                if (is_complement(x) && is_marked(y))
                    return true;
            }

            IF_VERBOSE(0, verbose_stream() << "miss " << mk_pp(main_expr, m) << "\n");

#if 0
            if (m.is_implies(a))
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

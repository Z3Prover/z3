/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    recfun_rewriter.cpp

Abstract:

    Rewriter recursive function applications to values

Author:

    Nikolaj Bjorner (nbjorner) 2020-04-26


--*/


#include "ast/rewriter/recfun_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/for_each_expr.h"
    
br_status recfun_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (m_rec.is_defined(f) && num_args > 0) {
        if (!m_rec.has_def(f))
            return BR_FAILED;
        recfun::def const& d = m_rec.get_def(f);
        if (!d.get_rhs())
            return BR_FAILED;
        auto r = d.get_rhs();
        bool safe_to_subst = true;
        for (unsigned i = 0; i < num_args; ++i) 
            if (!m.is_value(args[i]))
                safe_to_subst = false;

        // check if there is an argument that is a constructor
        // such that the recursive function can be partially evaluated.
        // at most one kind of accessor is allowed to prevent recursive
        // patterns that reconstruct the argument indirectly.
        // This can be relaxed to omitting at least one accessor, and probably other patterns.
        if (!safe_to_subst && !has_quantifiers(r)) {
            datatype::util u(m);
            auto is_decreasing = [&](unsigned i) {
                bool is_dec = true;
                unsigned idx = num_args - i - 1;
                func_decl* dec_fun = nullptr;
                for (auto t : subterms::all(expr_ref(r, m))) {
                    if (is_app(t) && any_of(*to_app(t), [&](expr* e) { return is_var(e) && to_var(e)->get_idx() == idx; })) {
                        if (!u.is_accessor(t) && !u.is_is(t) && !u.is_recognizer(t))
                            is_dec = false;                       
                        else if (u.is_accessor(t) && dec_fun && to_app(t)->get_decl() != dec_fun)
                            is_dec = false;
                        else if (u.is_accessor(t))                        
                            dec_fun = to_app(t)->get_decl();
                    }
                }
                return is_dec;
            };
            for (unsigned i = 0; i < num_args; ++i) {
                auto arg = args[i];
                if (u.is_constructor(arg) && is_decreasing(i)) {
                    safe_to_subst = true;
                    break;
                }
            }            
        }
        if (safe_to_subst) {
            var_subst sub(m);
            result = sub(d.get_rhs(), num_args, args);
            return BR_REWRITE_FULL;
        }
        return BR_FAILED;
        
    }
    else 
        return BR_FAILED;
}



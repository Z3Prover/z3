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
#include "params/rewriter_params.hpp"

void recfun_rewriter::updt_params(params_ref const &p) {
    rewriter_params rp(p);
    m_recfun_unfold = rp.unfold_recursive_functions();
}
    
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
        if (!m_recfun_unfold) {
            for (auto t : subterms::all(expr_ref(r, m)))
                if (is_uninterp(t))
                    return BR_FAILED;
        }            

        // check if there is an argument that is a constructor
        // such that the recursive function can be partially evaluated.
        // At most one kind of accessor is allowed to prevent recursive
        // patterns that reconstruct the argument indirectly, unless the
        // argument is ground: accessors of a ground constructor term are
        // strictly smaller ground terms, so unfolding terminates.
        // Model evaluation relies on the ground case to check a quantifier over a
        // recursively defined function whose recursion argument is ground
        // (e.g. forall a. isList(a, items)) - see smt_model_finder.
        if (!safe_to_subst && !has_quantifiers(r)) {
            datatype::util u(m);
            for (unsigned i = 0; i < num_args; ++i) {
                auto arg = args[i];
                if (u.is_constructor(arg) && is_decreasing_arg(f, i, is_ground(arg))) {
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

bool recfun_rewriter::is_decreasing_arg(func_decl* f, unsigned i, bool allow_any_accessor) {
    if (!m_rec.is_defined(f) || !m_rec.has_def(f))
        return false;
    recfun::def const& d = m_rec.get_def(f);
    expr* r = d.get_rhs();
    if (!r || has_quantifiers(r))
        return false;
    datatype::util u(m);
    unsigned num_args = f->get_arity();
    unsigned idx = num_args - i - 1;
    func_decl* dec_fun = nullptr;
    for (auto t : subterms::all(expr_ref(r, m))) {
        if (is_app(t) && any_of(*to_app(t), [&](expr* e) { return is_var(e) && to_var(e)->get_idx() == idx; })) {
            if (!u.is_accessor(t) && !u.is_is(t) && !u.is_recognizer(t))
                return false;
            if (u.is_accessor(t)) {
                if (!allow_any_accessor && dec_fun && to_app(t)->get_decl() != dec_fun)
                    return false;
                dec_fun = to_app(t)->get_decl();
            }
        }
    }
    return dec_fun != nullptr || !allow_any_accessor;
}

bool recfun_rewriter::is_recfun_with_ground_recursion_args(app* t) {
    func_decl* f = t->get_decl();
    if (!m_rec.is_defined(f) || !m_rec.has_def(f))
        return false;
    datatype::util dt(m);
    bool has_decreasing = false;
    unsigned i = 0;
    for (expr* arg : *t) {
        sort* s = arg->get_sort();
        if (!is_ground(arg)) {
            if (!m.is_uninterp(s))
                return false;
        }
        else if (dt.is_datatype(s) && is_decreasing_arg(f, i, true)) {
            has_decreasing = true;
        }
        ++i;
    }
    return has_decreasing;
}

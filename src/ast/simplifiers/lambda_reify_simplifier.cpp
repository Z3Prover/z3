/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    lambda_reify_simplifier.cpp

Abstract:

    see lambda_reify_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/

#include "ast/simplifiers/lambda_reify_simplifier.h"
#include "ast/used_vars.h"
#include "ast/rewriter/var_subst.h"

// Recursively replace lambda-literal subterms of e with applications of a
// fresh function symbol. ctx_sorts[i] is the sort of the enclosing bound
// variable with de Bruijn index i at this position (innermost first); when
// a lambda literal is encountered, any of these enclosing variables that
// occur free in its body are lifted as extra parameters of the fresh
// function, and the defining axiom universally quantifies over exactly the
// lifted enclosing variables together with the lambda's own parameters:
//
//   ! [A] : P( (lambda (X) body(A, X)) )
//     ~~>
//   ! [A] : P( lam(A) )   with axiom   ! [A, X] : (select (lam A) X) = body(A, X)
//
// A lambda literal that is the direct rhs/lhs of a top-level equality naming
// a 0-ary constant (the shape lambda_simplifier targets) is left untouched:
// that shape is handled by inlining, not reification.
expr* lambda_reify_simplifier::reify_rec(expr* e, ptr_vector<sort> const& ctx_sorts, expr_ref_vector& new_defs, expr_ref_vector& pinned) {
    expr* result = e;
    if (is_lambda(e)) {
        quantifier* q = to_quantifier(e);
        unsigned n = q->get_num_decls();
        // extend the context with the lambda's own parameters (innermost).
        ptr_vector<sort> inner_ctx;
        for (unsigned i = 0; i < n; ++i)
            inner_ctx.push_back(q->get_decl_sort(i));
        for (sort* s : ctx_sorts)
            inner_ctx.push_back(s);
        expr_ref new_body(reify_rec(q->get_expr(), inner_ctx, new_defs, pinned), m);

        // determine which enclosing variables (de Bruijn index >= n, relative
        // to new_body) occur free in new_body.
        used_vars uv;
        uv.process(new_body);
        unsigned max_outer = ctx_sorts.size();
        ptr_vector<sort> lifted_sorts;
        unsigned_vector lifted_outer; // outer position (0 = innermost enclosing var)
        for (unsigned outer = 0; outer < max_outer; ++outer) {
            if (uv.contains(n + outer)) {
                lifted_sorts.push_back(ctx_sorts[outer]);
                lifted_outer.push_back(outer);
            }
        }
        unsigned k = lifted_sorts.size();

        func_decl_ref fn(m.mk_fresh_func_decl("lam", "", k, lifted_sorts.data(), q->get_sort()), m);

        // 1) build the application used inside the defining axiom: there,
        //    the lifted vars are the last k of the n+k quantified vars,
        //    at de Bruijn indices n .. n+k-1 (in lifted_outer order).
        ptr_vector<expr> axiom_fn_args;
        for (unsigned j = 0; j < k; ++j)
            axiom_fn_args.push_back(m.mk_var(n + j, lifted_sorts[j]));
        app_ref c_in_axiom(m.mk_app(fn, axiom_fn_args.size(), axiom_fn_args.data()), m);
        pinned.push_back(c_in_axiom);

        ptr_vector<expr> sel_args;
        sel_args.push_back(c_in_axiom);
        for (unsigned i = 0; i < n; ++i)
            sel_args.push_back(m.mk_var(i, q->get_decl_sort(i)));
        expr_ref sel(m_array.mk_select(sel_args.size(), sel_args.data()), m);
        expr_ref eq(m.mk_eq(sel, new_body), m);

        ptr_vector<sort> decl_sorts;
        svector<symbol> decl_names;
        for (unsigned i = 0; i < n; ++i) {
            decl_sorts.push_back(q->get_decl_sort(i));
            decl_names.push_back(q->get_decl_name(i));
        }
        for (unsigned j = 0; j < k; ++j) {
            decl_sorts.push_back(lifted_sorts[j]);
            decl_names.push_back(symbol(std::string("lamv").append(std::to_string(j)).c_str()));
        }
        expr_ref ax(m.mk_forall(decl_sorts.size(), decl_sorts.data(), decl_names.data(), eq), m);
        pinned.push_back(ax);
        new_defs.push_back(ax);
        ++m_stats.m_num_reified;

        // 2) build the application used at the occurrence site: there, the
        //    lifted vars use their *caller* frame indices (ctx_sorts' own
        //    indexing, i.e., outer position directly).
        ptr_vector<expr> call_args;
        for (unsigned outer : lifted_outer)
            call_args.push_back(m.mk_var(outer, ctx_sorts[outer]));
        result = m.mk_app(fn, call_args.size(), call_args.data());
        pinned.push_back(result);
    }
    else if (is_app(e)) {
        app* a = to_app(e);
        // Beta-redex shortcut: (select (lambda ...) args...) should be beta-
        // reduced rather than having its lambda argument reified — reifying
        // here would turn a trivial simplification into an opaque function
        // call and can prevent otherwise-easy proofs (observed regression:
        // AGT037^1.p and others solve instantly without this guard failing).
        if (m_array.is_select(a) && a->get_num_args() >= 1 && is_lambda(a->get_arg(0))) {
            expr_ref beta(m);
            var_subst subst(m, false);
            quantifier* q = to_quantifier(a->get_arg(0));
            expr_ref_vector args(m);
            for (unsigned i = 1; i < a->get_num_args(); ++i)
                args.push_back(a->get_arg(i));
            beta = subst(q->get_expr(), args.size(), args.data());
            expr* new_beta = reify_rec(beta, ctx_sorts, new_defs, pinned);
            pinned.push_back(new_beta);
            return new_beta;
        }
        bool changed = false;
        ptr_vector<expr> new_args;
        for (expr* arg : *a) {
            expr* new_arg = reify_rec(arg, ctx_sorts, new_defs, pinned);
            new_args.push_back(new_arg);
            changed |= new_arg != arg;
        }
        if (changed) {
            result = m.mk_app(a->get_decl(), new_args.size(), new_args.data());
            pinned.push_back(result);
        }
    }
    else if (is_quantifier(e) && !is_lambda(e)) {
        quantifier* q = to_quantifier(e);
        unsigned n = q->get_num_decls();
        ptr_vector<sort> inner_ctx;
        for (unsigned i = 0; i < n; ++i)
            inner_ctx.push_back(q->get_decl_sort(i));
        for (sort* s : ctx_sorts)
            inner_ctx.push_back(s);
        expr_ref new_body(reify_rec(q->get_expr(), inner_ctx, new_defs, pinned), m);
        if (new_body.get() != q->get_expr()) {
            result = m.update_quantifier(q, new_body);
            pinned.push_back(result);
        }
    }
    return result;
}

void lambda_reify_simplifier::reduce() {
    expr_ref_vector new_defs(m);
    expr_ref_vector pinned(m);
    ptr_vector<sort> empty_ctx;

    for (unsigned idx : indices()) {
        expr* f = m_fmls[idx].fml();
        // Skip a top-level macro-defining equality (c = lambda ...): that
        // shape is left for lambda_simplifier to inline; reifying it here
        // would just re-wrap the same lambda in a different fresh name.
        expr* lhs = nullptr, * rhs = nullptr;
        if (m.is_eq(f, lhs, rhs) && ((is_uninterp_const(lhs) && is_lambda(rhs)) ||
                                      (is_uninterp_const(rhs) && is_lambda(lhs))))
            continue;
        expr_ref new_fml(reify_rec(f, empty_ctx, new_defs, pinned), m);
        if (new_fml.get() == f)
            continue;
        proof_ref new_pr(m);
        m_rewriter(new_fml, new_fml, new_pr);
        m_fmls.update(idx, dependent_expr(m, new_fml, nullptr, m_fmls[idx].dep()));
    }

    for (expr* ax : new_defs)
        m_fmls.add(dependent_expr(m, ax, nullptr, nullptr));
}

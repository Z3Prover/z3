/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    lambda_reify_simplifier.h

Abstract:

    Reify lambda literals that occur as (sub)terms of predicate-like sort
    (i.e., array sort with Boolean-ish range, such as a shallow embedding
    of an HOL predicate T -> $o) into a fresh opaque 0-ary constant plus a
    defining "select"-equality axiom:

        c = (lambda (x) body)     ~~>     c (fresh), forall x. (select c x) = body[x]

    and, symmetrically, for a lambda literal appearing directly as an
    argument at some occurrence (e.g., f(lambda (x) body)):

        f( (lambda (x) body) )    ~~>     f(c),  forall x. (select c x) = body[x]

    Motivation: E-matching/HO pattern matching triggers are built around
    applications of uninterpreted function/constant symbols. A raw lambda
    term occurring inside a ground assertion (either directly, or after
    lambda_simplifier inlines a macro-defined constant back into its use
    sites) is inert for matching purposes: axioms whose triggers expect an
    applied constant (e.g., finite(A1)) can never fire against a subterm
    that is a bare (lambda ...) node, even though it is semantically an
    ordinary predicate. Reifying the lambda into a fresh named constant
    with a universally quantified defining equation restores the shape
    that matching already handles well, without changing the meaning of
    the formula (the new axiom is a conservative extension: c is fully
    determined by the equation and does not occur in it other than via
    select).

    This is the dual of lambda_simplifier: lambda_simplifier eliminates a
    named constant in favor of inlining its lambda body (useful when the
    lambda body itself should be beta-reduced away, e.g., under a select);
    lambda_reify_simplifier goes the other way, introducing a name for a
    lambda literal so that it can participate in ordinary E-matching. Both
    can't fire on the same term in the same pass (guarded by an "is this
    already just a bare constant?" check on each side), so it is safe to
    run lambda_reify_simplifier unconditionally after lambda_simplifier.

Author:

    Nikolaj Bjorner (nbjorner) 2026

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/array_decl_plugin.h"

class lambda_reify_simplifier : public dependent_expr_simplifier {

    struct stats {
        unsigned m_num_reified = 0;
        void reset() { m_num_reified = 0; }
    };

    th_rewriter  m_rewriter;
    array_util   m_array;
    stats        m_stats;

    // Rewrite lambda literals occurring anywhere in e into applications of a
    // fresh function symbol, accumulating defining axioms into new_defs.
    // ctx_sorts gives the sorts of the enclosing bound variables at the
    // current position, innermost first (ctx_sorts[i] is the sort of the
    // variable with de Bruijn index i here); a lambda literal referencing
    // such variables is lifted into an n-ary fresh function of those
    // enclosing sorts, so its defining axiom can universally quantify over
    // them together with the lambda's own parameters. No caching across
    // recursive calls: a subterm's transformation depends on ctx_sorts, so
    // memoizing by expr* alone would be unsound if the same subterm is
    // shared under different binder contexts.
    expr* reify_rec(expr* e, ptr_vector<sort> const& ctx_sorts, expr_ref_vector& new_defs, expr_ref_vector& pinned);

public:
    lambda_reify_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m),
        m_array(m) {
        updt_params(p);
    }

    char const* name() const override { return "lambda-reify"; }

    void reduce() override;

    void collect_statistics(statistics& st) const override {
        st.update("lambda-literals-reified", m_stats.m_num_reified);
    }

    void reset_statistics() override { m_stats.reset(); }

    void updt_params(params_ref const& p) override {
        m_rewriter.updt_params(p);
    }

    void collect_param_descrs(param_descrs& r) override {
        th_rewriter::get_param_descrs(r);
    }
};

/*
  ADD_SIMPLIFIER("lambda-reify", "reify lambda literals occurring as subterms into fresh named constants with a select-defining axiom, so they participate in E-matching.", "alloc(lambda_reify_simplifier, m, p, s)")
 */

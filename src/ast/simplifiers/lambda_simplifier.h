/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    lambda_simplifier.h

Abstract:

    Unfold constants that are defined by an equality to a lambda term,
    e.g., (assert (= c (lambda ((x T)) body))), and inline occurrences
    of the constant elsewhere by the (beta-reducible) lambda term.

    This targets shallow embeddings of higher-order logic in TPTP/THF
    problems, where modal or higher-order operators are introduced as
    0-ary constants of function/array sort whose meaning is pinned down
    by such an equality (rather than the classical macro shape
    (= (f x1 .. xn) body(x1 .. xn)) that is already handled by
    eliminate_predicates/macro_finder). Once occurrences of the constant
    are replaced by the lambda term, ordinary rewriting (array_rewriter)
    beta-reduces select-of-lambda applications automatically.

Author:

    Nikolaj Bjorner (nbjorner) 2024

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "util/obj_hashtable.h"

class lambda_simplifier : public dependent_expr_simplifier {

    struct stats {
        unsigned m_num_macros = 0;
        unsigned m_num_substs = 0;
        void reset() { m_num_macros = 0; m_num_substs = 0; }
    };

    struct config {
        // Skip inlining a macro whose constant occurs in more than this many
        // formulas: inlining a widely-shared definition duplicates its body
        // at every use site and can blow up formula size (observed regression
        // on TPTP's ITP domain, where type-class operations are shared across
        // hundreds of assertions).
        unsigned m_max_occs = 16;
    };

    th_rewriter               m_rewriter;
    stats                     m_stats;
    config                    m_config;

    // find (= c L) / (= L c) shaped assertions where c is a 0-ary uninterpreted
    // constant, L is (headed by) a lambda term, and c does not occur in L.
    void collect_macros(obj_map<func_decl, expr*>& raw_defs,
                         obj_map<func_decl, unsigned>& def_idx,
                         expr_ref_vector& pinned);

    // remove candidates whose constant is used too widely to be safely inlined.
    void filter_by_occurrences(obj_map<func_decl, expr*>& raw_defs,
                                obj_map<func_decl, unsigned>& def_idx);

    // resolve nested macro references to a fixpoint, guarding against cycles.
    expr* resolve(func_decl* d,
                  obj_map<func_decl, expr*> const& raw_defs,
                  obj_map<func_decl, expr*>& resolved,
                  obj_hashtable<func_decl>& in_progress,
                  obj_hashtable<func_decl>& failed,
                  expr_ref_vector& pinned);

public:
    lambda_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        m_rewriter(m) {
        updt_params(p);
    }

    char const* name() const override { return "lambda-macros"; }

    void reduce() override;

    void collect_statistics(statistics& st) const override {
        st.update("lambda-macros-found", m_stats.m_num_macros);
        st.update("lambda-macros-substituted", m_stats.m_num_substs);
    }

    void reset_statistics() override { m_stats.reset(); }

    void updt_params(params_ref const& p) override {
        m_rewriter.updt_params(p);
        m_config.m_max_occs = p.get_uint("lambda_macros_max_occs", m_config.m_max_occs);
    }

    void collect_param_descrs(param_descrs& r) override {
        th_rewriter::get_param_descrs(r);
        r.insert("lambda_macros_max_occs", CPK_UINT, "max number of formulas a lambda-defined constant may occur in to still be inlined", "16");
    }
};

/*
  ADD_SIMPLIFIER("lambda-macros", "unfold constants defined as lambda terms (shallow embeddings of higher-order operators), inlining and beta-reducing occurrences.", "alloc(lambda_simplifier, m, p, s)")
 */

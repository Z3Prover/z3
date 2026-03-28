/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    normalize_bounds.h

Abstract:

    Replace x with x' + l, when l <= x
    where x' is a fresh variable.
    Note that, after the transformation 0 <= x'.

Author:

    Leonardo de Moura (leonardo) 2011-10-21.
    Ported to simplifier by Nikolaj Bjorner (nbjorner) 2024.

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/bound_manager.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/expr_substitution.h"
#include "ast/arith_decl_plugin.h"

class normalize_bounds_simplifier : public dependent_expr_simplifier {
    arith_util  m_util;
    th_rewriter m_rw;
    bool        m_normalize_int_only;
    params_ref  m_params;

    bool is_target(expr* var, bound_manager& bm, rational& val) const {
        bool strict;
        return is_uninterp_const(var) &&
               (!m_normalize_int_only || m_util.is_int(var)) &&
               bm.has_lower(var, val, strict) &&
               !val.is_zero();
    }

public:
    normalize_bounds_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s) :
        dependent_expr_simplifier(m, s),
        m_util(m),
        m_rw(m, p),
        m_normalize_int_only(true),
        m_params(p) {
        updt_params(p);
    }

    char const* name() const override { return "normalize-bounds"; }

    bool supports_proofs() const override { return true; }

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        m_rw.updt_params(m_params);
        m_normalize_int_only = m_params.get_bool("norm_int_only", true);
    }

    void collect_param_descrs(param_descrs& r) override {
        r.insert("norm_int_only", CPK_BOOL,
                 "normalize only the bounds of integer constants.", "true");
    }

    void reduce() override {
        // pass 1: collect bounds over indices()
        bound_manager bm(m);
        for (unsigned idx : indices())
            bm(m_fmls[idx].fml(), m_fmls[idx].dep(), nullptr);

        // check whether there is anything to do
        bool has_lower = false;
        rational val;
        for (expr* e : bm) {
            if (is_target(e, bm, val)) {
                has_lower = true;
                break;
            }
        }
        if (!has_lower)
            return;

        // pass 2: build substitution and apply
        expr_substitution subst(m);
        for (expr* x : bm) {
            if (!is_target(x, bm, val))
                continue;
            sort* s = x->get_sort();
            app* x_prime = m.mk_fresh_const(nullptr, s);
            expr* def = m_util.mk_add(x_prime, m_util.mk_numeral(val, s));
            subst.insert(x, def);
            m_fmls.model_trail().hide(x_prime->get_decl());
            m_fmls.model_trail().push(to_app(x)->get_decl(), def, nullptr, {});
        }

        m_rw.set_substitution(&subst);
        expr_ref new_curr(m);
        proof_ref new_pr(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_rw(d.fml(), new_curr, new_pr);
            m_fmls.update(idx, dependent_expr(m, new_curr, mp(d.pr(), new_pr), d.dep()));
        }
        m_rw.set_substitution(nullptr);
    }
};

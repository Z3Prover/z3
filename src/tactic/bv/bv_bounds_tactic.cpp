/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv_bounds_tactic.cpp

Abstract:

    Contextual bounds simplification tactic.

Author:

    Nuno Lopes (nlopes) 2016-2-12

    Nikolaj Bjorner (nbjorner) 


--*/

#include "ast/bv_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/bv_bounds_base.h"
#include "ast/simplifiers/dominator_simplifier.h"
#include "ast/simplifiers/bv_bounds_simplifier.h"
#include "tactic/bv/bv_bounds_tactic.h"
#include "tactic/core/ctx_simplify_tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include <climits>


namespace {


    class bv_bounds_simplifier : public ctx_simplify_tactic::simplifier, public bv::bv_bounds_base {
        params_ref         m_params;

    public:
        bv_bounds_simplifier(ast_manager& m, params_ref const& p) : bv::bv_bounds_base(m), m_params(p) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) override {
            m_propagate_eq = p.get_bool("propagate_eq", false);
        }

        static void get_param_descrs(param_descrs& r) {
            r.insert("propagate-eq", CPK_BOOL, "propagate equalities from inequalities", "false");
        }

        bool assert_expr(expr * t, bool sign) override {
            return assert_expr_core(t, sign);
        }

        bool simplify(expr* t, expr_ref& result) override {
            return simplify_core(t, result);
        }

        bool may_simplify(expr* t) override {
            if (m_bv.is_numeral(t))
                return false;

            while (m.is_not(t, t));

            for (auto & v : m_bound) 
                if (contains(t, v.m_key)) 
                    return true;

            expr* t1;
            bv::interval b;
            // skip common case: single bound constraint without any context for simplification
            if (is_bound(t, t1, b)) 
                return b.is_full() || m_bound.contains(t1);

            return contains_bound(t);
        }

        void pop(unsigned num_scopes) override {
            pop_core(num_scopes);
        }

        simplifier * translate(ast_manager & m) override {
            return alloc(bv_bounds_simplifier, m, m_params);
        }

        unsigned scope_level() const override {
            return m_scopes.size();
        }
    };

}

tactic * mk_bv_bounds_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(ctx_simplify_tactic, m, alloc(bv_bounds_simplifier, m, p), p));
}

tactic* mk_dom_bv_bounds_tactic(ast_manager& m, params_ref const& p) {
    return alloc(dependent_expr_state_tactic, m, p, mk_bv_bounds_simplifier);
}

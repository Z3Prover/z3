/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_bounds_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-27

--*/

#include "ast/simplifiers/bv_bounds_simplifier.h"
#include "ast/simplifiers/dominator_simplifier.h"
#include "ast/rewriter/bv_bounds_base.h"
#include "ast/rewriter/dom_simplifier.h"


class dom_bv_bounds_simplifier : public dom_simplifier, public bv::bv_bounds_base {
    params_ref         m_params;
    
public:
    dom_bv_bounds_simplifier(ast_manager& m, params_ref const& p) : bv_bounds_base(m), m_params(p) {
        updt_params(p);
    }
    
    ~dom_bv_bounds_simplifier() override {
    }
    
    void updt_params(params_ref const & p) override {
        m_propagate_eq = p.get_bool("propagate_eq", false);
    }
    
    void collect_param_descrs(param_descrs& r) override {
        r.insert("propagate-eq", CPK_BOOL, "propagate equalities from inequalities", "false");
    }
    
    bool assert_expr(expr * t, bool sign) override {
        return assert_expr_core(t, sign);
    }
    
    void operator()(expr_ref& r) override {
        expr_ref result(m);
        simplify_core(r, result);
        if (result)
            r = result;
    }       
    
    void pop(unsigned num_scopes) override {
        pop_core(num_scopes);
    }
    
    dom_simplifier * translate(ast_manager & m) override {
        return alloc(dom_bv_bounds_simplifier, m, m_params);
    }
    
    unsigned scope_level() const override {
        return m_scopes.size();
    }
};

dependent_expr_simplifier* mk_bv_bounds_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s) {
    return alloc(dominator_simplifier, m, s, alloc(dom_bv_bounds_simplifier, m, p), p); 
}

/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    macro_replacer.cpp

Abstract:

    Abstract (functor) for applying macro replacement.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

Notes:

--*/

#include "ast/rewriter/macro_replacer.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"

/**
* Rewriting formulas using macro definitions.
*/
struct macro_replacer::macro_replacer_cfg : public default_rewriter_cfg {
    ast_manager& m;
    macro_replacer& ep;
    expr_dependency_ref& m_used_macro_dependencies;
    expr_ref_vector m_trail;

    macro_replacer_cfg(ast_manager& m, macro_replacer& ep, expr_dependency_ref& deps) :
        m(m),
        ep(ep),
        m_used_macro_dependencies(deps),
        m_trail(m)
    {}

    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl* f) const { return false; }
    br_status reduce_app(func_decl* f, unsigned num, expr* const* args, expr_ref& result, proof_ref& result_pr) {
        result_pr = nullptr;
        return BR_FAILED;
    }

    /**
    * adapted from macro_manager.cpp
    * Perhaps hoist and combine?
    */
    bool reduce_quantifier(quantifier* old_q,
        expr* new_body,
        expr* const* new_patterns,
        expr* const* new_no_patterns,
        expr_ref& result,
        proof_ref& result_pr) {

        bool erase_patterns = false;
        for (unsigned i = 0; !erase_patterns && i < old_q->get_num_patterns(); i++) 
            if (old_q->get_pattern(i) != new_patterns[i])
                erase_patterns = true;
        
        for (unsigned i = 0; !erase_patterns && i < old_q->get_num_no_patterns(); i++) 
            if (old_q->get_no_pattern(i) != new_no_patterns[i])
                erase_patterns = true;
        
        if (erase_patterns) 
            result = m.update_quantifier(old_q, 0, nullptr, 0, nullptr, new_body);
        
        if (erase_patterns && m.proofs_enabled()) 
            result_pr = m.mk_rewrite(old_q, result);
        
        return erase_patterns;
    }

    bool get_subst(expr* _n, expr*& r, proof*& p) {
        if (!is_app(_n))
            return false;
        p = nullptr;
        app* n = to_app(_n);
        func_decl* d = n->get_decl();
        app_ref head(m);
        expr_ref def(m);
        expr_dependency_ref dep(m);
        if (ep.has_macro(d, head, def, dep)) {
            unsigned num = head->get_num_args();
            ptr_buffer<expr> subst_args;
            subst_args.resize(num, 0);
            for (unsigned i = 0; i < num; i++) {
                var* v = to_var(head->get_arg(i));
                VERIFY(v->get_idx() < num);
                unsigned nidx = num - v->get_idx() - 1;
                SASSERT(!subst_args[nidx]);
                subst_args[nidx] = n->get_arg(i);
            }
            var_subst s(m);
            expr_ref rr = s(def, num, subst_args.data());
            r = rr;
            m_trail.push_back(rr);
            m_used_macro_dependencies = m.mk_join(m_used_macro_dependencies, dep);
            // skip proof terms for simplifiers
            return true;
        }
        
        return false;
    }
};

struct macro_replacer::macro_replacer_rw : public rewriter_tpl<macro_replacer::macro_replacer_cfg> {
    macro_replacer::macro_replacer_cfg m_cfg;

    macro_replacer_rw(ast_manager& m, macro_replacer& ep, expr_dependency_ref& deps) :
        rewriter_tpl<macro_replacer::macro_replacer_cfg>(m, false, m_cfg),
        m_cfg(m, ep, deps)
    {}
};


void macro_replacer::insert(app* head, expr* def, expr_dependency* dep) {
    func_decl* f = head->get_decl();
    m_trail.push_back(head);
    m_trail.push_back(def);
    m_deps.push_back(dep);
    m_map.insert(f, std::tuple(head, def, dep));
}

void macro_replacer::operator()(expr* t, expr_dependency* dep_in, expr_ref& result, expr_dependency_ref& dep_out) {
    expr_dependency_ref _dep_in(dep_in, m);
    macro_replacer_rw exp(m, *this, dep_out);
    exp(t, result);
    if (!dep_in)
        return;
    // update dependencies if needed
    m_dep_exprs.reset();
    m.linearize(dep_in, m_dep_exprs);
    unsigned sz = m_trail.size();
    for (expr*& d : m_dep_exprs) {
        exp(d, result);
        if (result != d) {
            d = result.get();
            m_trail.push_back(result);
        }
    }
    if (sz != m_trail.size()) {
        dep_in = m.mk_join(m_dep_exprs.size(), m_dep_exprs.data());
        m_trail.shrink(sz);
    }
    dep_out = m.mk_join(dep_in, dep_out);
}

bool macro_replacer::has_macro(func_decl* f, app_ref& head, expr_ref& def, expr_dependency_ref& dep) {
    std::tuple<app*,expr*,expr_dependency*> v;
    if (!m_map.find(f, v))
        return false;
    auto const& [h, d, dp] = v;
    head = h;
    def = d;
    dep = dp;
    return true;
}

/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    propagate_values.h

Abstract:

    relatively cheap value propagation

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

Notes:
    
    Incremental version of propagate_values_tactic

--*/

#include "params/tactic_params.hpp"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/shared_occs.h"
#include "ast/simplifiers/propagate_values.h"

propagate_values::propagate_values(ast_manager& m, dependent_expr_state& fmls):
    dependent_expr_simplifier(m, fmls),
    m_rewriter(m) {
    m_rewriter.set_order_eq(true);
    m_rewriter.set_flat_and_or(false);
}

void propagate_values::reduce() {
    shared_occs shared(m, true);
    expr_substitution subst(m, true, false);
    expr* x, * y;

    auto add_shared = [&]() {
        shared_occs_mark visited;
        shared.reset();
        for (unsigned i = 0; i < m_fmls.size(); ++i)
            shared(m_fmls[i].fml(), visited);
    };
    
    auto add_sub = [&](dependent_expr const& de) {
        auto const& [f, dep] = de();
        if (m.is_not(f, x) && shared.is_shared(x))
            subst.insert(x, m.mk_false(), dep);
        else if (shared.is_shared(f))
            subst.insert(f, m.mk_true(), dep);
        if (m.is_eq(f, x, y)) {
            if (m.is_value(x) && shared.is_shared(y))
                subst.insert(y, x, dep);
            else if (m.is_value(y) && shared.is_shared(x))
                subst.insert(x, y, dep);
        }
    };
    
    auto process_fml = [&](unsigned i) {
        auto [f, dep] = m_fmls[i]();
        expr_ref fml(m);
        proof_ref pr(m);
        m_rewriter(f, fml, pr);
        if (fml != f) {
            dep = m.mk_join(dep, m_rewriter.get_used_dependencies());
            m_fmls.update(i, dependent_expr(m, fml, dep));
            ++m_stats.m_num_rewrites;
        }
        m_rewriter.reset_used_dependencies();
        add_sub(m_fmls[i]);
    };

    auto init_sub = [&]() {
        add_shared();
        subst.reset();
        m_rewriter.reset();
        m_rewriter.set_substitution(&subst);
        for (unsigned i = 0; i < m_qhead; ++i)
            add_sub(m_fmls[i]);
    };
    
    unsigned rw = m_stats.m_num_rewrites + 1;
    for (unsigned r = 0; r < m_max_rounds && rw != m_stats.m_num_rewrites; ++r) {            
        rw = m_stats.m_num_rewrites;
        init_sub();
        for (unsigned i = m_qhead; i < m_fmls.size() && !m_fmls.inconsistent(); ++i)
            process_fml(i);
        init_sub();
        for (unsigned i = m_fmls.size(); i-- > m_qhead && !m_fmls.inconsistent();)
            process_fml(i);
        if (subst.empty())
            break;
    }
    
    m_rewriter.set_substitution(nullptr);        
    m_rewriter.reset();

    advance_qhead(m_fmls.size());
}

void propagate_values::collect_statistics(statistics& st) const {
    st.update("propagate-values-rewrites", m_stats.m_num_rewrites);        
}

void propagate_values::updt_params(params_ref const& p) {
    tactic_params tp(p);
    m_max_rounds = p.get_uint("max_rounds", tp.propagate_values_max_rounds());
    m_rewriter.updt_params(p);
}

void propagate_values::collect_param_descrs(param_descrs& r) {
    th_rewriter::get_param_descrs(r);
    r.insert("max_rounds", CPK_UINT, "(default: 4) maximum number of rounds.");
}
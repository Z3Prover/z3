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
#include "ast/simplifiers/propagate_values.h"

propagate_values::propagate_values(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
    dependent_expr_simplifier(m, fmls),
    m_rewriter(m),
    m_shared(m, true),
    m_subst(m, true, false) {
    m_rewriter.set_flat_and_or(false);
    updt_params(p);
}

void propagate_values::process_fml(unsigned i) {
    if (!m_subst.empty()) {
        auto [f, p, dep] = m_fmls[i]();
        expr_ref fml(m);
        proof_ref pr(m);
        m_rewriter(f, fml, pr);
        if (fml != f) {
            dep = m.mk_join(dep, m_rewriter.get_used_dependencies());
            m_fmls.update(i, dependent_expr(m, fml, mp(p, pr), dep));
            ++m_stats.m_num_rewrites;
        }
        m_rewriter.reset_used_dependencies();
    }
    add_sub(m_fmls[i]);
}

void propagate_values::add_sub(dependent_expr const& de) {
    expr* x, * y;
    auto const& [f, p, dep] = de();
    if (m.is_not(f, x) && m_shared.is_shared(x))
        m_subst.insert(x, m.mk_false(), dep);
    if (m_shared.is_shared(f))
        m_subst.insert(f, m.mk_true(), dep);
    if (m.is_eq(f, x, y)) {
        if (m.is_value(x) && m_shared.is_shared(y))
            m_subst.insert(y, x, dep);
        else if (m.is_value(y) && m_shared.is_shared(x))
            m_subst.insert(x, y, dep);
    }
};

void propagate_values::reduce() {
    m_shared.reset();
    m_subst.reset();

    auto add_shared = [&]() {
        shared_occs_mark visited;
        m_shared.reset();
        for (unsigned i = 0; i < qtail(); ++i)
            m_shared(m_fmls[i].fml(), visited);
    };   
   
    auto init_sub = [&]() {
        add_shared();
        m_subst.reset();
        m_rewriter.reset();
        m_rewriter.set_substitution(&m_subst);
        for (unsigned i = 0; i < qhead(); ++i)
            add_sub(m_fmls[i]);
    };
    
    unsigned rw = m_stats.m_num_rewrites + 1;
    for (unsigned r = 0; r < m_max_rounds && m.inc() && rw != m_stats.m_num_rewrites; ++r) {            
        rw = m_stats.m_num_rewrites;
        init_sub();
        for (unsigned i : indices())
            process_fml(i);
        init_sub();
        for (unsigned i = qtail(); i-- > qhead() && m.inc() && !m_fmls.inconsistent();)
            process_fml(i);
        if (m_subst.empty())
            break;
    }
    
    m_rewriter.set_substitution(nullptr);        
    m_rewriter.reset();
    m_subst.reset();
    m_shared.reset();
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
    r.insert("max_rounds", CPK_UINT, "maximum number of rounds.", "4");
}

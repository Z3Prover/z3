/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    user_propagator.cpp

Abstract:

    User theory propagator plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/


#include "ast/ast_pp.h"
#include "smt/user_propagator.h"
#include "smt/smt_context.h"

using namespace smt;

user_propagator::user_propagator(context& ctx):
    theory(ctx, ctx.get_manager().mk_family_id("user_propagator"))
{}

user_propagator::~user_propagator() {
    dealloc(m_api_context);
}

void user_propagator::force_push() {
    for (; m_num_scopes > 0; --m_num_scopes) {
        theory::push_scope_eh();
        m_push_eh(m_user_context);
        m_prop_lim.push_back(m_prop.size());
    }
}

unsigned user_propagator::add_expr(expr* e) {
    force_push();
    enode* n = ensure_enode(e);
    if (is_attached_to_var(n))
        return n->get_th_var(get_id());
    theory_var v = mk_var(n);
    ctx.attach_th_var(n, this, v);
    return v;
}

void user_propagator::propagate_cb(
    unsigned num_fixed, unsigned const* fixed_ids, 
    unsigned num_eqs, unsigned const* eq_lhs, unsigned const* eq_rhs, 
    expr* conseq) {
    m_prop.push_back(prop_info(num_fixed, fixed_ids, num_eqs, eq_lhs, eq_rhs, expr_ref(conseq, m)));
}

theory * user_propagator::mk_fresh(context * new_ctx) { 
    auto* th = alloc(user_propagator, *new_ctx); 
    void* ctx = m_fresh_eh(m_user_context, new_ctx->get_manager(), th->m_api_context);
    th->add(ctx, m_push_eh, m_pop_eh, m_fresh_eh);
    if ((bool)m_fixed_eh) th->register_fixed(m_fixed_eh);
    if ((bool)m_final_eh) th->register_final(m_final_eh);
    if ((bool)m_eq_eh) th->register_eq(m_eq_eh);
    if ((bool)m_diseq_eh) th->register_diseq(m_diseq_eh);
    return th;
}

final_check_status user_propagator::final_check_eh() {
    if (!(bool)m_final_eh)
        return FC_DONE;
    force_push();
    unsigned sz = m_prop.size();
    m_final_eh(m_user_context, this);
    propagate();
    bool done = (sz == m_prop.size()) && !ctx.inconsistent();
    return done ? FC_DONE : FC_CONTINUE;
}

void user_propagator::new_fixed_eh(theory_var v, expr* value, unsigned num_lits, literal const* jlits) {
    if (!m_fixed_eh)
        return;
    force_push();
    if (m_fixed.contains(v))
        return;
    m_fixed.insert(v);
    ctx.push_trail(insert_map<uint_set, unsigned>(m_fixed, v));
    m_id2justification.setx(v, literal_vector(num_lits, jlits), literal_vector());
    m_fixed_eh(m_user_context, this, v, value);
}

void user_propagator::push_scope_eh() {
    ++m_num_scopes;
}

void user_propagator::pop_scope_eh(unsigned num_scopes) {
    unsigned n = std::min(num_scopes, m_num_scopes);
    m_num_scopes -= n;
    num_scopes -= n;
    if (num_scopes == 0)
        return;
    m_pop_eh(m_user_context, num_scopes);
    theory::pop_scope_eh(num_scopes);
    unsigned old_sz = m_prop_lim.size() - num_scopes;
    m_prop.shrink(m_prop_lim[old_sz]);
    m_prop_lim.shrink(old_sz);
}

bool user_propagator::can_propagate() {
    return m_qhead < m_prop.size();
}

void user_propagator::propagate() {
    if (m_qhead == m_prop.size())
        return;
    force_push();
    unsigned qhead = m_qhead;
    justification* js;
    while (qhead < m_prop.size() && !ctx.inconsistent()) {
        auto const& prop = m_prop[qhead];
        m_lits.reset();   
        m_eqs.reset();
        for (unsigned id : prop.m_ids)
            m_lits.append(m_id2justification[id]);
        for (auto const& p : prop.m_eqs)
            m_eqs.push_back(enode_pair(get_enode(p.first), get_enode(p.second)));
        DEBUG_CODE(for (auto const& p : m_eqs) VERIFY(p.first->get_root() == p.second->get_root()););

        if (m.is_false(prop.m_conseq)) {
            js = ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(), m_lits.size(), m_lits.data(), m_eqs.size(), m_eqs.data(), 0, nullptr));
            ctx.set_conflict(js);
        }
        else {
            literal lit = mk_literal(prop.m_conseq);
            js = ctx.mk_justification(
                ext_theory_propagation_justification(
                    get_id(), ctx.get_region(), m_lits.size(), m_lits.data(), m_eqs.size(), m_eqs.data(), lit));
            ctx.assign(lit, js);
        }
        ++m_stats.m_num_propagations;
        ++qhead;
    }
    ctx.push_trail(value_trail<unsigned>(m_qhead));
    m_qhead = qhead;
}

void user_propagator::collect_statistics(::statistics & st) const {
    st.update("user-propagations", m_stats.m_num_propagations);
    st.update("user-watched",      get_num_vars());
}



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
    theory(ctx, ctx.get_manager().mk_family_id("user_propagator")),
    m_qhead(0),
    m_num_scopes(0)
{}

void user_propagator::force_push() {
    for (; m_num_scopes > 0; --m_num_scopes) {
        theory::push_scope_eh();
        m_push_eh(m_user_context);
        m_prop_lim.push_back(m_prop.size());
    }
}

// TODO: check type of 'e', either Bool or Bit-vector.
//

unsigned user_propagator::add_expr(expr* e) {
    force_push();
    enode* n = ensure_enode(e);
    if (is_attached_to_var(n))
        return n->get_th_var(get_id());
    theory_var v = mk_var(n);
    ctx.attach_th_var(n, this, v);
    return v;
}

void user_propagator::new_fixed_eh(theory_var v, expr* value, unsigned num_lits, literal const* jlits) {
    force_push();
    m_id2justification.setx(v, literal_vector(num_lits, jlits), literal_vector());
    m_fixed_eh(m_user_context, v, value);
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
    force_push();
    unsigned qhead = m_qhead;
    literal_vector lits;
    enode_pair_vector eqs;
    justification* js;
    while (qhead < m_prop.size() && !ctx.inconsistent()) {
        auto const& prop = m_prop[qhead];
        lits.reset();        
        for (unsigned id : prop.m_ids) 
            lits.append(m_id2justification[id]);
        if (m.is_false(prop.m_conseq)) {
            js = ctx.mk_justification(
                ext_theory_conflict_justification(
                    get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), 0, nullptr));
            ctx.set_conflict(js);
        }
        else {
            literal lit = mk_literal(prop.m_conseq);
            js = ctx.mk_justification(
                ext_theory_propagation_justification(
                    get_id(), ctx.get_region(), lits.size(), lits.c_ptr(), eqs.size(), eqs.c_ptr(), lit));
            ctx.assign(lit, js);
        }
        ++qhead;
    }
    ctx.push_trail(value_trail<context, unsigned>(m_qhead));
    m_qhead = qhead;
}



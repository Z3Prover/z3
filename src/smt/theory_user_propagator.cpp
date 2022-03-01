/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    theory_user_propagator.cpp

Abstract:

    User theory propagator plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/


#include "ast/ast_pp.h"
#include "smt/theory_user_propagator.h"
#include "smt/smt_context.h"

using namespace smt;

theory_user_propagator::theory_user_propagator(context& ctx):
    theory(ctx, ctx.get_manager().mk_family_id(user_propagator::plugin::name())),
    m_var2expr(ctx.get_manager())
{}

theory_user_propagator::~theory_user_propagator() {
    dealloc(m_api_context);
}

void theory_user_propagator::force_push() {
    for (; m_num_scopes > 0; --m_num_scopes) {
        theory::push_scope_eh();
        m_push_eh(m_user_context);
        m_prop_lim.push_back(m_prop.size());
    }
}

void theory_user_propagator::add_expr(expr* term) {
    force_push();
    expr_ref r(m);
    expr* e = term;
    ctx.get_rewriter()(e, r);
    if (r != e) {
        r = m.mk_fresh_const("aux-expr", e->get_sort());
        expr_ref eq(m.mk_eq(r, e), m);
        ctx.assert_expr(eq);
        ctx.internalize_assertions();
        e = r;
        ctx.mark_as_relevant(eq.get());
    }
    enode* n = ensure_enode(e);
    if (is_attached_to_var(n))
        return;


    theory_var v = mk_var(n);
    m_var2expr.reserve(v + 1);
    m_var2expr[v] = term;
    m_expr2var.setx(term->get_id(), v, null_theory_var);
    
    if (m.is_bool(e) && !ctx.b_internalized(e)) {
        bool_var bv = ctx.mk_bool_var(e);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
    }
    SASSERT(!m.is_bool(e) || ctx.b_internalized(e));

    ctx.attach_th_var(n, this, v);
    literal_vector explain;
    if (ctx.is_fixed(n, r, explain))
        m_prop.push_back(prop_info(explain, v, r));
    
}

void theory_user_propagator::propagate_cb(
    unsigned num_fixed, expr* const* fixed_ids, 
    unsigned num_eqs, expr* const* eq_lhs, expr* const* eq_rhs, 
    expr* conseq) {
    CTRACE("user_propagate", ctx.lit_internalized(conseq) && ctx.get_assignment(ctx.get_literal(conseq)) == l_true,
           ctx.display(tout << "redundant consequence: " << mk_pp(conseq, m) << "\n"));
    expr_ref _conseq(conseq, m);
    ctx.get_rewriter()(conseq, _conseq);
    if (ctx.lit_internalized(_conseq) && ctx.get_assignment(ctx.get_literal(_conseq)) == l_true) 
        return;
    m_prop.push_back(prop_info(num_fixed, fixed_ids, num_eqs, eq_lhs, eq_rhs, _conseq));    
}

void theory_user_propagator::register_cb(expr* e) {
    add_expr(e);
}

theory * theory_user_propagator::mk_fresh(context * new_ctx) {
    auto* th = alloc(theory_user_propagator, *new_ctx);
    void* ctx;
    try {
        ctx = m_fresh_eh(m_user_context, new_ctx->get_manager(), th->m_api_context);
    }
    catch (...) {
        throw default_exception("Exception thrown in \"fresh\"-callback");
    }
    th->add(ctx, m_push_eh, m_pop_eh, m_fresh_eh);
    if ((bool)m_fixed_eh) th->register_fixed(m_fixed_eh);
    if ((bool)m_final_eh) th->register_final(m_final_eh);
    if ((bool)m_eq_eh) th->register_eq(m_eq_eh);
    if ((bool)m_diseq_eh) th->register_diseq(m_diseq_eh);
    if ((bool)m_created_eh) th->register_created(m_created_eh);
    return th;
}

final_check_status theory_user_propagator::final_check_eh() {
    if (!(bool)m_final_eh)
        return FC_DONE;
    force_push();
    unsigned sz = m_prop.size();
    try {
        m_final_eh(m_user_context, this);
    }
    catch (...) {
      throw default_exception("Exception thrown in \"final\"-callback");
    }
    propagate();
    bool done = (sz == m_prop.size()) && !ctx.inconsistent();
    return done ? FC_DONE : FC_CONTINUE;
}

void theory_user_propagator::new_fixed_eh(theory_var v, expr* value, unsigned num_lits, literal const* jlits) {
    if (!m_fixed_eh)
        return;
    force_push();
    if (m_fixed.contains(v))
        return;
    m_fixed.insert(v);
    ctx.push_trail(insert_map<uint_set, unsigned>(m_fixed, v));
    m_id2justification.setx(v, literal_vector(num_lits, jlits), literal_vector());
    try {
         m_fixed_eh(m_user_context, this, var2expr(v), value);
     }
     catch (...) {
        throw default_exception("Exception thrown in \"fixed\"-callback");
     }
}

void theory_user_propagator::push_scope_eh() {
    ++m_num_scopes;
}

void theory_user_propagator::pop_scope_eh(unsigned num_scopes) {
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

bool theory_user_propagator::can_propagate() {
    return m_qhead < m_prop.size();
}

void theory_user_propagator::propagate_consequence(prop_info const& prop) {
    justification* js;
    m_lits.reset();   
    m_eqs.reset();
    for (expr* id : prop.m_ids)
        m_lits.append(m_id2justification[expr2var(id)]);
    for (auto const& p : prop.m_eqs)
        m_eqs.push_back(enode_pair(get_enode(expr2var(p.first)), get_enode(expr2var(p.second))));
    DEBUG_CODE(for (auto const& p : m_eqs) VERIFY(p.first->get_root() == p.second->get_root()););
    DEBUG_CODE(for (expr* e : prop.m_ids) VERIFY(m_fixed.contains(expr2var(e))););
    DEBUG_CODE(for (literal lit : m_lits) VERIFY(ctx.get_assignment(lit) == l_true););
    
    TRACE("user_propagate", tout << "propagating #" << prop.m_conseq->get_id() << ": " << prop.m_conseq << "\n");
    
    if (m.is_false(prop.m_conseq)) {
        js = ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx.get_region(), m_lits.size(), m_lits.data(), m_eqs.size(), m_eqs.data(), 0, nullptr));
        ctx.set_conflict(js);
    }
    else {
        for (auto& lit : m_lits)
            lit.neg();
        for (auto const& [a,b] : m_eqs)
            m_lits.push_back(~mk_eq(a->get_expr(), b->get_expr(), false));
        
        literal lit; 
        if (has_quantifiers(prop.m_conseq)) {
            expr_ref fn(m.mk_fresh_const("aux-literal", m.mk_bool_sort()), m);
            expr_ref eq(m.mk_eq(fn, prop.m_conseq), m);
            ctx.assert_expr(eq);
            ctx.internalize_assertions();
            lit = mk_literal(fn);
        }
        else 
            lit = mk_literal(prop.m_conseq);            
        ctx.mark_as_relevant(lit);
        m_lits.push_back(lit);
        ctx.mk_th_lemma(get_id(), m_lits);
        TRACE("user_propagate", ctx.display(tout););
    }
}

void theory_user_propagator::propagate_new_fixed(prop_info const& prop) {
    new_fixed_eh(prop.m_var, prop.m_conseq, prop.m_lits.size(), prop.m_lits.data());
}


void theory_user_propagator::propagate() {
    TRACE("user_propagate", tout << "propagating queue head: " << m_qhead << " prop queue: " << m_prop.size() << "\n");
    if (m_qhead == m_prop.size())
        return;
    force_push();
    unsigned qhead = m_qhead;
    while (qhead < m_prop.size() && !ctx.inconsistent()) {
        auto const& prop = m_prop[qhead];
        if (prop.m_var == null_theory_var)
            propagate_consequence(prop);
        else
            propagate_new_fixed(prop);
        ++m_stats.m_num_propagations;
        ++qhead;
    }
    ctx.push_trail(value_trail<unsigned>(m_qhead));
    m_qhead = qhead;
}


bool theory_user_propagator::internalize_atom(app* atom, bool gate_ctx) {
    return internalize_term(atom);
}

bool theory_user_propagator::internalize_term(app* term)  { 
    for (auto arg : *term)
        ensure_enode(arg);
    if (term->get_family_id() == get_id() && !ctx.e_internalized(term)) 
        ctx.mk_enode(term, true, false, true);
    
    add_expr(term);
    
    if (!m_created_eh)
        throw default_exception("You have to register a created event handler for new terms if you track them");

    try {
        m_created_eh(m_user_context, this, term);
    }
    catch (...) {
        throw default_exception("Exception thrown in \"created\"-callback");
    }

    return true;
}

void theory_user_propagator::collect_statistics(::statistics & st) const {
    st.update("user-propagations", m_stats.m_num_propagations);
    st.update("user-watched",      get_num_vars());
}



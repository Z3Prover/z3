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
#include "smt/theory_bv.h"
#include "smt/theory_user_propagator.h"
#include "smt/smt_context.h"

using namespace smt;

theory_user_propagator::theory_user_propagator(context& ctx):
    theory(ctx, ctx.get_manager().mk_family_id(user_propagator::plugin::name())),
    m_var2expr(ctx.get_manager()),
    m_push_popping(false),
    m_to_add(ctx.get_manager())
{}

theory_user_propagator::~theory_user_propagator() {
    dealloc(m_api_context);
}

void theory_user_propagator::force_push() {
    for (; m_num_scopes > 0; --m_num_scopes) {
        flet<bool> _pushing(m_push_popping, true);
        theory::push_scope_eh();
        m_prop_lim.push_back(m_prop.size());
        m_to_add_lim.push_back(m_to_add.size());
        m_push_eh(m_user_context, this);
    }
}

void theory_user_propagator::add_expr(expr* term, bool ensure_enode) {
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
    enode* n = ensure_enode ? this->ensure_enode(e) : ctx.get_enode(e);
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
    if (m_push_popping)
        m_to_add.push_back(e);
    else
        add_expr(e, true);
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
    if ((bool)m_decide_eh) th->register_decide(m_decide_eh);
    return th;
}

final_check_status theory_user_propagator::final_check_eh() {
    if (!(bool)m_final_eh)
        return FC_DONE;
    force_push();
    unsigned sz1 = m_prop.size();
    unsigned sz2 = m_expr2var.size();
    try {
        m_final_eh(m_user_context, this);
    }
    catch (...) {
      throw default_exception("Exception thrown in \"final\"-callback");
    }
    propagate();
    // check if it became inconsistent or something new was propagated/registered
    bool done = (sz1 == m_prop.size()) && (sz2 == m_expr2var.size()) && !ctx.inconsistent();
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

void theory_user_propagator::decide(bool_var& var, bool& is_pos) {

    const bool_var_data& d = ctx.get_bdata(var);
    
    if (!d.is_enode() && !d.is_theory_atom()) 
        return;
    
    enode* original_enode = nullptr; 
    unsigned original_bit = 0;
    bv_util bv(m);
    theory* th = nullptr;
    theory_var v = null_theory_var;
    
    // get the associated theory
    if (!d.is_enode()) {
        // it might be a value that does not have an enode
        th = ctx.get_theory(d.get_theory());
    }
    else {
        original_enode = ctx.bool_var2enode(var);
        v = original_enode->get_th_var(get_family_id());
        if (v == null_theory_var) {
            // it is not a registered boolean expression
            th = ctx.get_theory(d.get_theory());
        }
    }
    
    if (!th && v == null_theory_var)
        return;

    if (v == null_theory_var) {
        if (th->get_family_id() == bv.get_fid()) {
            // it is not a registered boolean value but it is a bitvector
            auto registered_bv = ((theory_bv*)th)->get_bv_with_theory(var, get_family_id());
            if (!registered_bv.first)
                // there is no registered bv associated with the bit
                return;
            original_enode = registered_bv.first;
            original_bit = registered_bv.second;
            v = original_enode->get_th_var(get_family_id());
        }
        else
            return;
    }

    // call the registered callback
    unsigned new_bit = original_bit;
    lbool phase = is_pos ? l_true : l_false;
    
    expr* e = var2expr(v);
    m_decide_eh(m_user_context, this, &e, &new_bit, &phase);
    enode* new_enode = ctx.get_enode(e);

    // check if the callback changed something
    if (original_enode == new_enode && (new_enode->is_bool() || original_bit == new_bit)) {
        if (phase != l_undef)
            // it only affected the truth value
            is_pos = phase == l_true;
        return;
    }

    if (new_enode->is_bool()) {
        // expression was set to a boolean
        bool_var new_var = ctx.enode2bool_var(new_enode);
        if (ctx.get_assignment(new_var) == l_undef) {
            var = new_var;
        }
    }
    else {
        // expression was set to a bit-vector
        auto th_bv = (theory_bv*)ctx.get_theory(bv.get_fid());
        bool_var new_var = th_bv->get_first_unassigned(new_bit, new_enode);

        if (new_var != null_bool_var) {
            var = new_var;
        }
    }

    // in case the callback did not decide on a truth value -> let Z3 decide
    is_pos = ctx.guess(var, phase);
}

void theory_user_propagator::push_scope_eh() {    
    ++m_num_scopes;
}

void theory_user_propagator::pop_scope_eh(unsigned num_scopes) {
    flet<bool> _popping(m_push_popping, true);
    unsigned n = std::min(num_scopes, m_num_scopes);
    m_num_scopes -= n;
    num_scopes -= n;
    if (num_scopes == 0)
        return;
    theory::pop_scope_eh(num_scopes);
    unsigned old_sz = m_prop_lim.size() - num_scopes;
    m_prop.shrink(m_prop_lim[old_sz]);
    m_prop_lim.shrink(old_sz);
    old_sz = m_to_add_lim.size() - num_scopes;
    m_to_add.shrink(m_to_add_lim[old_sz]);
    m_to_add_lim.shrink(old_sz);
    m_pop_eh(m_user_context, this, num_scopes);
}

bool theory_user_propagator::can_propagate() {
    return m_qhead < m_prop.size() || m_to_add_qhead < m_to_add.size();
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
    if (m_qhead == m_prop.size() && m_to_add_qhead == m_to_add.size())
        return;
    force_push();
    
    unsigned qhead = m_to_add_qhead;
    if (qhead < m_to_add.size()) {
        for (; qhead < m_to_add.size(); ++qhead)
            add_expr(m_to_add.get(qhead), true);
        ctx.push_trail(value_trail<unsigned>(m_to_add_qhead));
        m_to_add_qhead = qhead;
    }

    qhead = m_qhead;
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
    
    add_expr(term, false);
    
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



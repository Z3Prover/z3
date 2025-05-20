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
#include "ast/ast_ll_pp.h"

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
    TRACE("user_propagate", tout << "add " << mk_bounded_pp(e, m) << "\n");
    if (!is_ground(r)) {
        if (m_add_expr_fresh.contains(term))
            return;
        m_add_expr_fresh.insert(term);
        ctx.push_trail(insert_obj_trail(m_add_expr_fresh, term));
        r = m.mk_fresh_const("aux-expr", e->get_sort());
        expr_ref eq(m.mk_eq(r, e), m);
        ctx.assert_expr(eq);
        ctx.internalize_assertions();
        ctx.mark_as_relevant(eq.get());
    }
    e = r;
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

bool theory_user_propagator::propagate_cb(
    unsigned num_fixed, expr* const* fixed_ids, 
    unsigned num_eqs, expr* const* eq_lhs, expr* const* eq_rhs, 
    expr* conseq) {
    CTRACE("user_propagate", ctx.lit_internalized(conseq) && ctx.get_assignment(ctx.get_literal(conseq)) == l_true,
           ctx.display(tout << "redundant consequence: " << mk_pp(conseq, m) << "\n"));

    expr_ref _conseq(conseq, m);
    ctx.get_rewriter()(conseq, _conseq);
    if (!ctx.get_manager().is_true(_conseq) && !ctx.get_manager().is_false(_conseq))
        ctx.mark_as_relevant((expr*)_conseq);

    if (ctx.lit_internalized(_conseq) && ctx.get_assignment(ctx.get_literal(_conseq)) == l_true)
        return false;
    m_prop.push_back(prop_info(num_fixed, fixed_ids, num_eqs, eq_lhs, eq_rhs, _conseq));
    return true;
}

void theory_user_propagator::register_cb(expr* e) {
    if (m_push_popping)
        m_to_add.push_back(e);
    else
        add_expr(e, true);
}

bool theory_user_propagator::next_split_cb(expr* e, unsigned idx, lbool phase) {
    if (e == nullptr) { // clear
        m_next_split_var = nullptr;
        return true;
    }
    if (!ctx.e_internalized(e)) {
        // We may not eagerly internalize it (might crash when done in pop) => delay
        m_next_split_var = e;
        return true;
    }
    bool_var b = enode_to_bool(ctx.get_enode(e), idx);
    if (b == null_bool_var || ctx.get_assignment(b) != l_undef)
        return false;
    m_next_split_var = e;
    m_next_split_idx = idx;
    m_next_split_phase = phase;
    return true;
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
    unsigned sz2 = get_num_vars();
    try {
        m_final_eh(m_user_context, this);
    }
    catch (...) {
        throw default_exception("Exception thrown in \"final\"-callback");
    }
    CTRACE("user_propagate", can_propagate(), tout << "can propagate\n");
    propagate();
    CTRACE("user_propagate", ctx.inconsistent(), tout << "inconsistent\n");
    // check if it became inconsistent or something new was propagated/registered
    bool done = (sz1 == m_prop.size()) && (sz2 == get_num_vars()) && !ctx.inconsistent();
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

bool_var theory_user_propagator::enode_to_bool(enode* n, unsigned idx) {
    if (n->is_bool()) {
        // expression is a boolean
        return ctx.enode2bool_var(n);
    }
    // expression is a bit-vector
    bv_util bv(m);
    auto th_bv = (theory_bv*)ctx.get_theory(bv.get_fid());
    return th_bv->get_bit(idx, n);
}

void theory_user_propagator::decide(bool_var& var, bool& is_pos) {
    if (!m_decide_eh)
        return;

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

    if (v == null_theory_var && !th)
        return;

    if (v == null_theory_var && th->get_family_id() != bv.get_fid())
        return;

    if (v == null_theory_var) {
        // it is not a registered boolean value but it is a bitvector
        auto registered_bv = ((theory_bv*) th)->get_bv_with_theory(var, get_family_id());
        if (!registered_bv.first)
            // there is no registered bv associated with the bit
            return;
        original_enode = registered_bv.first;
        original_bit = registered_bv.second;
        v = original_enode->get_th_var(get_family_id());
    }

    // call the registered callback
    unsigned new_bit = original_bit;

    force_push();
    expr *e = var2expr(v);
    m_decide_eh(m_user_context, this, e, new_bit, is_pos);

    bool_var new_var;
    if (!get_case_split(new_var, is_pos) || new_var == var)
        // The user did not interfere
        return;
    var = new_var;

    // check if the new variable is unassigned
    if (ctx.get_assignment(var) != l_undef)
        throw default_exception("expression in \"decide\" is already assigned");
}

bool theory_user_propagator::get_case_split(bool_var& var, bool& is_pos) {
    if (m_next_split_var == nullptr)
        return false;
    ensure_enode(m_next_split_var);
    bool_var b = enode_to_bool(ctx.get_enode(m_next_split_var), m_next_split_idx);
    if (b == null_bool_var || ctx.get_assignment(b) != l_undef)
        return false;
    var = b;
    is_pos = ctx.guess(var, m_next_split_phase);
    m_next_split_var = nullptr;
    m_next_split_idx = 0;
    m_next_split_phase = l_undef;
    return true;
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
    return m_qhead < m_prop.size() || m_to_add_qhead < m_to_add.size() || m_replay_qhead < m_clauses_to_replay.size();
}

void theory_user_propagator::propagate_consequence(prop_info const& prop) {
    justification* js;
    m_lits.reset();
    m_eqs.reset();
    for (expr* id: prop.m_ids)
        m_lits.append(m_id2justification[expr2var(id)]);
    for (auto const& [a, b]: prop.m_eqs)
        if (a != b)
            m_eqs.push_back(enode_pair(get_enode(expr2var(a)), get_enode(expr2var(b))));
    DEBUG_CODE(for (auto const& [a, b] : m_eqs) VERIFY(a->get_root() == b->get_root()););
    DEBUG_CODE(for (expr* e : prop.m_ids) VERIFY(m_fixed.contains(expr2var(e))););
    DEBUG_CODE(for (literal lit : m_lits) VERIFY(ctx.get_assignment(lit) == l_true););
    
    TRACE("user_propagate", tout << "propagating #" << prop.m_conseq->get_id() << ": " << prop.m_conseq << "\n";
          for (auto const& [a,b] : m_eqs) tout << enode_pp(a, ctx) << " == " << enode_pp(b, ctx) << "\n";
          for (expr* e : prop.m_ids) tout << mk_pp(e, m) << "\n";
          for (literal lit : m_lits) tout << lit << "\n");
    
    if (m.is_false(prop.m_conseq)) {
        js = ctx.mk_justification(
            ext_theory_conflict_justification(
                get_id(), ctx, m_lits.size(), m_lits.data(), m_eqs.size(), m_eqs.data(), 0, nullptr));
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

        if (ctx.get_fparams().m_up_persist_clauses) {
            expr_ref_vector clause(m);
            for (auto l : m_lits)
                clause.push_back(ctx.literal2expr(l));
            m_clauses_to_replay.push_back(clause);
            if (m_replay_qhead + 1 < m_clauses_to_replay.size())
                std::swap(m_clauses_to_replay[m_replay_qhead], m_clauses_to_replay[m_clauses_to_replay.size()-1]);
            ctx.push_trail(value_trail<unsigned>(m_replay_qhead));
            ++m_replay_qhead;
            ctx.mk_th_axiom(get_id(), m_lits);
        }
        else
            ctx.mk_th_lemma(get_id(), m_lits);
    }
    TRACE("user_propagate", ctx.display(tout););
    
}

void theory_user_propagator::propagate_new_fixed(prop_info const& prop) {
    new_fixed_eh(prop.m_var, prop.m_conseq, prop.m_lits.size(), prop.m_lits.data());
}


void theory_user_propagator::propagate() {
    if (m_qhead == m_prop.size() && m_to_add_qhead == m_to_add.size() && m_replay_qhead == m_clauses_to_replay.size())
        return;
    TRACE("user_propagate", tout << "propagating queue head: " << m_qhead << " prop queue: " << m_prop.size() << "\n");
    force_push();

    unsigned qhead = m_replay_qhead;
    if (qhead < m_clauses_to_replay.size()) {        
        for (; qhead < m_clauses_to_replay.size() && !ctx.inconsistent(); ++qhead)
            replay_clause(m_clauses_to_replay.get(qhead));
        ctx.push_trail(value_trail<unsigned>(m_replay_qhead));
        m_replay_qhead = qhead;
    }

    qhead = m_to_add_qhead;
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


void theory_user_propagator::replay_clause(expr_ref_vector const& clause) {
    m_lits.reset();
    for (expr* e : clause)
        m_lits.push_back(mk_literal(e));
    ctx.mk_th_axiom(get_id(), m_lits);
}

bool theory_user_propagator::internalize_atom(app* atom, bool gate_ctx) {
    return internalize_term(atom);
}

bool theory_user_propagator::internalize_term(app* term) {
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

void theory_user_propagator::collect_statistics(::statistics& st) const {
    st.update("user-propagations", m_stats.m_num_propagations);
    st.update("user-watched", get_num_vars());
}



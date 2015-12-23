/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    elim_bounds.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-28.

Revision History:

--*/
#include"elim_bounds.h"
#include"used_vars.h"
#include"obj_hashtable.h"
#include"var_subst.h"
#include"ast_pp.h"

elim_bounds::elim_bounds(ast_manager & m):
    m_manager(m),
    m_util(m) {
}

/**
   \brief Find bounds of the form

   (<= x k)
   (<= (+ x (* -1 y)) k)
   (<= (+ x (* -1 t)) k)  
   (<= (+ t (* -1 x)) k)

   x and y are a bound variables, t is a ground term and k is a numeral

   It also detects >=, and the atom can be negated.
*/
bool elim_bounds::is_bound(expr * n, var * & lower, var * & upper) {
    upper    = 0;
    lower    = 0;
    bool neg = false;
    if (m_manager.is_not(n)) {
        n   = to_app(n)->get_arg(0);
        neg = true;
    }

    bool le  = false;
    if (m_util.is_le(n)) {
        SASSERT(m_util.is_numeral(to_app(n)->get_arg(1)));
        n  = to_app(n)->get_arg(0);
        le = true;
    }
    else if (m_util.is_ge(n)) {
        SASSERT(m_util.is_numeral(to_app(n)->get_arg(1)));
        n  = to_app(n)->get_arg(0);
        le = false;
    }
    else {
        return false;
    }

    if (neg)
        le = !le;
    
    if (is_var(n)) {
        upper = to_var(n);
    }
    else if (m_util.is_add(n) && to_app(n)->get_num_args() == 2) {
        expr * arg1 = to_app(n)->get_arg(0);
        expr * arg2 = to_app(n)->get_arg(1);
        if (is_var(arg1)) 
            upper   = to_var(arg1);
        else if (!is_ground(arg1))
            return false;
        rational k;
        bool is_int;
        if (m_util.is_mul(arg2) && m_util.is_numeral(to_app(arg2)->get_arg(0), k, is_int) && k.is_minus_one()) {
            arg2    = to_app(arg2)->get_arg(1);
            if (is_var(arg2))
                lower = to_var(arg2);
            else if (!is_ground(arg2))
                return false; // not supported
        }
        else {
            return false; // not supported
        }
    }
    else {
        return false;
    }

    if (!le)
        std::swap(upper, lower);
    
    return true;
}

bool elim_bounds::is_bound(expr * n) {
    var * lower, * upper;
    return is_bound(n, lower, upper);
}

void elim_bounds::operator()(quantifier * q, expr_ref & r) {
    if (!q->is_forall()) {
        r = q;
        return;
    }
    expr * n = q->get_expr();
    unsigned num_vars = q->get_num_decls();
    ptr_buffer<expr> atoms;
    if (m_manager.is_or(n))
        atoms.append(to_app(n)->get_num_args(), to_app(n)->get_args());
    else
        atoms.push_back(n);
    used_vars          m_used_vars;
    // collect non-candidates
    unsigned sz = atoms.size();
    for (unsigned i = 0; i < sz; i++) {
        expr * a = atoms[i];
        if (!is_bound(a))
            m_used_vars.process(a);
    }
    if (m_used_vars.uses_all_vars(q->get_num_decls())) {
        r = q;
        return;
    }
    // collect candidates
    obj_hashtable<var> m_lowers;
    obj_hashtable<var> m_uppers;
    obj_hashtable<var> m_candidate_set;
    ptr_buffer<var>    m_candidates;
#define ADD_CANDIDATE(V) if (!m_lowers.contains(V) && !m_uppers.contains(V)) { m_candidate_set.insert(V); m_candidates.push_back(V); }
    for (unsigned i = 0; i < sz; i++) {
        expr * a    = atoms[i];
        var * lower = 0;
        var * upper = 0;
        if (is_bound(a, lower, upper)) {
            if (lower != 0 && !m_used_vars.contains(lower->get_idx()) && lower->get_idx() < num_vars) {
                ADD_CANDIDATE(lower);
                m_lowers.insert(lower);
            }
            if (upper != 0 && !m_used_vars.contains(upper->get_idx()) && upper->get_idx() < num_vars) {
                ADD_CANDIDATE(upper);
                m_uppers.insert(upper);
            }
        }
    }
    TRACE("elim_bounds", tout << "candidates:\n"; for (unsigned i = 0; i < m_candidates.size(); i++) tout << mk_pp(m_candidates[i], m_manager) << "\n";);
    // remove candidates that have lower and upper bounds
    for (unsigned i = 0; i < m_candidates.size(); i++) {
        var * v = m_candidates[i];
        if (m_lowers.contains(v) && m_uppers.contains(v))
            m_candidate_set.erase(v);
    }
    TRACE("elim_bounds", tout << "candidates after filter:\n"; for (unsigned i = 0; i < m_candidates.size(); i++) tout << mk_pp(m_candidates[i], m_manager) << "\n";);
    if (m_candidate_set.empty()) {
        r = q;
        return;
    }
    // remove bounds that contain variables in m_candidate_set
    unsigned j = 0;
    for (unsigned i = 0; i < sz; i++) {
        expr * a    = atoms[i];
        var * lower = 0;
        var * upper = 0;
        if (is_bound(a, lower, upper) && ((lower != 0 && m_candidate_set.contains(lower)) || (upper != 0 && m_candidate_set.contains(upper))))
            continue;
        atoms[j] = a;
        j++;
    }
    atoms.resize(j);
    expr * new_body = 0;
    switch (atoms.size()) {
    case 0:
        r = m_manager.mk_false();
        TRACE("elim_bounds", tout << mk_pp(q, m_manager) << "\n" << mk_pp(r, m_manager) << "\n";);
        return;
    case 1:
        new_body = atoms[0];
        break;
    default:
        new_body = m_manager.mk_or(atoms.size(), atoms.c_ptr());
        break;
    }
    quantifier_ref new_q(m_manager);
    new_q = m_manager.update_quantifier(q, new_body);
    elim_unused_vars(m_manager, new_q, r);
    TRACE("elim_bounds", tout << mk_pp(q, m_manager) << "\n" << mk_pp(r, m_manager) << "\n";);
}

bool elim_bounds_star::visit_quantifier(quantifier * q) {
    if (!q->is_forall() || q->get_num_patterns() != 0)
        return true;
    bool visited         = true;
    visit(q->get_expr(), visited);
    return visited;
}
 
void elim_bounds_star::reduce1_quantifier(quantifier * q) {
    if (!q->is_forall() || q->get_num_patterns() != 0) {
        cache_result(q, q, 0); 
        return;
    }
    quantifier_ref new_q(m);
    expr * new_body = 0;
    proof * new_pr;
    get_cached(q->get_expr(), new_body, new_pr);
    new_q = m.update_quantifier(q, new_body);
    expr_ref r(m);
    m_elim(new_q, r);
    if (q == r.get()) {
        cache_result(q, q, 0);
        return;
    }
    proof_ref pr(m);
    if (m.fine_grain_proofs())
        pr = m.mk_rewrite(q, r); // TODO: improve justification
    cache_result(q, r, pr);
}


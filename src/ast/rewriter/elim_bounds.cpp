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

#ifndef ELIM_BOUNDS_H_
#define ELIM_BOUNDS_H_

#include "ast/used_vars.h"
#include "util/obj_hashtable.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/elim_bounds.h"
#include "ast/ast_pp.h"

elim_bounds_cfg::elim_bounds_cfg(ast_manager & m):
    m(m),
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
bool elim_bounds_cfg::is_bound(expr * n, var * & lower, var * & upper) {
    upper    = nullptr;
    lower    = nullptr;
    bool neg = false;
    if (m.is_not(n)) {
        n   = to_app(n)->get_arg(0);
        neg = true;
    }

    expr* l = nullptr, *r = nullptr;
    bool le  = false;
    if (m_util.is_le(n, l, r) && m_util.is_numeral(r)) {
        n  = l;
        le = true;
    }
    else if (m_util.is_ge(n, l, r) && m_util.is_numeral(r)) {
        n  = l;
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
    else if (m_util.is_add(n, l, r)) {
        expr * arg1 = l;
        expr * arg2 = r;
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

bool elim_bounds_cfg::is_bound(expr * n) {
    var * lower, * upper;
    return is_bound(n, lower, upper);
}


bool elim_bounds_cfg::reduce_quantifier(quantifier * q, 
                                     expr * n, 
                                     expr * const * new_patterns, 
                                     expr * const * new_no_patterns,
                                     expr_ref & result,
                                     proof_ref & result_pr) {
    if (!q->is_forall()) {
        return false;
    }
    unsigned num_vars = q->get_num_decls();
    ptr_buffer<expr> atoms;
    if (m.is_or(n))
        atoms.append(to_app(n)->get_num_args(), to_app(n)->get_args());
    else
        atoms.push_back(n);
    used_vars          used_vars;
    // collect non-candidates
    for (expr * a : atoms) {
        if (!is_bound(a))
            used_vars.process(a);
    }
    if (used_vars.uses_all_vars(q->get_num_decls())) {
        return false;
    }
    // collect candidates
    obj_hashtable<var> lowers;
    obj_hashtable<var> uppers;
    obj_hashtable<var> candidate_set;
    ptr_buffer<var>    candidates;
#define ADD_CANDIDATE(V) if (!lowers.contains(V) && !uppers.contains(V)) { candidate_set.insert(V); candidates.push_back(V); }
    for (expr * a : atoms) {
        var * lower = nullptr;
        var * upper = nullptr;
        if (is_bound(a, lower, upper)) {
            if (lower != nullptr && !used_vars.contains(lower->get_idx()) && lower->get_idx() < num_vars) {
                ADD_CANDIDATE(lower);
                lowers.insert(lower);
            }
            if (upper != nullptr && !used_vars.contains(upper->get_idx()) && upper->get_idx() < num_vars) {
                ADD_CANDIDATE(upper);
                uppers.insert(upper);
            }
        }
    }
    TRACE("elim_bounds", tout << "candidates:\n"; for (unsigned i = 0; i < candidates.size(); i++) tout << mk_pp(candidates[i], m) << "\n";);
    // remove candidates that have lower and upper bounds

    for (var * v : candidates) {
        if (lowers.contains(v) && uppers.contains(v))
            candidate_set.erase(v);
    }
    TRACE("elim_bounds", tout << "candidates after filter:\n"; for (unsigned i = 0; i < candidates.size(); i++) tout << mk_pp(candidates[i], m) << "\n";);
    if (candidate_set.empty()) {
        return false;
    }
    // remove bounds that contain variables in candidate_set
    unsigned j = 0;
    for (unsigned i = 0; i < atoms.size(); ++i) {
        expr * a = atoms[i];
        var * lower = nullptr;
        var * upper = nullptr;
        if (is_bound(a, lower, upper) && ((lower != nullptr && candidate_set.contains(lower)) || (upper != nullptr && candidate_set.contains(upper))))
            continue;
        atoms[j] = a;
        j++;
    }
    if (j == atoms.size()) {
        return false;
    }
    atoms.resize(j);
    expr * new_body = nullptr;
    switch (atoms.size()) {
    case 0:
        result = m.mk_false();
        result_pr = m.mk_rewrite(q, result);
        TRACE("elim_bounds", tout << mk_pp(q, m) << "\n" << result << "\n";);
        return true;
    case 1:
        new_body = atoms[0];
        break;
    default:
        new_body = m.mk_or(atoms.size(), atoms.c_ptr());
        break;
    }
    quantifier_ref new_q(m);
    new_q = m.update_quantifier(q, new_body);
    elim_unused_vars(m, new_q, params_ref(), result);
    result_pr = m.mk_rewrite(q, result);
    TRACE("elim_bounds", tout << mk_pp(q, m) << "\n" << result << "\n";);
    return true;
}

#endif /* ELIM_BOUNDS_H_ */

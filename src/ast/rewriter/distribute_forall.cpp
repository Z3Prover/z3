/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    distribute_forall.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-04-02.

Revision History:

    Christoph Wintersteiger 2010-04-06: Added implementation.

--*/
#include "ast/rewriter/var_subst.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/rewriter/distribute_forall.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/has_free_vars.h"
#include "ast/used_vars.h"

distribute_forall::distribute_forall(ast_manager & m) :
    m_manager(m),
    m_autil(m),
    m_cache(m) {
}

// The or-argument is a negated conjunct. Accept (not (= s t)) where s or t is a
// select over a ground array, i.e. the bound variables only occur as indices
// (or on the other side of the equation) and the quantifier does not range
// over arrays.
bool distribute_forall::is_array_select_eq(expr * arg) const {
    expr * e = nullptr, * lhs = nullptr, * rhs = nullptr;
    if (!m_manager.is_not(arg, e) || !m_manager.is_eq(e, lhs, rhs))
        return false;
    bool is_sel = false;
    for (expr * side : { lhs, rhs }) {
        if (!m_autil.is_select(side))
            continue;
        if (has_free_vars(to_app(side)->get_arg(0)))
            return false;
        is_sel = true;
    }
    return is_sel;
}

// True if some bound variable of the quantifier does not occur in the conjunct,
// so the quantifier obtained for it binds fewer variables (elim_unused_vars).
bool distribute_forall::omits_bound_var(expr * arg, unsigned num_decls) const {
    used_vars uv;
    uv(arg);
    for (unsigned i = 0; i < num_decls; ++i)
        if (!uv.contains(i))
            return true;
    return false;
}

// True if the conjunct applies an uninterpreted function (including Skolem
// functions introduced for nested existentials) to a term with bound variables.
// Splitting such conjunctions separates the occurrences that E-matching and
// nested quantifier reasoning rely on, so restricted mode keeps them together.
bool distribute_forall::has_uninterp_over_bound_vars(expr * arg) const {
    ptr_vector<expr> todo;
    ast_mark visited;
    todo.push_back(arg);
    while (!todo.empty()) {
        expr * e = todo.back();
        todo.pop_back();
        if (visited.is_marked(e) || is_ground(e))
            continue;
        visited.mark(e, true);
        if (is_quantifier(e)) {
            todo.push_back(to_quantifier(e)->get_expr());
            continue;
        }
        if (!is_app(e))
            continue;
        app * a = to_app(e);
        if (a->get_num_args() > 0 && a->get_family_id() == null_family_id)
            return true;
        for (expr * child : *a)
            todo.push_back(child);
    }
    return false;
}

bool distribute_forall::should_distribute(quantifier * q, app * or_e) const {
    if (!m_restricted)
        return true;
    bool all_array_eqs = true, some_omit = false, has_uf = false;
    for (expr * arg : *or_e) {
        if (all_array_eqs && !is_array_select_eq(arg))
            all_array_eqs = false;
        if (!some_omit && omits_bound_var(arg, q->get_num_decls()))
            some_omit = true;
        if (!has_uf && has_uninterp_over_bound_vars(arg))
            has_uf = true;
    }
    // Either pointwise equalities over ground arrays, or a split that yields a
    // quantifier over fewer variables without tearing apart uninterpreted
    // function applications over the bound variables.
    return all_array_eqs || (some_omit && !has_uf);
}

void distribute_forall::visit(expr * n, bool & visited) {
    if (!is_cached(n)) {
        m_todo.push_back(n);
        visited = false;
    }
}

bool distribute_forall::visit_children(expr * n) {
    bool visited = true;
    unsigned j;
    switch(n->get_kind()) {
    case AST_VAR:
        break;
    case AST_APP:
        j = to_app(n)->get_num_args();
        while (j > 0) {
            --j;
            visit(to_app(n)->get_arg(j), visited);
        }
        break;
    case AST_QUANTIFIER:
        visit(to_quantifier(n)->get_expr(), visited);
        break;
    default:
        UNREACHABLE();
    }
    return visited;
}

void distribute_forall::reduce1(expr * n) {
    switch (n->get_kind()) {
    case AST_VAR:
        cache_result(n, n);
        break;
    case AST_APP:
        reduce1_app(to_app(n));
        break;
    case AST_QUANTIFIER:
        reduce1_quantifier(to_quantifier(n));
        break;
    default: UNREACHABLE();
    }
}

void distribute_forall::reduce1_app(app * a) {
    SASSERT(a);
    unsigned num_args = a->get_num_args();
    unsigned j        = num_args;
    bool reduced      = false;
    m_new_args.reserve(num_args);
    app * na = a;

    while(j > 0) {
        --j;
        SASSERT(is_cached(a->get_arg(j)));
        expr * c = get_cached(a->get_arg(j));
        SASSERT(c!=0);
        if (c != a->get_arg(j))
            reduced = true;
        m_new_args[j] = c;
    }

    if (reduced) {
        na = m_manager.mk_app(a->get_decl(), num_args, m_new_args.data());
    }

    cache_result(a, na);
}

void distribute_forall::reduce1_quantifier(quantifier * q) {
    // This transformation is applied after skolemization/quantifier elimination. So, all quantifiers are universal.
    SASSERT(q->get_kind() == forall_k);

    // This transformation is applied after basic pre-processing steps.
    // So, we can assume that
    //    1) All (and f1 ... fn) are already encoded as (not (or (not f1 ... fn)))
    //    2) All or-formulas are flat (or f1 (or f2 f3)) is encoded as (or f1 f2 f3)

    expr * e = get_cached(q->get_expr());
    // A trigger for the original body need not be valid for each conjunct.
    if (m_manager.is_not(e) && m_manager.is_or(to_app(e)->get_arg(0)) &&
        !q->get_num_patterns() && !q->get_num_no_patterns() &&
        should_distribute(q, to_app(to_app(e)->get_arg(0)))) {
        bool_rewriter br(m_manager);

        // found target for simplification
        // (forall X (not (or F1 ... Fn)))
        // -->
        // (and (forall X (not F1))
        //      ...
        //      (forall X (not Fn)))
        app * or_e        = to_app(to_app(e)->get_arg(0));
        unsigned num_args = or_e->get_num_args();
        expr_ref_buffer new_args(m_manager);
        for (unsigned i = 0; i < num_args; ++i) {
            expr * arg = or_e->get_arg(i);
            expr_ref not_arg(m_manager);
            br.mk_not(arg, not_arg);
            quantifier_ref tmp_q(m_manager);
            tmp_q = m_manager.update_quantifier(q, not_arg);
            new_args.push_back(elim_unused_vars(m_manager, tmp_q, params_ref()));
        }
        expr_ref result(m_manager);
        // m_bsimp.mk_and actually constructs a (not (or ...)) formula,
        // it will also apply basic simplifications.
        br.mk_and(new_args.size(), new_args.data(), result);
        cache_result(q, result);
    }
    else {
        cache_result(q, m_manager.update_quantifier(q, e));
    }
}

void distribute_forall::operator()(expr * f, expr_ref & result) {
    m_todo.reset();
    flush_cache();

    m_todo.push_back(f);

    while (!m_todo.empty()) {
        expr * e = m_todo.back();
        if (visit_children(e)) {
            m_todo.pop_back();
            reduce1(e);
        }
    }

    result = get_cached(f);
    SASSERT(result!=0);
    TRACE(distribute_forall, tout << mk_ll_pp(f, m_manager) << "======>\n"
          << mk_ll_pp(result, m_manager););
}

expr * distribute_forall::get_cached(expr * n) const {
    return const_cast<distribute_forall*>(this)->m_cache.find(n);
}

void distribute_forall::cache_result(expr * n, expr * r) {
    SASSERT(r != 0);
    m_cache.insert(n, r);
}

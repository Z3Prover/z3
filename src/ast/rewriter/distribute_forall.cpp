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

distribute_forall::distribute_forall(ast_manager & m) :
    m_manager(m),
    m_cache(m) {
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
        na = m_manager.mk_app(a->get_decl(), num_args, m_new_args.c_ptr());
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
    if (m_manager.is_not(e) && m_manager.is_or(to_app(e)->get_arg(0))) {
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
        for (unsigned i = 0; i < num_args; i++) {
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
        br.mk_and(new_args.size(), new_args.c_ptr(), result);
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
    TRACE("distribute_forall", tout << mk_ll_pp(f, m_manager) << "======>\n"
          << mk_ll_pp(result, m_manager););
}

expr * distribute_forall::get_cached(expr * n) const {
    return const_cast<distribute_forall*>(this)->m_cache.find(n);
}

void distribute_forall::cache_result(expr * n, expr * r) {
    SASSERT(r != 0);
    m_cache.insert(n, r);
}

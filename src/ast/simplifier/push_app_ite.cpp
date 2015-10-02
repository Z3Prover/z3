/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    push_app_ite.cpp

Abstract:

    TODO: Write a better ite lifter


Author:

    Leonardo de Moura (leonardo) 2008-05-14.

Revision History:

--*/
#include"push_app_ite.h"
#include"ast_pp.h"

push_app_ite::push_app_ite(simplifier & s, bool conservative):
    simplifier(s.get_manager()),
    m_conservative(conservative) {

    borrow_plugins(s);
}

push_app_ite::~push_app_ite() {
    // the plugins were borrowed. So, release ownership.
    m_plugins.release();
}

int push_app_ite::has_ite_arg(unsigned num_args, expr * const * args) {
    for (unsigned i = 0; i < num_args; i++)
        if (m.is_ite(args[i]))
            return i;
    return -1;
}

void push_app_ite::apply(func_decl * decl, unsigned num_args, expr * const * args, expr_ref & r) {
    TRACE("push_app_ite", tout << "pushing app...\n";);
    int ite_arg_idx = has_ite_arg(num_args, args);
    if (ite_arg_idx < 0) {
        mk_app(decl, num_args, args, r);
        return;
    }
    app * ite               = to_app(args[ite_arg_idx]);
    expr * c                = ite->get_arg(0);
    expr * t                = ite->get_arg(1);
    expr * e                = ite->get_arg(2);
    expr ** args_prime      = const_cast<expr**>(args);
    expr * old              = args_prime[ite_arg_idx];
    args_prime[ite_arg_idx] = t;
    expr_ref t_new(m);
    apply(decl, num_args, args_prime, t_new);
    args_prime[ite_arg_idx] = e;
    expr_ref e_new(m);
    apply(decl, num_args, args_prime, e_new);
    args_prime[ite_arg_idx] = old;
    expr * new_args[3] = { c, t_new, e_new };
    mk_app(ite->get_decl(), 3, new_args, r);
}

/**
   \brief Default (conservative) implementation. Return true if there one and only one ite-term argument.
*/
bool push_app_ite::is_target(func_decl * decl, unsigned num_args, expr * const * args) {
    if (m.is_ite(decl))
        return false;
    bool found_ite = false;
    for (unsigned i = 0; i < num_args; i++) {
        if (m.is_ite(args[i]) && !m.is_bool(args[i])) {
            if (found_ite) {
                if (m_conservative)
                    return false;
            }
            else {
                found_ite = true;
            }
        }
    }
    CTRACE("push_app_ite", found_ite, tout << "found target for push app ite:\n";
          tout << decl->get_name();
          for (unsigned i = 0; i < num_args; i++) tout << " " << mk_pp(args[i], m);
          tout << "\n";);
    return found_ite;
}

void push_app_ite::operator()(expr * s, expr_ref & r, proof_ref & p) {
    expr  * result;
    proof * result_proof;
    reduce_core(s);
    get_cached(s, result, result_proof);
    r = result;
    switch (m.proof_mode()) {
    case PGM_DISABLED:
        p = m.mk_undef_proof();
        break;
    case PGM_COARSE:
        if (result == s)
            p = m.mk_reflexivity(s);
        else
            p = m.mk_rewrite_star(s, result, 0, 0);
        break;
    case PGM_FINE:
        if (result == s)
            p = m.mk_reflexivity(s);
        else
            p = result_proof;
        break;
    }
}

void push_app_ite::reduce_core(expr * n) {
    if (!is_cached(n)) {
        unsigned sz = m_todo.size();
        m_todo.push_back(n);
        while (m_todo.size() != sz) {
            expr * n = m_todo.back();
            if (is_cached(n))
                m_todo.pop_back();
            else if (visit_children(n)) {
                m_todo.pop_back();
                reduce1(n);
            }
        }
    }
}

bool push_app_ite::visit_children(expr * n) {
    bool visited = true;
    unsigned j;
    switch(n->get_kind()) {
    case AST_VAR:
        return true;
    case AST_APP:
        j = to_app(n)->get_num_args();
        while (j > 0) {
            --j;
            visit(to_app(n)->get_arg(j), visited);
        }
        return visited;
    case AST_QUANTIFIER: 
        visit(to_quantifier(n)->get_expr(), visited);
        return visited;
    default:
        UNREACHABLE();
        return true;
    }
}

void push_app_ite::reduce1(expr * n) {
    switch (n->get_kind()) {
    case AST_VAR:
        cache_result(n, n, 0);
        break;
    case AST_APP:
        reduce1_app(to_app(n));
        break;
    case AST_QUANTIFIER:
        reduce1_quantifier(to_quantifier(n));
        break;
    default:
        UNREACHABLE();
    }
}

void push_app_ite::reduce1_app(app * n) {
    m_args.reset();
    
    func_decl * decl = n->get_decl();
    proof_ref p1(m);
    get_args(n, m_args, p1);

    expr_ref r(m);
    if (is_target(decl, m_args.size(), m_args.c_ptr()))
        apply(decl, m_args.size(), m_args.c_ptr(), r);
    else
        mk_app(decl, m_args.size(), m_args.c_ptr(), r);
    
    if (!m.fine_grain_proofs())
        cache_result(n, r, 0);
    else {
        expr * s = m.mk_app(decl, m_args.size(), m_args.c_ptr());
        proof * p;
        if (n == r)
            p = 0;
        else if (r != s) 
            p = m.mk_transitivity(p1, m.mk_rewrite(s, r));
        else
            p = p1;
        cache_result(n, r, p);
    }
}

void push_app_ite::reduce1_quantifier(quantifier * q) {
    expr *  new_body;
    proof * new_body_pr;
    get_cached(q->get_expr(), new_body, new_body_pr);
    
    quantifier * new_q = m.update_quantifier(q, new_body);
    proof *      p     = q == new_q ? 0 : m.mk_quant_intro(q, new_q, new_body_pr);   
    cache_result(q, new_q, p);
}

bool ng_push_app_ite::is_target(func_decl * decl, unsigned num_args, expr * const * args) {
    bool r = push_app_ite::is_target(decl, num_args, args);
    if (!r) 
        return false;
    for (unsigned i = 0; i < num_args; i++)
        if (!is_ground(args[i]))
            return true;
    return false;
}

ng_push_app_ite::ng_push_app_ite(simplifier & s, bool conservative):
    push_app_ite(s, conservative) {
}

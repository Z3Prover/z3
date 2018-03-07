/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    expr_functors.cpp

Abstract:

    Functors on expressions.

Author:

    Nikolaj Bjorner (nbjorner) 2010-02-19

Revision History:

    Hoisted from quant_elim.

--*/

#include "ast/expr_functors.h"

// ----------
// check_pred

bool check_pred::operator()(expr* e) {
    if (!m_visited.is_marked(e)) {
        m_refs.push_back(e);
        visit(e);
    }
    SASSERT(m_visited.is_marked(e));
    return m_pred_holds.is_marked(e);
}        

void check_pred::visit(expr* e) {
    ptr_vector<expr> todo;
    todo.push_back(e);
    while (!todo.empty()) {
        e = todo.back();
        if (m_pred(e)) {
            m_pred_holds.mark(e, true);                
        }
        if (m_visited.is_marked(e)) {
            todo.pop_back();
            continue;
        }
        switch(e->get_kind()) {
        case AST_APP: {
            app* a = to_app(e);
            bool all_visited = true;
            unsigned num_args = a->get_num_args();
            for (unsigned i = 0; i < num_args; ++i) {
                expr* arg = a->get_arg(i);
                if (!m_visited.is_marked(arg)) {
                    todo.push_back(arg);
                    all_visited = false;
                }
                else if (m_pred_holds.is_marked(arg)) {
                    m_pred_holds.mark(e, true);
                }
            }
            if (all_visited) {
                m_visited.mark(e, true);
                todo.pop_back();
            }
            break;
        }
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(e);
            expr* arg = q->get_expr();
            if (m_visited.is_marked(arg)) {
                todo.pop_back();
                if (m_pred_holds.is_marked(arg)) {
                    m_pred_holds.mark(e, true);
                }
                m_visited.mark(e, true);
            }
            else {
                todo.push_back(arg);
            }
            break;
        }
        case AST_VAR: 
            todo.pop_back();
            m_visited.mark(e, true);
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
}

// ------------
// contains_app


bool contains_app::operator()(unsigned size, expr* const* es) {
    for (unsigned i = 0; i < size; ++i) {
        if ((*this)(es[i])) {
            return true;
        }
    }
    return false;
}

// -----------
// map_proc

void map_proc::reconstruct(app* a) {
    m_args.reset();
    bool is_new = false;
    for (unsigned i = 0; i < a->get_num_args(); ++i) {
        expr* e1 = a->get_arg(i);
        expr* e2 = get_expr(e1);
        m_args.push_back(e2);
        if (e1 != e2) {
            is_new = true;
        }
    }
    if (is_new) {
        expr* b = m.mk_app(a->get_decl(), m_args.size(), m_args.c_ptr());
        m_map.insert(a, b, nullptr);
    }
    else {
        m_map.insert(a, a, nullptr);
    }    
}

void map_proc::visit(quantifier* e) {
    expr_ref q(m);
    q = m.update_quantifier(e, get_expr(e->get_expr()));
    m_map.insert(e, q, nullptr);
}

expr* map_proc::get_expr(expr* e) {
    expr* result = nullptr;
    proof* p = nullptr;
    m_map.get(e, result, p);
    return result;
}

/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    for_each_expr.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-12-28.

Revision History:

--*/
#ifndef FOR_EACH_EXPR_H_
#define FOR_EACH_EXPR_H_

#include "ast/ast.h"
#include "util/trace.h"

template<typename ForEachProc, typename ExprMark, bool MarkAll, bool IgnorePatterns>
void for_each_expr_core(ForEachProc & proc, ExprMark & visited, expr * n) {
    typedef std::pair<expr *, unsigned> frame;

    if (MarkAll || n->get_ref_count() > 1) {
        if (visited.is_marked(n))
            return;
        visited.mark(n);
    }

    sbuffer<frame> stack;    
    
    stack.push_back(frame(n, 0));
    while (!stack.empty()) {
    start:
        frame & fr  = stack.back();
        expr * curr = fr.first;
        switch (curr->get_kind()) {
        case AST_VAR:
            proc(to_var(curr));
            stack.pop_back();
            break;
        case AST_APP: {
            unsigned num_args = to_app(curr)->get_num_args();
            while (fr.second < num_args) {
                expr * arg = to_app(curr)->get_arg(fr.second);
                fr.second++;
                if (MarkAll || arg->get_ref_count() > 1) {
                    if (visited.is_marked(arg))
                        continue;
                    visited.mark(arg);
                }
                switch (arg->get_kind()) {
                case AST_VAR:
                    proc(to_var(arg));
                    break;
                case AST_QUANTIFIER:
                    stack.push_back(frame(arg, 0));
                    goto start;
                case AST_APP:
                    if (to_app(arg)->get_num_args() == 0) {
                        proc(to_app(arg));
                    }
                    else {
                        stack.push_back(frame(arg, 0));
                        goto start;
                    }
                    break;
                default:
                    UNREACHABLE();
                    break;
                }
            }
            stack.pop_back();
            proc(to_app(curr));
            break;
        }
        case AST_QUANTIFIER: {
            quantifier * q        = to_quantifier(curr);
            unsigned num_children = IgnorePatterns ? 1 : q->get_num_children();
            while (fr.second < num_children) {
                expr * child = q->get_child(fr.second);
                fr.second++;
                if (MarkAll || child->get_ref_count() > 1) {
                    if (visited.is_marked(child))
                        continue;
                    visited.mark(child);
                }
                stack.push_back(frame(child, 0));
                goto start;
            }
            stack.pop_back();
            proc(to_quantifier(curr));
            break;
        }
        default:
            UNREACHABLE();
            break;
        }
    }
}

template<typename T>
bool for_each_expr_args(ptr_vector<expr> & stack, expr_mark & visited, unsigned num_args, T * const * args) {
    bool result = true;
    for (unsigned i = 0; i < num_args; i++) {
        T * arg = args[i];
        if (!visited.is_marked(arg)) {
            stack.push_back(arg);
            result = false;
        }
    }
    return result;
}

template<typename ForEachProc>
void for_each_expr(ForEachProc & proc, expr_mark & visited, expr * n) {
    for_each_expr_core<ForEachProc, expr_mark, true, false>(proc, visited, n);
}

template<typename ForEachProc>
void for_each_expr(ForEachProc & proc, expr * n) {
    expr_mark visited;
    for_each_expr_core<ForEachProc, expr_mark, false, false>(proc, visited, n);
}

template<typename ForEachProc>
void for_each_expr(ForEachProc & proc, unsigned n, expr * const* es) {
    expr_mark visited;
    for (unsigned i = 0; i < n; ++i) 
        for_each_expr_core<ForEachProc, expr_mark, false, false>(proc, visited, es[i]);
}

template<typename ForEachProc>
void for_each_expr(ForEachProc & proc, expr_ref_vector const& es) {
    expr_mark visited;
    for (expr* e : es) 
        for_each_expr_core<ForEachProc, expr_mark, false, false>(proc, visited, e);
}

template<typename ForEachProc>
void quick_for_each_expr(ForEachProc & proc, expr_fast_mark1 & visited, expr * n) {
    for_each_expr_core<ForEachProc, expr_fast_mark1, false, false>(proc, visited, n);
}

template<typename ForEachProc>
void quick_for_each_expr(ForEachProc & proc, expr * n) {
    expr_fast_mark1 visited;
    for_each_expr_core<ForEachProc, expr_fast_mark1, false, false>(proc, visited, n);
}

template<typename EscapeProc>
struct for_each_expr_proc : public EscapeProc {
    void operator()(expr * n)        { EscapeProc::operator()(n); }
    void operator()(var * n)        { operator()(static_cast<expr *>(n)); }
    void operator()(app * n)        { operator()(static_cast<expr *>(n)); }
    void operator()(quantifier * n) { operator()(static_cast<expr *>(n)); }
};                     

unsigned get_num_exprs(expr * n);
unsigned get_num_exprs(expr * n, expr_mark & visited);
unsigned get_num_exprs(expr * n, expr_fast_mark1 & visited);

bool has_skolem_functions(expr * n);

// pre-order traversal of subterms
class subterms {
    expr_ref_vector m_es;
public:
    class iterator {
        expr_ref_vector m_es;
        expr_mark       m_visited;        
    public:
        iterator(subterms& f, bool start);
        expr* operator*();
        iterator operator++(int);
        iterator& operator++();
        bool operator==(iterator const& other) const;
        bool operator!=(iterator const& other) const;
    };
    subterms(expr_ref_vector const& es);
    subterms(expr_ref& e);
    iterator begin();
    iterator end();
};

class subterms_postorder {
    expr_ref_vector m_es;
public:
    class iterator {
        expr_ref_vector m_es;
        expr_mark       m_visited, m_seen; 
        void next();
    public:
        iterator(subterms_postorder& f, bool start);
        expr* operator*();
        iterator operator++(int);
        iterator& operator++();
        bool operator==(iterator const& other) const;
        bool operator!=(iterator const& other) const;
    };
    subterms_postorder(expr_ref_vector const& es);
    subterms_postorder(expr_ref& e);
    iterator begin();
    iterator end();
};

#endif /* FOR_EACH_EXPR_H_ */


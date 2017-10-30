/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    has_free_vars.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-23.

Revision History:

--*/
#include "ast/ast.h"
#include "ast/expr_delta_pair.h"
#include "util/hashtable.h"

class contains_vars {
    typedef hashtable<expr_delta_pair, obj_hash<expr_delta_pair>, default_eq<expr_delta_pair> > cache;
    cache                    m_cache;
    svector<expr_delta_pair> m_todo;
    bool                     m_contains;
    unsigned                 m_window;

    void visit(expr * n, unsigned delta, bool & visited) {
        expr_delta_pair e(n, delta);
        if (!m_cache.contains(e)) {
            m_todo.push_back(e);
            visited = false;
        }
    }

    bool visit_children(expr * n, unsigned delta) {
        bool visited = true;
        unsigned dw;
        unsigned j;
        switch (n->get_kind()) {
        case AST_VAR:
            dw = m_window <= UINT_MAX - delta ? m_window + delta : UINT_MAX;
            if (to_var(n)->get_idx() >= delta && to_var(n)->get_idx() <= dw) 
                m_contains = true;
            break;
        case AST_APP:
            j = to_app(n)->get_num_args();
            while (j > 0) {
                --j;
                visit(to_app(n)->get_arg(j), delta, visited);
            }
            break;
        case AST_QUANTIFIER:
            if (delta <= UINT_MAX - to_quantifier(n)->get_num_decls()) {
                visit(to_quantifier(n)->get_expr(), delta + to_quantifier(n)->get_num_decls(), visited);
            }
        break;
        default:
            break;
        }
        return visited;
    }

public:
    // return true if n contains a variable in the range [begin, end]
    bool operator()(expr * n, unsigned begin = 0, unsigned end = UINT_MAX) {
        m_contains   = false;
        m_window     = end - begin;
        m_todo.reset();
        m_cache.reset();
        m_todo.push_back(expr_delta_pair(n, begin));
        while (!m_todo.empty()) {
            expr_delta_pair e = m_todo.back();
            if (visit_children(e.m_node, e.m_delta)) {
                m_cache.insert(e);
                m_todo.pop_back();
            }
            if (m_contains) {
                return true;
            }
        }
        SASSERT(!m_contains);
        return false;
    }
};

bool has_free_vars(expr * n) {
    contains_vars p;
    return p(n);
}



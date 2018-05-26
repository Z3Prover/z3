/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    recurse_expr.h

Abstract:

    Traverse an expression applying a visitor.

Author:

    Leonardo de Moura (leonardo) 2008-01-11.

Revision History:

--*/
#ifndef RECURSE_EXPR_H_
#define RECURSE_EXPR_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"

template<typename T, typename Visitor, bool IgnorePatterns=false>
class recurse_expr : public Visitor {
    obj_map<expr, T>         m_cache;
    ptr_vector<expr>         m_todo;
    vector<T>                m_results1;
    vector<T>                m_results2;

    bool is_cached(expr * n) const { T c; return m_cache.find(n, c); }
    T get_cached(expr * n) const { return m_cache.find(n); }
    void cache_result(expr * n, T c) { m_cache.insert(n, c); }
    
    void visit(expr * n, bool & visited);
    bool visit_children(expr * n);
    void process(expr * n);
    
public:
    recurse_expr(Visitor const & v = Visitor()):Visitor(v) {}
    T operator()(expr * n);
    void reset() { m_cache.reset(); m_todo.clear(); }
    void finalize() { m_cache.finalize(); m_todo.finalize(); }
};

#endif /* RECURSE_EXPR_H_ */

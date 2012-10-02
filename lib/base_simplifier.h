/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    base_simplifier.h

Abstract:

    Base class for expression simplifier functors.

Author:

    Leonardo (leonardo) 2008-01-11

Notes:

--*/
#ifndef _BASE_SIMPLIFIER_H_
#define _BASE_SIMPLIFIER_H_

#include"expr_map.h"

/**
   \brief Implements basic functionality used by expression simplifiers.
*/
class base_simplifier {
protected:
    ast_manager &                  m_manager;
    expr_map                       m_cache;
    ptr_vector<expr>               m_todo;

    void cache_result(expr * n, expr * r, proof * p) { m_cache.insert(n, r, p); }
    void reset_cache() { m_cache.reset(); }
    void flush_cache() { m_cache.flush(); }
    void get_cached(expr * n, expr * & r, proof * & p) const { m_cache.get(n, r, p); }

    void visit(expr * n, bool & visited) {
        if (!is_cached(n)) {
            m_todo.push_back(n);
            visited = false;
        }
    }

public:
    base_simplifier(ast_manager & m):
        m_manager(m),
        m_cache(m, m.fine_grain_proofs()) {
    }
    bool is_cached(expr * n) const {  return m_cache.contains(n); }
    ast_manager & get_manager() { return m_manager; }
};

#endif /* _BASE_SIMPLIFIER_H_ */

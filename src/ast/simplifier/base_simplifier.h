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
#ifndef BASE_SIMPLIFIER_H_
#define BASE_SIMPLIFIER_H_

#include"expr_map.h"
#include"ast_pp.h"

/**
   \brief Implements basic functionality used by expression simplifiers.
*/
class base_simplifier {
protected:
    ast_manager &                  m;
    expr_map                       m_cache;
    ptr_vector<expr>               m_todo;

    void cache_result(expr * n, expr * r, proof * p) { 
        m_cache.insert(n, r, p); 
        CTRACE("simplifier", !is_rewrite_proof(n, r, p),
               tout << mk_pp(n, m) << "\n";
               tout << mk_pp(r, m) << "\n";
               tout << mk_pp(p, m) << "\n";);
        SASSERT(is_rewrite_proof(n, r, p));
    }
    void reset_cache() { m_cache.reset(); }
    void flush_cache() { m_cache.flush(); }
    void get_cached(expr * n, expr * & r, proof * & p) const { m_cache.get(n, r, p); }

    void reinitialize() { m_cache.set_store_proofs(m.fine_grain_proofs()); }


    void visit(expr * n, bool & visited) {
        if (!is_cached(n)) {
            m_todo.push_back(n);
            visited = false;
        }
    }

public:
    base_simplifier(ast_manager & m):
        m(m),
        m_cache(m, m.fine_grain_proofs()) {
    }
    bool is_cached(expr * n) const {  return m_cache.contains(n); }
    ast_manager & get_manager() { return m; }

    bool is_rewrite_proof(expr* n, expr* r, proof* p) {
        if (p && 
            !m.is_undef_proof(p) && 
            !(m.has_fact(p) && 
              (m.is_eq(m.get_fact(p)) || m.is_oeq(m.get_fact(p)) || m.is_iff(m.get_fact(p))) && 
              to_app(m.get_fact(p))->get_arg(0) == n && 
              to_app(m.get_fact(p))->get_arg(1) == r)) return false;
        
        return (!m.fine_grain_proofs() || p || (n == r));
    }
};

#endif /* BASE_SIMPLIFIER_H_ */

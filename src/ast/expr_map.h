/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    expr_map.h

Abstract:

    Mapping from expressions to expressions + proofs. This mapping
    is used to cache simplification results. 
    For every entry [e1->(e2, p)] we have that p is a proof that (= e1 e2).

Author:

    Leonardo (leonardo) 2008-01-03

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"

/**
   \brief Map from expressions to expressions+proofs.

   When proof production is disabled, no extra space is used.
*/
class expr_map {
    ast_manager &         m_manager;
    bool                  m_store_proofs;
    obj_map<expr, expr*>  m_expr2expr;
    obj_map<expr, proof*> m_expr2pr;
public:
    typedef obj_map<expr, expr*> Map;
    typedef Map::iterator iterator;
    typedef Map::key key;
    typedef Map::value value;
    typedef Map::data data;
    typedef Map::entry entry;

    expr_map(ast_manager & m);
    expr_map(ast_manager & m, bool store_proofs);
    ~expr_map();
    void insert(expr * k, expr * d, proof * p);
    bool contains(expr * k) const { return m_expr2expr.contains(k); }
    void get(expr * k, expr * & d, proof * & p) const;
    void erase(expr * k);
    void reset();
    void flush();
    iterator begin () const { return m_expr2expr.begin (); }
    iterator end () const {return m_expr2expr.end (); }
    void set_store_proofs(bool f) { 
        if (m_store_proofs != f) flush();
        m_store_proofs = f; 
    }
};


/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    matcher.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-02.

Revision History:

--*/
#pragma once

#include "ast/substitution/substitution.h"
#include "util/hashtable.h"

/**
   \brief Functor for matching expressions.
*/
class matcher {
    typedef std::pair<expr *, expr *> expr_pair;
    typedef pair_hash<obj_ptr_hash<expr>, obj_ptr_hash<expr> > expr_pair_hash;
    typedef hashtable<expr_pair, expr_pair_hash, default_eq<expr_pair> > cache;

    substitution *        m_subst;
    // cache                 m_cache;
    svector<expr_pair>    m_todo;

    void reset();

public:
    /**
       \brief Return true if e2 is an instance of e1.
       In case of success (result is true), it will store the substitution that makes e1 equals to e2 into s.
       
       For example:
       1) e1 = f(g(x), x), e2 = f(g(h(a)), h(a))
       The result is true, and s will contain x -> h(a)

       2) e1 = f(a, x)     e2 = f(x, a)
       The result is false.

       3) e1 = f(x, x)     e2 = f(y, a)
       The result is false

       4) e1 = f(x, y)     e2 = f(h(z), a)
       The result is true, and s contains x->h(z) and y->a
    */
    bool operator()(expr * e1, expr * e2, substitution & s);
};



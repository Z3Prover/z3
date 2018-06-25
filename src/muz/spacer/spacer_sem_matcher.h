/*++
Copyright (c) 2006 Microsoft Corporation and Arie Gurfinkel

Module Name:

    sem_matcher.h

Abstract:

   Semantic matcher

Author:

    Leonardo de Moura (leonardo) 2008-02-02.
    Arie Gurfinkel

Revision History:

--*/
#ifndef SPACER_SEM_MATCHER_H_
#define SPACER_SEM_MATCHER_H_

#include "ast/substitution/substitution.h"
#include "ast/arith_decl_plugin.h"
#include "util/hashtable.h"

namespace spacer {
/**
   \brief Functor for matching expressions.
*/
class sem_matcher {
    typedef std::pair<expr *, expr *> expr_pair;
    typedef pair_hash<obj_ptr_hash<expr>, obj_ptr_hash<expr> > expr_pair_hash;
    typedef hashtable<expr_pair, expr_pair_hash, default_eq<expr_pair> > cache;

    ast_manager &m;
    arith_util m_arith;
    expr_ref_vector m_pinned;
    substitution *        m_subst;
    svector<expr_pair>    m_todo;

    void reset();

    bool match_var(var *v, expr *e);
public:
    sem_matcher(ast_manager &man);

    /**
       \brief Return true if e2 is an instance of e1.
       In case of success (result is true), it will store the substitution that makes e1 equals to e2 into s.
       Sets pos to true if the match is positive and to false if it is negative (i.e., e1 equals !e2)

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
    bool operator()(expr * e1, expr * e2, substitution & s, bool &pos);
};
}
#endif /* SPACER_SEM_MATCHER_H_ */

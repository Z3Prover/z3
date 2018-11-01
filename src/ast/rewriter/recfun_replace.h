/*++
Copyright (c) 2018 Microsoft Corporation

Module Name:

    recfun_replace.h

Abstract:

    replace function for recfun.
    recfun_decl_plugin relies on being able to do expression replacement.
    It uses expr_safe_replace from ast/rewriter, which depends on ast.
    To break the dependency cycle we hoist the relevant functionality into 
    an argument to functionality exposed by recfun::set_definition

Author:

    Nikolaj Bjorner (nbjorner) 2018-11-01

Revision History:


--*/

#ifndef RECFUN_REPLACE_H_
#define RECFUN_REPLACE_H_

#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/expr_safe_replace.h"

class recfun_replace : public recfun::replace {
    ast_manager& m;
    expr_safe_replace m_replace;
public:
    recfun_replace(ast_manager& m): m(m), m_replace(m) {}
    void reset() override { m_replace.reset(); }
    void insert(expr* s, expr* t) override { m_replace.insert(s, t); }
    expr_ref operator()(expr* e) override { expr_ref r(m); m_replace(e, r); return r; }
};

#endif /* RECFUN_REPLACE_H_ */

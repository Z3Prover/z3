/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_ll_pp.h

Abstract:

    AST low level pretty printer.

Author:

    Leonardo de Moura (leonardo) 2006-10-19.

Revision History:

--*/
#ifndef AST_LL_PP_H_
#define AST_LL_PP_H_

#include "ast/ast.h"
#include<iostream>

void ast_ll_pp(std::ostream & out, ast_manager & m, ast * n, bool only_exprs=true, bool compact=true);
void ast_ll_pp(std::ostream & out, ast_manager & m, ast * n, ast_mark & visited, bool only_exprs=true, bool compact=true);
void ast_def_ll_pp(std::ostream & out, ast_manager & m, ast * n, ast_mark & visited, bool only_exprs=true, bool compact=true);
void ast_ll_bounded_pp(std::ostream & out, ast_manager & m, ast * n, unsigned depth);

struct mk_ll_pp {
    ast *         m_ast;
    ast_manager & m_manager;
    bool          m_only_exprs;
    bool          m_compact;
    mk_ll_pp(ast * a, ast_manager & m, bool only_exprs=true, bool compact=true): m_ast(a), m_manager(m), m_only_exprs(only_exprs), m_compact(compact) {}
};

inline std::ostream & operator<<(std::ostream & out, mk_ll_pp const & p) {
    ast_ll_pp(out, p.m_manager, p.m_ast, p.m_only_exprs, p.m_compact);
    return out;
}

struct mk_bounded_pp {
    ast *         m_ast;
    ast_manager & m_manager;
    unsigned      m_depth;
    mk_bounded_pp(ast * a, ast_manager & m, unsigned depth=3): m_ast(a), m_manager(m), m_depth(depth) {}
};

inline std::ostream & operator<<(std::ostream & out, mk_bounded_pp const & p) {
    ast_ll_bounded_pp(out, p.m_manager, p.m_ast, p.m_depth);
    return out;
}


#endif /* AST_LL_PP_H_ */


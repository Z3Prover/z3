/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ast_lt.h

Abstract:

    Total order on ASTs that does not depend on the internal ids.

Author:

    Leonardo de Moura (leonardo) 2011-04-08

Revision History:

--*/
#ifndef _AST_LT_H_
#define _AST_LT_H_

class ast;

bool lt(ast * n1, ast * n2);
bool is_sorted(unsigned num, expr * const * ns);

struct ast_to_lt {
    bool operator()(ast * n1, ast * n2) const { return lt(n1, n2); }
};

bool lex_lt(unsigned num, ast * const * n1, ast * const * n2);
inline bool lex_lt(unsigned num, expr * const * n1, expr * const * n2) {
    return lex_lt(num, reinterpret_cast<ast*const*>(n1), reinterpret_cast<ast*const*>(n2));
}

#endif

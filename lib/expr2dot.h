/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr2dot.h

Abstract:

    Convert expressions into a .DOT file

Author:

    Leonardo de Moura (leonardo) 2008-03-07.

Revision History:

--*/
#ifndef _EXPR2DOT_H_
#define _EXPR2DOT_H_

#include"ast.h"

void expr2dot(std::ostream & out, expr * a, ast_manager & m, bool proofs = false);

#endif /* _AST2DOT_H_ */


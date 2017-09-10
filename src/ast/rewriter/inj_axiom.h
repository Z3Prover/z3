/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    inj_axiom.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-23.

Revision History:

--*/
#ifndef INJ_AXIOM_H_
#define INJ_AXIOM_H_

#include "ast/ast.h"

bool simplify_inj_axiom(ast_manager & m, quantifier * q, expr_ref & result);

#endif /* INJ_AXIOM_H_ */


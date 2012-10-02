/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    uses_theory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-21.

Revision History:

--*/
#ifndef _USES_THEORY_H_
#define _USES_THEORY_H_

#include"ast.h"

/**
   \brief Return true if the given expression contains a symbol of the given theory.
*/
bool uses_theory(expr * n, family_id fid);

/**
    \brief Return true if the given expression contains a symbol of the given theory.
    Only the expressions not marked as visited are checked. The set visited is updated 
    with the new checked expressions.
*/
bool uses_theory(expr * n, family_id fid, expr_mark & visited);

#endif /* _USES_THEORY_H_ */


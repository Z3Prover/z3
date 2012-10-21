/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    has_free_vars.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-23.

Revision History:

--*/
#ifndef _HAS_FREE_VARS_H_
#define _HAS_FREE_VARS_H_

class expr;

bool has_free_vars(expr * n);

#endif /* _HAS_FREE_VARS_H_ */


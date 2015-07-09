/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pp.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/
#ifndef PP_H_
#define PP_H_

#include"format.h"
#include"params.h"

void pp(std::ostream & out, format_ns::format * f, ast_manager & m, params_ref const & p = params_ref());

#endif /* PP_H_ */


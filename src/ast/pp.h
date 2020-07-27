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
#pragma once

#include "ast/format.h"
#include "util/params.h"

void pp(std::ostream & out, format_ns::format * f, ast_manager & m, params_ref const & p = params_ref());



/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt2parser.h

Abstract:

    SMT 2.0 parser

Author:

    Leonardo de Moura (leonardo) 2011-03-01

Revision History:

--*/
#pragma once

#include "cmd_context/cmd_context.h"

bool parse_smt2_commands(cmd_context & ctx, std::istream & is, bool interactive = false, params_ref const & p = params_ref(), char const * filename = nullptr);

sexpr_ref parse_sexpr(cmd_context& ctx, std::istream& is, params_ref const& ps, char const* filename);


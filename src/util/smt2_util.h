/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    smt2_util.h

Abstract:

    Goodies for SMT2 standard

Author:

    Leonardo (leonardo) 2012-10-20

Notes:

--*/
#pragma once

#include "util/symbol.h"

bool is_smt2_simple_symbol_char(char c);
bool is_smt2_quoted_symbol(char const * s);
bool is_smt2_quoted_symbol(symbol const & s);
std::string mk_smt2_quoted_symbol(symbol const & s);


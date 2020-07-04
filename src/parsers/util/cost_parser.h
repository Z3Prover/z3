/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cost_parser.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-14.

Revision History:

--*/
#pragma once

#include "parsers/util/simple_parser.h"
#include "ast/arith_decl_plugin.h"

class cost_parser : public simple_parser {
    arith_util     m_util;
    var_ref_vector m_vars;
public:
    cost_parser(ast_manager & m);
    ~cost_parser() override {}
    expr * parse_int(rational const & r) override;
    expr * parse_float(rational const & r) override;
    unsigned add_var(symbol name);
    unsigned add_var(char const * name) { return add_var(symbol(name)); }
    void reset_vars();
};



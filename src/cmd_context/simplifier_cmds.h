/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    simplifier_cmds.h

Abstract:
    Support for simplifier commands in SMT 2.0 front-end

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-30

--*/
#pragma once

#include "ast/ast.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "util/params.h"
#include "util/cmd_context_types.h"
#include "util/ref.h"


class simplifier_cmd {
    symbol             m_name;
    char const *       m_descr;
    simplifier_factory m_factory;
public:
    simplifier_cmd(symbol const & n, char const * d, simplifier_factory f):
        m_name(n), m_descr(d), m_factory(f) {}

    symbol get_name() const { return m_name; }
    
    char const * get_descr() const { return m_descr; }
    
    simplifier_factory factory() { return m_factory; }
};

simplifier_factory sexpr2simplifier(cmd_context & ctx, sexpr * n);

void install_core_simplifier_cmds(cmd_context & ctx);

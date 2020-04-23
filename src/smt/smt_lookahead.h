/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_lookahead.h

Abstract:

    Lookahead solver for SMT

Author:

    nbjorner 2019-05-27.

Revision History:

--*/

#pragma once

#include "ast/ast.h"

namespace smt {
    class context;

    class lookahead {
        context&     ctx;
        ast_manager& m;

        struct compare;

        double get_score();

    public:
        lookahead(context& ctx);

        expr_ref choose();
    };
}

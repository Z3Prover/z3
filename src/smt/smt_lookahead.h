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

        void choose_rec(expr_ref_vector& trail, expr_ref_vector& result, unsigned depth, unsigned budget);

    public:
        lookahead(context& ctx);

        expr_ref choose(unsigned budget = 2000);

        expr_ref_vector choose_rec(unsigned depth);

    };
}

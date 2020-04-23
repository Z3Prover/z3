/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    smt_parallel.h

Abstract:

    Parallel SMT, portfolio loop specialized to SMT core.

Author:

    nbjorner 2020-01-31

Revision History:

--*/
#pragma once

#include "smt/smt_context.h"

namespace smt {

    class parallel {
        context& ctx;
    public:
        parallel(context& ctx): ctx(ctx) {}

        lbool operator()(expr_ref_vector const& asms);

    };

}

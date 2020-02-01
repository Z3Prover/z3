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
        expr_ref_vector     m_unit_trail;
        obj_hashtable<expr> m_unit_set;
        unsigned_vector     m_unit_lim;
        std::mutex          m_mux;
    public:
        parallel(context& ctx): ctx(ctx), m_unit_trail(ctx.m) {}

        lbool operator()(expr_ref_vector const& asms);

        void add_unit(context& ctx, expr* e);

        void get_units(unsigned idx, context& pctx);
    };

}
